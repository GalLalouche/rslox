use std::mem;

use either::Either::{Left, Right};
use nonempty::NonEmpty;
use num_traits::FromPrimitive;

use crate::rslox::common::error::{convert_errors, LoxResult, ParserError};
use crate::rslox::common::lexer::{Token, TokenType};
use crate::rslox::compiled::chunk::{Chunk, GcWeak, Line, OpCode};

pub fn parse(lexems: Vec<Token>) -> LoxResult<Chunk> {
    convert_errors(Parser::new(lexems).parse())
}

struct Parser {
    chunk: Chunk,
    tokens: Vec<Token>,
    current: usize,
}

#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd, FromPrimitive)]
enum Precedence {
    TopLevel,
    Assignment,
    Or,
    And,
    Equality /* == != */,
    Comparison /* < > <= >= */,
    Term /* + - */,
    Factor /* * / */,
    Unary /* ! - */,
    Call /* . () */,
    Primary,
}

impl Precedence {
    fn next(&self) -> Option<Self> {
        FromPrimitive::from_u8(*self as u8 + 1)
    }
}

impl From<&TokenType> for Precedence {
    fn from(tt: &TokenType) -> Self {
        match tt {
            TokenType::Minus => Precedence::Term,
            TokenType::Plus => Precedence::Term,
            TokenType::Slash => Precedence::Factor,
            TokenType::Star => Precedence::Factor,
            TokenType::EqualEqual => Precedence::Equality,
            TokenType::BangEqual => Precedence::Equality,
            TokenType::Less => Precedence::Comparison,
            TokenType::LessEqual => Precedence::Comparison,
            TokenType::Greater => Precedence::Comparison,
            TokenType::GreaterEqual => Precedence::Comparison,
            _ => Precedence::TopLevel,
        }
    }
}

impl Parser {
    pub fn new(lexems: Vec<Token>) -> Self {
        Parser { chunk: Chunk::new(), tokens: lexems, current: 0 }
    }

    pub fn parse(mut self) -> Result<Chunk, NonEmpty<ParserError>> {
        let mut line: Line = 0;
        let mut errors = Vec::new();
        while !self.is_at_end() {
            match self.declaration() {
                Ok(l) => line = l,
                Err(err) => {
                    errors.push(err);
                    self.synchronize();
                }
            }
        }
        match NonEmpty::from_vec(errors) {
            None => {
                self.chunk.write(OpCode::Return, line);
                Ok(self.chunk)
            }
            Some(errs) => Err(errs),
        }
    }

    fn synchronize(&mut self) {
        while !self.is_at_end() && !self.matches(TokenType::Semicolon).is_some() {
            match self.peek_type() {
                TokenType::Class | TokenType::Fun | TokenType::Var | TokenType::For | TokenType::If
                | TokenType::While | TokenType::Print | TokenType::Return => return,
                _ => {
                    self.advance();
                }
            }
        }
    }

    fn declaration(&mut self) -> Result<Line, ParserError> {
        self.statement()
    }

    fn statement(&mut self) -> Result<Line, ParserError> {
        let line = if let Some(line) = self.matches(TokenType::Print) {
            self.parse_expression()?;
            self.chunk.write(OpCode::Print, line);
            line
        } else if let Some(line) = self.matches(TokenType::Var) {
            let global: GcWeak<String> = self.parse_variable()?;
            if self.matches(TokenType::Equal).is_some() {
                self.parse_expression()
            } else {
                self.chunk.write(OpCode::Nil, line);
                Ok(line)
            }?;
            self.chunk.write(OpCode::DefineGlobal(global), line);
            line
        } else {
            let line = self.parse_expression()?;
            self.chunk.write(OpCode::Pop, line);
            line
        };
        self.consume(TokenType::Semicolon, None)?;
        Ok(line)
    }

    fn parse_variable(&mut self) -> Result<GcWeak<String>, ParserError> {
        let Token { r#type, line } = self.advance();
        match r#type {
            TokenType::Identifier(name) => Ok(self.chunk.define_global(name)),
            e => Err(ParserError {
                message: format!("Expected Identifier for variable, got '{:?}'", e),
                token: Token { r#type: e, line },
            })
        }
    }

fn parse_expression(&mut self) -> Result<Line, ParserError> {
    self.parse_precedence(Precedence::Assignment)
}

fn parse_precedence(&mut self, precedence: Precedence) -> Result<Line, ParserError> {
    let Token { line, r#type } = self.advance();
    match r#type {
        TokenType::Minus => {
            self.parse_precedence(Precedence::Unary)?;
            self.chunk.write(OpCode::Negate, line);
        }
        TokenType::Bang => {
            self.parse_precedence(Precedence::Unary)?;
            self.chunk.write(OpCode::Not, line);
        }
        TokenType::NumberLiteral(num) => {
            self.chunk.write_constant(num, line);
        }
        TokenType::Identifier(name) => {
            let global = self.chunk.define_global(name);
            self.chunk.write(OpCode::Identifier(global), line);
        }
        TokenType::StringLiteral(str) => {
            self.chunk.add_string(str, line);
        }
        TokenType::True | TokenType::False | TokenType::Nil => {
            let op = match &r#type {
                TokenType::True => OpCode::Bool(true),
                TokenType::False => OpCode::Bool(false),
                TokenType::Nil => OpCode::Nil,
                _ => panic!(),
            };
            self.chunk.write(op, line);
        }
        TokenType::OpenParen => {
            self.parse_expression()?;
            self.consume(TokenType::CloseParen, None)?;
        }
        e => return Err(
            ParserError::new(format!("Unexpected '{:?}'", e), Token { r#type: e, line })),
    }
    let mut last_line = line;
    while !self.is_at_end() && precedence <= Precedence::from(self.peek_type()) {
        let Token { line, r#type } = self.advance();
        let next_precedence = Precedence::from(&r#type).next().unwrap();
        let op = match r#type {
            TokenType::Minus => Left(OpCode::Subtract),
            TokenType::Plus => Left(OpCode::Add),
            TokenType::Slash => Left(OpCode::Divide),
            TokenType::Star => Left(OpCode::Multiply),
            TokenType::EqualEqual => Left(OpCode::Equals),
            TokenType::Less => Left(OpCode::Less),
            TokenType::Greater => Left(OpCode::Greater),
            TokenType::BangEqual => Right(OpCode::Equals),
            TokenType::LessEqual => Right(OpCode::Greater),
            TokenType::GreaterEqual => Right(OpCode::Less),
            _ => panic!()
        };
        self.parse_precedence(next_precedence)?;
        match op {
            Left(op) => self.chunk.write(op, line),
            Right(op) => {
                self.chunk.write(op, line);
                self.chunk.write(OpCode::Not, line);
            }
        }
        last_line = line;
    }
    Ok(last_line)
}

fn consume(&mut self, expected: TokenType, msg: Option<String>) -> Result<(), ParserError> {
    let expected_msg = msg.unwrap_or(expected.to_string());
    if self.is_at_end() {
        return Err(ParserError::new(
            format!("Expected {}, but encountered end of file", expected_msg),
            self.tokens.last().expect("empty tokens").to_owned(),
        ));
    }

    let token = self.advance();
    if token.r#type != expected {
        Err(ParserError::new(
            format!(
                "Expected {}, but encountered {} at line {}",
                expected_msg,
                token.r#type,
                token.line,
            ),
            token.to_owned(),
        ))
    } else {
        assert_ne!(expected, TokenType::Eof);
        Ok(())
    }
}

fn matches(&mut self, tt: TokenType) -> Option<Line> {
    if self.peek_type() == &tt {
        let result = self.tokens[self.current].line;
        self.advance();
        Some(result)
    } else {
        None
    }
}

fn advance(&mut self) -> Token {
    let result =
        mem::replace(self.tokens.get_mut(self.current).unwrap(), Token::new(0, TokenType::Eof));
    self.current += 1;
    result
}

fn is_at_end(&self) -> bool {
    self.current == self.tokens.len()
}

fn peek_type(&self) -> &TokenType {
    &self.tokens[self.current].r#type
}
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::ops::Deref;
    use std::rc::Rc;

    use crate::assert_deep_eq;
    use crate::rslox::common::tests::unsafe_tokenize;
    use crate::rslox::compiled::tests::unsafe_parse;

    use super::*;

    #[test]
    fn constant() {
        let mut expected = Chunk::new();
        expected.write_constant(123.0, 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_parse(vec!["123;"]),
            expected,
        )
    }

    #[test]
    fn grouped_constant() {
        let mut expected = Chunk::new();
        expected.write_constant(123.0, 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            parse(unsafe_tokenize(vec!["(123);"])).unwrap(),
            expected,
        )
    }

    #[test]
    fn unary_minus() {
        let mut expected = Chunk::new();
        expected.write_constant(123.0, 1);
        expected.write(OpCode::Negate, 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_parse(vec!["-123;"]),
            expected,
        )
    }

    #[test]
    fn basic_precedence() {
        let mut expected = Chunk::new();
        expected.write_constant(1.0, 1);
        expected.write(OpCode::Negate, 1);
        expected.write_constant(2.0, 1);
        expected.write(OpCode::Add, 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_parse(vec!["-1+2;"]),
            expected,
        )
    }

    #[test]
    fn mixed_unary_and_binary() {
        let mut expected = Chunk::new();
        expected.write_constant(1.0, 1);
        expected.write(OpCode::Negate, 1);
        expected.write_constant(2.0, 1);
        expected.write(OpCode::Subtract, 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_parse(vec!["-1-2;"]),
            expected,
        )
    }

    #[test]
    fn string_interning() {
        let interned_strings = unsafe_parse(vec![r#""str" == "str";"#]).interned_strings;
        let mut expected = HashSet::new();
        expected.insert(Rc::new("str".to_owned()));
        assert_eq!(
            interned_strings,
            expected,
        )
    }

    #[test]
    fn multiple_error_report() {
        let vec: Vec<_> = parse(
            unsafe_tokenize(
                vec![
                    "1 +;",
                    "3 * 3;",
                    r#"print -;"#,
                ])
        ).unwrap_err().into();
        assert_eq!(
            vec.iter().map(|e| e.deref().get_info().line).collect::<Vec<_>>(),
            vec![1, 3],
        )
    }

    #[test]
    fn define_nil_var() {
        let parsed = unsafe_parse(vec!["var foo;"]);
        let mut expected = Chunk::new();
        let w = expected.define_global("foo".to_owned());
        expected.write(OpCode::Nil, 1);
        expected.write(OpCode::DefineGlobal(w), 1);
        expected.write(OpCode::Return, 1);
        assert_deep_eq!(
            parsed,
            expected,
        )
    }
}