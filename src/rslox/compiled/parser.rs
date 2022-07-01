use std::mem;

use either::Either::{Left, Right};
use nonempty::NonEmpty;
use num_traits::FromPrimitive;

use crate::rslox::common::error::{convert_errors, LoxResult, ParserError};
use crate::rslox::common::lexer::{Token, TokenType};
use crate::rslox::compiled::chunk::{Chunk, Line, OpCode};

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
        let line = self.parse_expression().map_err(NonEmpty::new)?;
        self.chunk.write(OpCode::Return, line);
        Ok(self.chunk)
    }

    fn parse_expression(&mut self) -> Result<Line, ParserError> {
        self.parse_precedence(Precedence::Assignment)
    }
    fn parse_precedence(&mut self, precedence: Precedence) -> Result<Line, ParserError> {
        let Token {line, r#type} = self.advance();
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
            e => todo!("{:?}", e),
        }
        let mut last_line = line;
        while !self.is_at_end() && precedence <= Precedence::from(self.peek_type()) {
            let Token {line, r#type} = self.advance();
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
            ))
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
    use std::rc::Rc;

    use crate::rslox::common::tests::unsafe_tokenize;
    use crate::rslox::compiled::tests::unsafe_parse;

    use super::*;

    #[test]
    fn constant() {
        let mut expected = Chunk::new();
        expected.write_constant(123.0, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_parse(vec!["123"]),
            expected,
        )
    }

    #[test]
    fn grouped_constant() {
        let mut expected = Chunk::new();
        expected.write_constant(123.0, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            parse(unsafe_tokenize(vec!["(123)"])).unwrap(),
            expected,
        )
    }

    #[test]
    fn unary_minus() {
        let mut expected = Chunk::new();
        expected.write_constant(123.0, 1);
        expected.write(OpCode::Negate, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_parse(vec!["-123"]),
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
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_parse(vec!["-1+2"]),
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
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_parse(vec!["-1-2"]),
            expected,
        )
    }

    #[test]
    fn string_interning() {
        let interned_strings = unsafe_parse(vec![r#""str" == "str""#]).interned_strings;
        let mut expected = HashSet::new();
        expected.insert(Rc::new("str".to_owned()));
        assert_eq!(
            interned_strings,
            expected,
        )
    }
}