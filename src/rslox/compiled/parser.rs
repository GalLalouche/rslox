use std::borrow::Borrow;

use nonempty::NonEmpty;
use num_traits::FromPrimitive;

use crate::rslox::common::error::{convert_errors, LoxResult, ParserError};
use crate::rslox::common::lexer::{Token, TokenType};
use crate::rslox::compiled::chunk::{Chunk, OpCode};

pub fn parse(lexems: &Vec<Token>) -> LoxResult<Chunk> {
    convert_errors(Parser::new(lexems).parse())
}

struct Parser<'a> {
    chunk: Chunk,
    tokens: &'a Vec<Token>,
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
            _ => Precedence::TopLevel,
        }
    }
}

impl<'a> Parser<'a> {
    pub fn new(lexems: &'a Vec<Token>) -> Self {
        Parser { chunk: Chunk::new(), tokens: lexems, current: 0 }
    }

    pub fn parse(mut self) -> Result<Chunk, NonEmpty<ParserError>> {
        self.parse_expression().map_err(NonEmpty::new)?;
        self.chunk.write(OpCode::Return, self.tokens.last().unwrap().line);
        Ok(self.chunk)
    }

    fn parse_expression(&mut self) -> Result<(), ParserError> {
        self.parse_precedence(Precedence::Assignment)
    }
    fn parse_precedence(&mut self, precedence: Precedence) -> Result<(), ParserError> {
        match &self.peek().r#type {
            TokenType::Minus => {
                let line = self.peek().line;
                self.advance();
                self.parse_precedence(Precedence::Unary)?;
                self.chunk.write(OpCode::Negate, line);
            }
            TokenType::Bang => {
                let line = self.peek().line;
                self.advance();
                self.parse_precedence(Precedence::Unary)?;
                self.chunk.write(OpCode::Not, line);
            }
            TokenType::NumberLiteral(num) => {
                self.chunk.write_constant(*num, self.peek().line);
                self.advance();
            }
            TokenType::True | TokenType::False | TokenType::Nil => {
                let op = match &self.peek().r#type {
                    TokenType::True => OpCode::Bool(true),
                    TokenType::False => OpCode::Bool(false),
                    TokenType::Nil => OpCode::Nil,
                    _ => panic!(),
                };
                self.chunk.write(op, self.peek().line);
                self.advance();
            }
            TokenType::OpenParen => {
                self.advance();
                self.parse_expression()?;
                self.consume(TokenType::CloseParen, None)?;
            }
            e => todo!("{:?}", e),
        }
        while !self.is_at_end() && precedence <= Precedence::from(self.peek().r#type.borrow()) {
            let op = match &self.peek().r#type {
                TokenType::Minus => OpCode::Subtract,
                TokenType::Plus => OpCode::Add,
                TokenType::Slash => OpCode::Divide,
                TokenType::Star => OpCode::Multiply,
                _ => panic!()
            };
            let line = self.peek().line;
            let next = Precedence::from(&self.peek().r#type).next().unwrap();
            self.advance();
            self.parse_precedence(next)?;
            self.chunk.write(op, line);
        }
        Ok(())
    }

    fn consume(&mut self, expected: TokenType, msg: Option<String>) -> Result<(), ParserError> {
        let expected_msg = msg.unwrap_or(expected.to_string());
        if self.is_at_end() {
            Err(ParserError::new(
                format!("Expected {}, but encountered end of file", expected_msg),
                self.tokens.last().expect("empty tokens").to_owned(),
            ))
        } else if self.peek().get_type() != &expected {
            let p = self.peek();
            Err(ParserError::new(
                format!(
                    "Expected {}, but encountered {} at line {}",
                    expected_msg,
                    p.get_type(),
                    p.line,
                ),
                p.to_owned(),
            ))
        } else {
            assert_ne!(expected, TokenType::Eof);
            self.advance();
            Ok(())
        }
    }

    fn advance(&mut self) -> &Token {
        assert!(!self.is_at_end());
        self.current += 1;
        self.previous()
    }

    fn is_at_end(&self) -> bool {
        self.current == self.tokens.len()
    }

    fn previous(&self) -> &Token {
        &self.tokens[self.current - 1]
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.current]
    }
}

#[cfg(test)]
mod tests {
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
            parse(&unsafe_tokenize(vec!["(123)"])).unwrap(),
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
}