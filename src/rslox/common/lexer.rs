use std::fmt;
use std::fmt::{Display, Formatter};

use crate::rslox::common;
use crate::rslox::common::error::{ErrorInfo, LoxError, LoxResult};

pub fn tokenize(source: &str) -> LoxResult<Vec<Token>> {
    common::error::convert_error(Lexer::new(source).get_lexems())
}


// Only failure possible during lexing is unterminated string or multi-line comment. Therefore, at
// most one error can occur at any given time.
type LexResult<A> = Result<A, LexError>;

#[derive(Debug, PartialEq, Clone)]
pub enum TokenType {
    // Single-character tokens.
    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    Comma,
    Question,
    Colon,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,
    // One or two character tokens.
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    // Keywords.
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,

    StringLiteral(String),
    NumberLiteral(f64),
    Identifier(String),

    Eof,
}

impl TokenType {
    fn string_literal<S: Into<String>>(str: S) -> Self { TokenType::StringLiteral(str.into()) }
    fn number_literal(f: f64) -> Self { TokenType::NumberLiteral(f) }
    pub fn identifier<S: Into<String>>(str: S) -> Self { TokenType::Identifier(str.into()) }
}

impl Display for TokenType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{:?}", self))
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    pub line: usize,
    pub r#type: TokenType,
}

impl Token {
    pub fn new(line: usize, r#type: TokenType) -> Self {
        Token { line, r#type }
    }
    pub fn get_type(&self) -> &TokenType { &self.r#type }

    pub fn error_info(&self) -> ErrorInfo {
        ErrorInfo { line: self.line }
    }
}

#[derive(Debug)]
pub struct LexError {
    line: usize,
    r#where: String,
    message: String,
}

impl LoxError for LexError {
    fn get_info(&self) -> ErrorInfo {
        ErrorInfo { line: self.line }
    }

    fn get_message(&self) -> String {
        self.message.to_owned()
    }
}

impl LexError {
    fn error(line: usize, message: String) -> LexError {
        LexError::report(line, "".to_owned(), message)
    }
    fn report(line: usize, r#where: String, message: String) -> LexError {
        LexError { line, r#where, message }
    }
}

impl Display for LexError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[line {}] Error{}: {}", self.line, self.r#where, self.message)
    }
}

struct Lexer<'a> {
    source: &'a str,
    current: usize,
    start: usize,
    line: usize,
    lexems: Vec<Token>,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str) -> Self {
        Lexer {
            source,
            current: 0,
            start: 0,
            line: 1,
            lexems: Vec::new(),
        }
    }

    pub fn get_lexems(mut self) -> LexResult<Vec<Token>> {
        if !self.is_at_end() {
            while !self.is_at_end() {
                self.start = self.current;
                self.scan_token()?;
            }
        }
        Ok(self.lexems)
    }

    fn is_at_end(&self) -> bool { self.current >= self.source.len() }

    fn add_token_type(&mut self, tt: TokenType) {
        self.lexems.push(Token::new(self.line, tt));
    }
    fn matches(&mut self, expected: char) -> bool {
        let result = self.source.chars().nth(self.current) == Some(expected);
        if result {
            self.current += 1;
        }
        result
    }
    fn scan_token(&mut self) -> LexResult<()> {
        let c = self.advance();
        match c {
            ',' => Ok(self.add_token_type(TokenType::Comma)),
            '?' => Ok(self.add_token_type(TokenType::Question)),
            ':' => Ok(self.add_token_type(TokenType::Colon)),
            '(' => Ok(self.add_token_type(TokenType::OpenParen)),
            ')' => Ok(self.add_token_type(TokenType::CloseParen)),
            '{' => Ok(self.add_token_type(TokenType::OpenBrace)),
            '}' => Ok(self.add_token_type(TokenType::CloseBrace)),
            '.' => Ok(self.add_token_type(TokenType::Dot)),
            '-' => Ok(self.add_token_type(TokenType::Minus)),
            '+' => Ok(self.add_token_type(TokenType::Plus)),
            ';' => Ok(self.add_token_type(TokenType::Semicolon)),
            '*' => Ok(self.add_token_type(TokenType::Star)),

            // TODO reduce duplication
            '!' => {
                let m = self.matches('=');
                Ok(self.add_token_type(if m { TokenType::BangEqual } else { TokenType::Bang }))
            }
            '=' => {
                let m = self.matches('=');
                Ok(self.add_token_type(if m { TokenType::EqualEqual } else { TokenType::Equal }))
            }
            '<' => {
                let m = self.matches('=');
                Ok(self.add_token_type(if m { TokenType::LessEqual } else { TokenType::Less }))
            }
            '>' => {
                let m = self.matches('=');
                Ok(self.add_token_type(if m { TokenType::GreaterEqual } else { TokenType::Greater }))
            }

            '/' =>
                if self.matches('/') {
                    self.skip_line_comment();
                    Ok(())
                } else if self.matches('*') {
                    self.skip_multiline_comment()?;
                    Ok(())
                } else {
                    Ok(self.add_token_type(TokenType::Slash))
                },

            ' ' | '\r' | '\t' => Ok(()),
            '\n' => {
                self.line += 1;
                Ok(())
            }
            '"' => self.read_string_literal().map(|e| self.add_token_type(e)),
            c =>
                if c.is_ascii_digit() {
                    let num = self.read_number_literal();
                    Ok(self.add_token_type(num))
                } else if c.is_alphabetic() {
                    let ident = self.read_identifier();
                    Ok(self.add_token_type(ident))
                } else {
                    self.error("unexpected char.")
                }
        }
    }

    fn error<A>(&self, msg: &str) -> LexResult<A> {
        Err(LexError::error(self.line, msg.to_owned()))
    }

    fn advance(&mut self) -> char {
        let result = self.source.chars().nth(self.current);
        self.current += 1;
        result.expect("Source is empty")
    }

    fn skip_line_comment(&mut self) -> () {
        while self.peek_test(negated_char_test('\n')) {
            self.advance();
        }
    }

    fn skip_multiline_comment(&mut self) -> LexResult<()> {
        while self.peek_test(negated_char_test('*')) || self.peek_n_test(1, negated_char_test('/')) {
            self.advance();
        }
        if self.peek_test(negated_char_test('*')) || self.peek_n_test(1, negated_char_test('/')) {
            self.error("unterminated multiline comment.")
        } else {
            self.current += 2; // Skip past closing comment
            Ok(())
        }
    }

    fn peek_test<F: CharTest>(&self, f: F) -> bool {
        self.peek_n_test(0, f)
    }
    fn peek_n_test<F: CharTest>(&self, n: usize, f: F) -> bool {
        self.source.chars().nth(self.current + n).map(|e| f.char_test(e)).unwrap_or(false)
    }

    fn read_number_literal(&mut self) -> TokenType {
        while self.peek_test(|e: char| e.is_numeric() || e == '.') {
            self.advance();
        }
        TokenType::number_literal(self.current_lexeme().parse::<f64>().expect("invalid number."))
    }

    fn read_string_literal(&mut self) -> LexResult<TokenType> {
        while self.peek_test(negated_char_test('"')) {
            if self.peek_test('\n') {
                self.line += 1
            }
            self.advance();
        }
        if self.is_at_end() {
            self.error("Unterminated string.")
        } else {
            self.start += 1; // Skip opening "
            let result = Ok(TokenType::string_literal(self.current_lexeme()));
            self.advance(); // Move past closing "
            result
        }
    }

    fn read_identifier(&mut self) -> TokenType {
        while self.peek_test(|e: char| e.is_alphanumeric() || e == '_') {
            self.advance();
        }
        let word = self.current_lexeme();
        Lexer::get_keyword(word).unwrap_or(TokenType::identifier(word))
    }

    fn current_lexeme(&self) -> &str {
        return &self.source[self.start..self.current];
    }
    fn get_keyword(word: &str) -> Option<TokenType> {
        match word.to_lowercase().as_str() {
            "and" => Some(TokenType::And),
            "class" => Some(TokenType::Class),
            "else" => Some(TokenType::Else),
            "false" => Some(TokenType::False),
            "for" => Some(TokenType::For),
            "fun" => Some(TokenType::Fun),
            "if" => Some(TokenType::If),
            "nil" => Some(TokenType::Nil),
            "or" => Some(TokenType::Or),
            "print" => Some(TokenType::Print),
            "return" => Some(TokenType::Return),
            "super" => Some(TokenType::Super),
            "this" => Some(TokenType::This),
            "true" => Some(TokenType::True),
            "var" => Some(TokenType::Var),
            "while" => Some(TokenType::While),
            _ => None,
        }
    }
}

trait CharTest {
    fn char_test(&self, c: char) -> bool;
}

fn negated_char_test(c: char) -> impl CharTest {
    move |c2| { c2 != c }
}

impl CharTest for char {
    fn char_test(&self, c: char) -> bool { self == &c }
}

impl<F> CharTest for F where F: Fn(char) -> bool {
    fn char_test(&self, c: char) -> bool { self(c) }
}

#[cfg(test)]
mod tests {
    use crate::rslox::common::tests::unsafe_tokenize;
    use super::*;

    #[test]
    fn test_identifier() {
        assert_eq!(
            unsafe_tokenize(vec!["x_y"]),
            vec!(Token::new(1, TokenType::identifier("x_y"))),
        )
    }

    #[test]
    fn test_basic_example() {
        assert_eq!(
            unsafe_tokenize(vec!["var x = \"language\";"]),
            vec!(
                Token::new(1, TokenType::Var),
                Token::new(1, TokenType::identifier("x")),
                Token::new(1, TokenType::Equal),
                Token::new(1, TokenType::string_literal("language")),
                Token::new(1, TokenType::Semicolon),
            ),
        )
    }

    #[test]
    fn test_basic_expression() {
        assert_eq!(
            unsafe_tokenize(vec!["x + 42 > \"foo\""]),
            vec!(
                Token::new(1, TokenType::identifier("x")),
                Token::new(1, TokenType::Plus),
                Token::new(1, TokenType::NumberLiteral(42.0)),
                Token::new(1, TokenType::Greater),
                Token::new(1, TokenType::string_literal("foo")),
            ),
        )
    }

    #[test]
    fn test_ternary() {
        assert_eq!(
            unsafe_tokenize(vec!["a ? b : c"]),
            vec!(
                Token::new(1, TokenType::identifier("a")),
                Token::new(1, TokenType::Question),
                Token::new(1, TokenType::identifier("b")),
                Token::new(1, TokenType::Colon),
                Token::new(1, TokenType::identifier("c")),
            ),
        )
    }

    #[test]
    fn test_comments() {
        assert_eq!(
            unsafe_tokenize(vec!["42 / 54.13; // Right?\n var xyz /**/ = /*//*/ foobar;"]),
            vec!(
                Token::new(1, TokenType::NumberLiteral(42.0)),
                Token::new(1, TokenType::Slash),
                Token::new(1, TokenType::NumberLiteral(54.13)),
                Token::new(1, TokenType::Semicolon),
                Token::new(2, TokenType::Var),
                Token::new(2, TokenType::identifier("xyz")),
                Token::new(2, TokenType::Equal),
                Token::new(2, TokenType::identifier("foobar")),
                Token::new(2, TokenType::Semicolon),
            ),
        )
    }

    #[test]
    fn return_in_function() {
        assert_eq!(
            unsafe_tokenize(vec!["fun f(x) { return x+1; }"]),
            vec![
                Token::new(1, TokenType::Fun),
                Token::new(1, TokenType::identifier("f")),
                Token::new(1, TokenType::OpenParen),
                Token::new(1, TokenType::identifier("x")),
                Token::new(1, TokenType::CloseParen),
                Token::new(1, TokenType::OpenBrace),
                Token::new(1, TokenType::Return),
                Token::new(1, TokenType::identifier("x")),
                Token::new(1, TokenType::Plus),
                Token::new(1, TokenType::number_literal(1.0)),
                Token::new(1, TokenType::Semicolon),
                Token::new(1, TokenType::CloseBrace),
            ],
        )
    }
}