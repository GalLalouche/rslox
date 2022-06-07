use std::fmt;
use std::fmt::Formatter;

pub fn run(line: &str) -> LexResult<()> {
    let tokens = tokenize(line)?;
    for token in tokens {
        println!("{:?}", token);
    }
    Ok(())
}

fn tokenize(source: &str) -> LexResult<Vec<Token>> {
    Lexer::new(source).get_lexems()
}


// Only failure possible during lexing is unterminated string or multi-line comment. Therefore, at
// most one error can occur at any given time.
pub type LexResult<A> = Result<A, LexError>;

#[derive(Debug, PartialEq, Clone)]
pub enum TokenType {
    // Single-character tokens.
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
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

    StringLiteral { literal: String },
    NumberLiteral { literal: f64 },
    Identifier { name: String },

    Eof,
}

impl TokenType {
    fn string_literal(str: &str) -> Self {
        TokenType::StringLiteral { literal: str.to_owned() }
    }
    fn number_literal(f: f64) -> Self {
        TokenType::NumberLiteral { literal: f }
    }
    fn identifier(str: &str) -> Self {
        TokenType::Identifier { name: str.to_owned() }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    line: usize,
    r#type: TokenType,
}

impl Token {
    fn new(line: usize, r#type: TokenType) -> Self {
        Token { line, r#type }
    }
}

#[derive(Debug)]
pub struct LexError {
    line: usize,
    r#where: String,
    message: String,
}

impl LexError {
    fn error(line: usize, message: String) -> LexError {
        LexError::report(line, "".to_owned(), message)
    }
    fn report(line: usize, r#where: String, message: String) -> LexError {
        LexError { line, r#where, message }
    }
}

impl fmt::Display for LexError {
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
            '(' => Ok(self.add_token_type(TokenType::LeftParen)),
            ')' => Ok(self.add_token_type(TokenType::RightParen)),
            '{' => Ok(self.add_token_type(TokenType::LeftBrace)),
            '}' => Ok(self.add_token_type(TokenType::RightBrace)),
            ',' => Ok(self.add_token_type(TokenType::Comma)),
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
            '>' => {
                let m = self.matches('=');
                Ok(self.add_token_type(if m { TokenType::LessEqual } else { TokenType::Less }))
            }
            '<' => {
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
        while !self.is_at_end() && self.peek() != '\n' {
            self.advance();
        }
    }

    fn skip_multiline_comment(&mut self) -> LexResult<()> {
        while self.current < self.source.len() - 1 && (self.peek() != '*' || self.peek_n(1) != '/') {
            self.advance();
        }
        if self.current >= self.source.len() - 1 || self.peek() != '*' || self.peek_n(1) != '/' {
            self.error("unterminated multiline comment.")
        } else {
            self.current += 2; // Skip past closing comment
            Ok(())
        }
    }

    fn peek(&self) -> char {
        self.peek_n(0)
    }
    fn peek_n(&self, n: usize) -> char {
        self.source.chars().nth(self.current + n)
            .expect(format!(
                "Index {} is out of bounds for source {}",
                self.current,
                self.source.len(),
            ).as_str())
    }

    fn read_number_literal(&mut self) -> TokenType {
        while self.peek().is_numeric() || self.peek() == '.' {
            self.advance();
        }
        TokenType::number_literal(self.current_lexeme().parse::<f64>().expect("invalid number."))
    }

    fn read_string_literal(&mut self) -> LexResult<TokenType> {
        while !self.is_at_end() && self.peek() != '"' {
            if self.peek() == '\n' {
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
        while self.peek().is_alphanumeric() {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_example() {
        assert_eq!(
            vec!(
                Token::new(1, TokenType::Var),
                Token::new(1, TokenType::Identifier { name: "x".to_owned() }),
                Token::new(1, TokenType::Equal),
                Token::new(1, TokenType::StringLiteral { literal: "language".to_owned() }),
                Token::new(1, TokenType::Semicolon),
            ),
            tokenize("var x = \"language\";").expect("tokenize failed")
        )
    }

    #[test]
    fn test_comments() {
        assert_eq!(
            vec!(
                Token::new(1, TokenType::NumberLiteral { literal: 42.0 }),
                Token::new(1, TokenType::Slash),
                Token::new(1, TokenType::NumberLiteral { literal: 54.13 }),
                Token::new(1, TokenType::Semicolon),
                Token::new(2, TokenType::Var),
                Token::new(2, TokenType::Identifier { name: "xyz".to_owned() }),
                Token::new(2, TokenType::Equal),
                Token::new(2, TokenType::Identifier { name: "foobar".to_owned() }),
                Token::new(2, TokenType::Semicolon),
            ),
            tokenize("42 / 54.13; // Right?\n var xyz /**/ = /*//*/ foobar;").expect("tokenize failed")
        )
    }
}