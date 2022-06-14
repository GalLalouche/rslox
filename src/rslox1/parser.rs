use nonempty::NonEmpty;

use crate::rslox1::annotated_ast::{AnnotatedExpression, AnnotatedProgram, AnnotatedStatement};
use crate::rslox1::annotated_ast::AnnotatedExpression::{Assign, Atomic};
use crate::rslox1::annotated_ast::AnnotatedStatement::{Block, Variable};
use crate::rslox1::ast::{Atom, BinaryOperator, UnaryOperator};
use crate::rslox1::common;
use crate::rslox1::common::{ErrorInfo, LoxError, LoxResult};
use crate::rslox1::lexer::{Token, TokenType};

#[derive(Debug)]
struct Parser<'a> {
    tokens: &'a Vec<Token>,
    errors: Vec<ParserError>,
    current: usize,
}

#[derive(Debug, PartialEq, Clone)]
struct ParserError {
    message: String,
    token: Token,
}

impl LoxError for ParserError {
    fn get_info(&self) -> ErrorInfo {
        ErrorInfo { line: self.token.line }
    }

    fn get_message(&self) -> String {
        self.message.to_owned()
    }
}

pub fn parse(tokens: &Vec<Token>) -> LoxResult<AnnotatedProgram> {
    common::convert_errors(Parser::parse(tokens))
}

type ParserResult<A> = Result<A, NonEmpty<ParserError>>;

impl<'a> Parser<'a> {
    pub fn parse(tokens: &Vec<Token>) -> ParserResult<AnnotatedProgram> {
        let mut parser = Parser { tokens, current: 0, errors: Vec::new() };
        parser.program()
    }

    fn program(&mut self) -> ParserResult<AnnotatedProgram> {
        let mut statements = Vec::new();
        while !self.is_at_end() {
            match self.block() {
                Ok(s) => statements.push(s),
                Err(e) => {
                    self.errors.push(e);
                    self.synchronize();
                }
            }
        }
        NonEmpty::from_vec(self.errors.clone())
            .map(Err)
            .unwrap_or(Ok(AnnotatedProgram { statements }))
    }

    fn block(&mut self) -> Result<AnnotatedStatement, ParserError> {
        self.matches_single(TokenType::LeftBrace)
            .map(|i| {
                let mut statements = Vec::new();
                while !self.is_at_end() && self.peek().get_type() != &TokenType::RightBrace {
                    self.block().map(|e| statements.push(e))?;
                }
                self.consume(TokenType::RightBrace, None).unwrap();
                Ok(Block(statements, i))
            }).unwrap_or_else(|| self.declaration())
    }
    fn declaration(&mut self) -> Result<AnnotatedStatement, ParserError> {
        self.matches_single(TokenType::Var)
            .map(|i| {
                let token = self.advance();
                let name = match token.get_type() {
                    TokenType::Identifier(name) => Ok(name.to_owned()),
                    _ => Err(ParserError {
                        message: format!("Expected identifier, got {:?}", token),
                        token: token.to_owned(),
                    })
                }?;
                let expr = self.matches_single(TokenType::Equal)
                    .map(|_| self.expression())
                    .unwrap_or(Ok(Atomic(Atom::Nil, i)))?;
                Ok(Variable(name, expr, i))
            }).unwrap_or_else(|| {
            self.statement()
        }).and_then(|e| {
            self.consume(TokenType::Semicolon, None)?;
            Ok(e)
        })
    }

    fn statement(&mut self) -> Result<AnnotatedStatement, ParserError> {
        self.matches_single(TokenType::Print)
            .map(|i| {
                self.expression().map(|e| AnnotatedStatement::Print(e, i))
            }).unwrap_or_else(|| {
            self.expression().map(|e| AnnotatedStatement::Expression(e))
        })
    }

    fn expression(&mut self) -> Result<AnnotatedExpression, ParserError> {
        self.comma()
    }

    fn comma(&mut self) -> Result<AnnotatedExpression, ParserError> {
        self.binary(
            |e| match e {
                TokenType::Comma => Some(BinaryOperator::Comma),
                _ => None,
            },
            |e| e.ternary(),
        )
    }

    fn assignment(&mut self) -> Result<AnnotatedExpression, ParserError> {
        let expr = self.equality()?;
        let next = self.peek().clone();
        match next.get_type() {
            TokenType::Equal => {
                self.consume(TokenType::Equal, None).unwrap();
                let value = self.assignment()?;
                match &expr {
                    Atomic(Atom::Identifier(name), _) => Ok(
                        Assign(name.clone(), Box::new(value), next.error_info())),
                    e => Err(ParserError {
                        message: format!("Invalid assignment r-value {:?}", e),
                        token: next,
                    })
                }
            }
            _ => Ok(expr)
        }
    }

    fn ternary(&mut self) -> Result<AnnotatedExpression, ParserError> {
        let expr = self.assignment()?;
        if !self.is_at_end() && self.peek().get_type() == &TokenType::Question {
            let start_info = self.peek().error_info();
            self.advance();
            let if_true = self.assignment()?;
            self.consume(TokenType::Colon, None)?;
            let if_false = self.ternary()?;
            Ok(AnnotatedExpression::Ternary(
                Box::new(expr),
                Box::new(if_true),
                Box::new(if_false),
                start_info,
            ))
        } else {
            Ok(expr)
        }
    }


    fn equality(&mut self) -> Result<AnnotatedExpression, ParserError> {
        self.binary(
            |e| match e {
                TokenType::BangEqual => Some(BinaryOperator::BangEqual),
                TokenType::EqualEqual => Some(BinaryOperator::EqualEqual),
                _ => None,
            },
            |e| e.comparison(),
        )
    }

    fn comparison(&mut self) -> Result<AnnotatedExpression, ParserError> {
        self.binary(
            |e| match e {
                TokenType::Greater => Some(BinaryOperator::Greater),
                TokenType::Less => Some(BinaryOperator::Less),
                TokenType::GreaterEqual => Some(BinaryOperator::GreaterEqual),
                TokenType::LessEqual => Some(BinaryOperator::LessEqual),
                _ => None,
            },
            |e| e.term(),
        )
    }

    fn term(&mut self) -> Result<AnnotatedExpression, ParserError> {
        self.binary(
            |e| match e {
                TokenType::Minus => Some(BinaryOperator::Minus),
                TokenType::Plus => Some(BinaryOperator::Plus),
                _ => None,
            },
            |e| e.factor(),
        )
    }

    fn factor(&mut self) -> Result<AnnotatedExpression, ParserError> {
        self.binary(
            |e| match e {
                TokenType::Slash => Some(BinaryOperator::Div),
                TokenType::Star => Some(BinaryOperator::Mult),
                _ => None,
            },
            |e| e.unary(),
        )
    }

    fn unary(&mut self) -> Result<AnnotatedExpression, ParserError> {
        match self.matches(|e| match e {
            TokenType::Bang => Some(UnaryOperator::Bang),
            TokenType::Minus => Some(UnaryOperator::Minus),
            _ => None,
        }) {
            Some((operator, info)) => {
                let right = self.unary()?;
                return Ok(AnnotatedExpression::Unary(operator, Box::new(right), info));
            }
            None => self.primary(),
        }
    }

    fn primary(&mut self) -> Result<AnnotatedExpression, ParserError> {
        assert!(!self.is_at_end());
        let info = self.peek().error_info();
        self.matches(|e| match e {
            TokenType::False => Some(Atom::False),
            TokenType::True => Some(Atom::True),
            TokenType::Nil => Some(Atom::Nil),
            TokenType::StringLiteral(literal) => Some(Atom::string(literal)),
            TokenType::NumberLiteral(literal) => Some(Atom::Number(*literal)),
            TokenType::Identifier(name) => Some(Atom::identifier(name)),
            _ => None,
        })
            .map(|(l, i)| Atomic(l, i))
            .map(|e| Ok(e))
            .unwrap_or_else(|| {
                self.consume(TokenType::LeftParen, Some("Expression".to_owned()))?;
                let expr = self.expression()?;
                self.consume(TokenType::RightParen, None)?;
                Ok(AnnotatedExpression::Grouping(Box::new(expr), info))
            })
    }

    fn binary<F, Next>(&mut self, func: F, next: Next) -> Result<AnnotatedExpression, ParserError>
        where F: Fn(&TokenType) -> Option<BinaryOperator>,
              Next: Fn(&mut Parser) -> Result<AnnotatedExpression, ParserError> {
        let mut expr = next(self)?;
        loop {
            match self.matches(&func) {
                Some((operator, info)) => {
                    let right = next(self)?;
                    expr = AnnotatedExpression::Binary(
                        operator,
                        Box::new(expr),
                        Box::new(right),
                        info,
                    )
                }
                None => break,
            }
        }
        Ok(expr)
    }

    fn matches_single(&mut self, expected: TokenType) -> Option<ErrorInfo> {
        if !self.is_at_end() && self.peek().get_type() == &expected {
            Some(self.consume(expected, None).unwrap())
        } else {
            None
        }
    }

    fn consume(&mut self, expected: TokenType, msg: Option<String>) -> Result<ErrorInfo, ParserError> {
        let expected_msg = msg.unwrap_or(expected.to_string());
        if self.is_at_end() {
            Parser::error(
                format!("Expected {}, but encountered end of file", expected_msg),
                self.tokens.last().expect("empty tokens").to_owned(),
            )
        } else if self.peek().get_type() != &expected {
            let p = self.peek();
            Parser::error(
                format!(
                    "Expected {}, but encountered {} at line {}",
                    expected_msg,
                    p.get_type(),
                    p.line,
                ), p.to_owned())
        } else {
            assert_ne!(expected, TokenType::Eof);
            Ok(self.advance().error_info())
        }
    }

    fn error<A>(message: String, token: Token) -> Result<A, ParserError> {
        Err(ParserError { message, token })
    }


    fn matches<F, A>(&mut self, func: F) -> Option<(A, ErrorInfo)>
        where F: Fn(&TokenType) -> Option<A>
    {
        if self.is_at_end() {
            return None;
        }
        let result = func(self.peek().get_type()).map(|e| (e, self.peek().error_info()));
        if result.is_some() {
            self.advance();
        }
        result
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

    fn synchronize(&mut self) {
        self.advance();
        while !self.is_at_end() {
            if self.previous().get_type() == &TokenType::Semicolon {
                return;
            }
            match self.peek().get_type() {
                TokenType::Class | TokenType::Fun | TokenType::Var | TokenType::For | TokenType::If
                | TokenType::While | TokenType::Print | TokenType::Return => return,
                _ => (),
            }
            self.advance();
        }
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Borrow;

    use crate::rslox1::ast::{Expression, Program, Statement};
    use crate::rslox1::ast::Atom::Number;
    use crate::rslox1::ast::Expression::{Atomic, Binary, Grouping, Ternary, Unary};
    use crate::rslox1::lexer::tokenize;

    use super::*;

    fn parse_program(line: &str) -> Vec<Statement> {
        let tokens = tokenize(line).unwrap();
        let program: Program = parse(&tokens).unwrap().borrow().into();
        program.statements
    }

    fn parse_single_statement(line: &str) -> Statement {
        let tokens = tokenize(line).unwrap();
        let prog = Parser::parse(&tokens).unwrap();
        let stmts = AnnotatedProgram::from(prog).statements;
        assert_eq!(stmts.len(), 1);
        stmts.first().unwrap().into()
    }

    fn parse_expression(line: &str) -> Expression {
        match parse_single_statement(line) {
            Statement::Expression(e) => e.into(),
            e => panic!("Expected an expression, got {:?}", e),
        }
    }

    #[test]
    fn basic_expression() {
        let expr = parse_expression("(x + 3) * 5;");
        let expected = Binary(
            BinaryOperator::Mult,
            Box::new(
                Grouping(Box::new(
                    Binary(
                        BinaryOperator::Plus,
                        Box::new(Atomic(Atom::identifier("x"))),
                        Box::new(Atomic(Number(3.0))),
                    )
                ))
            ),
            Box::new(Atomic(Number(5.0))),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn comma_separated() {
        let expr = parse_expression("1, 2, 3;");
        let expected =
            Binary(
                BinaryOperator::Comma,
                Box::new(
                    Binary(
                        BinaryOperator::Comma,
                        Box::new(Atomic(Number(1.0))),
                        Box::new(Atomic(Number(2.0))),
                    )
                ),
                Box::new(Atomic(Number(3.0))),
            );
        assert_eq!(expr, expected);
     }

    #[test]
    fn string_concat() {
        let expr = parse_expression("1 + \"2\" + 3;");
        let expected =
            Binary(
                BinaryOperator::Plus,
                Box::new(
                    Binary(
                        BinaryOperator::Plus,
                        Box::new(Atomic(Number(1.0))),
                        Box::new(Atomic(Atom::string("2"))),
                    )
                ),
                Box::new(Atomic(Number(3.0))),
            );
        assert_eq!(expr, expected);
    }

    #[test]
    fn ternary_operator() {
        let expr = parse_expression("-z == (x > 12 ? x + 2 : 1 + 2 * 3);");

        let expected =
            Binary(
                BinaryOperator::EqualEqual,
                Box::new(
                    Unary(
                        UnaryOperator::Minus,
                        Box::new(Atomic(Atom::identifier("z"))),
                    )
                ),
                Box::new(Grouping(
                    Box::new(Ternary(
                        Box::new(Binary(
                            BinaryOperator::Greater,
                            Box::new(Atomic(Atom::identifier("x"))),
                            Box::new(Atomic(Number(12.0))),
                        )),
                        Box::new(Binary(
                            BinaryOperator::Plus,
                            Box::new(Atomic(Atom::identifier("x"))),
                            Box::new(Atomic(Number(2.0))),
                        )),
                        Box::new(Binary(
                            BinaryOperator::Plus,
                            Box::new(Atomic(Number(1.0))),
                            Box::new(
                                Binary(
                                    BinaryOperator::Mult,
                                    Box::new(Atomic(Number(2.0))),
                                    Box::new(Atomic(Number(3.0))),
                                ),
                            ),
                        )),
                    ))
                )),
            );
        assert_eq!(expr, expected);
    }

    #[test]
    fn nested_ternary_operator() {
        let expr = parse_expression("a ? b : c ? d : e;");

        let expected =
            Ternary(
                Box::new(Atomic(Atom::identifier("a"))),
                Box::new(Atomic(Atom::identifier("b"))),
                Box::new(Ternary(
                    Box::new(Atomic(Atom::identifier("c"))),
                    Box::new(Atomic(Atom::identifier("d"))),
                    Box::new(Atomic(Atom::identifier("e"))),
                )),
            );
        assert_eq!(expr, expected);
    }

    #[test]
    fn multiple_errors() {
        let tokens = tokenize("var 12 = 12;\nvar x = b ? 1 : \"foo\";\n 5x;").unwrap();
        let program = parse(&tokens).unwrap_err();
        assert_eq!(
            program.into_iter().map(|e| e.get_info().line).collect::<Vec<usize>>(),
            vec![1, 3]
        );
    }

    #[test]
    fn print_statement() {
        let stmt = parse_single_statement("print x1 <= x2;");
        let expected = Statement::Print(
            Binary(
                BinaryOperator::LessEqual,
                Box::new(Atomic(Atom::identifier("x1"))),
                Box::new(Atomic(Atom::identifier("x2"))),
            )
        );
        assert_eq!(stmt, expected);
    }

    #[test]
    fn variable_statement() {
        let stmt = parse_single_statement("var z = x1 >= x2;");
        let expected = Statement::variable(
            "z",
            Binary(
                BinaryOperator::GreaterEqual,
                Box::new(Atomic(Atom::identifier("x1"))),
                Box::new(Atomic(Atom::identifier("x2"))),
            ),
        );
        assert_eq!(stmt, expected);
    }

    #[test]
    fn nil_variable_statement() {
        let stmt = parse_single_statement("var z;");
        let expected = Statement::variable(
            "z",
            Atomic(Atom::Nil),
        );
        assert_eq!(stmt, expected);
    }

    #[test]
    fn variable_assignment() {
        let prog = parse_program("var x = 1;\n x = \"foo\";");
        let expected =
            vec![
                Statement::variable("x", Atomic(Number(1.0))),
                Statement::Expression(
                    Expression::Assign(
                        "x".to_owned(),
                        Box::new(Atomic(Atom::string("foo"))),
                    ),
                ),
            ];
        assert_eq!(prog, expected);
    }

    #[test]
    fn assignment() {
        let expr = parse_expression("x = 42;");
        let expected =
            Expression::Assign(
                "x".to_owned(),
                Box::new(Atomic(Number(42.0))),
            );
        assert_eq!(expr, expected);
    }

    #[test]
    fn block() {
        let statement = parse_single_statement("{\nvar z;\nvar x;\n}");
        let expected = Statement::Block(vec![
            Statement::variable("z", Atomic(Atom::Nil)),
            Statement::variable("x", Atomic(Atom::Nil)),
        ]);
        assert_eq!(statement, expected);
    }
}
