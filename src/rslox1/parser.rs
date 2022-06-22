use nonempty::NonEmpty;

use crate::rslox1::annotated_ast::{AnnotatedExpression, AnnotatedFunctionDef, AnnotatedProgram, AnnotatedStatement};
use crate::rslox1::annotated_ast::AnnotatedExpression::{Assign, Atomic, Property, Set};
use crate::rslox1::annotated_ast::AnnotatedStatement::{Block, Function, Return, Variable};
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

impl ParserError {
    pub fn new<S: Into<String>>(message: S, token: Token) -> Self {
        ParserError { message: message.into(), token }
    }
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

    fn statement(&mut self) -> Result<AnnotatedStatement, ParserError> {
        self.block()
    }

    fn block(&mut self) -> Result<AnnotatedStatement, ParserError> {
        self.matches_single(TokenType::OpenBrace)
            .map(|i| {
                let mut statements = Vec::new();
                while !self.is_at_end() && self.peek().get_type() != &TokenType::CloseBrace {
                    self.block().map(|e| statements.push(e))?;
                }
                self.consume(TokenType::CloseBrace, None).unwrap();
                Ok(Block(statements, i))
            }).unwrap_or_else(|| self.class_statement())
    }

    fn class_statement(&mut self) -> Result<AnnotatedStatement, ParserError> {
        self.matches_single(TokenType::Class)
            .map(|i| {
                let name = self.identifier()?;
                self.consume(TokenType::OpenBrace, None)?;
                let mut methods = Vec::new();
                while self.peek_type() != &TokenType::CloseBrace {
                    let i = self.peek().error_info();
                    self.function(i).map(|f| methods.push(f))?;
                }
                self.consume(TokenType::CloseBrace, None)?;
                Ok(AnnotatedStatement::Class(name, methods, i))
            }).unwrap_or_else(|| self.if_statement())
    }
    fn if_statement(&mut self) -> Result<AnnotatedStatement, ParserError> {
        self.matches_single(TokenType::If)
            .map(|i| {
                self.consume(TokenType::OpenParen, None)?;
                let cond = self.expression()?;
                self.consume(TokenType::CloseParen, None)?;
                let if_stmt = self.statement().map(Box::new)?;
                let else_stmt = self.matches_single(TokenType::Else)
                    .map(|_| {
                        self.statement().map(|e| Some(Box::new(e)))
                    }).unwrap_or(Ok(None))?;
                Ok(AnnotatedStatement::IfElse {
                    cond,
                    if_stmt,
                    else_stmt,
                    error_info: i,
                })
            }).unwrap_or_else(|| self.while_statement())
    }

    fn while_statement(&mut self) -> Result<AnnotatedStatement, ParserError> {
        self.matches_single(TokenType::While)
            .map(|i| {
                self.consume(TokenType::OpenParen, None)?;
                let cond = self.expression()?;
                self.consume(TokenType::CloseParen, None)?;
                let stmt = self.statement().map(Box::new)?;
                Ok(AnnotatedStatement::While(cond, stmt, i))
            }).unwrap_or_else(|| self.for_statement())
    }

    fn for_statement(&mut self) -> Result<AnnotatedStatement, ParserError> {
        self.matches_single(TokenType::For)
            .map(|i| {
                self.consume(TokenType::OpenParen, None)?;
                let pre = if self.peek_type() != &TokenType::Semicolon {
                    self.variable_declaration().map(Some)
                } else {
                    Ok(None)
                }?;
                if self.peek_type() == &TokenType::Semicolon {
                    // It's possible that the var declaration already consumed the semicolon. This
                    // is honestly a very stupid hack, since maybe declaration shouldn't always
                    // consume a semicolon, but it's good enough for now.
                    self.advance();
                }
                let cond = if self.peek_type() == &TokenType::Semicolon {
                    Ok(Atomic(Atom::True, i))
                } else {
                    self.expression()
                }?;
                self.consume(TokenType::Semicolon, None)?;
                let post = if self.peek_type() == &TokenType::CloseParen {
                    Ok(None)
                } else {
                    self.expression().map(Some)
                }?;
                self.consume(TokenType::CloseParen, None)?;
                let stmt = self.statement().map(Box::new)?;
                let body = if let Some(p) = post {
                    let error_info = p.error_info().clone();
                    Box::new(Block(vec![*stmt, AnnotatedStatement::Expression(p)], error_info))
                } else {
                    stmt
                };
                let while_stmt = AnnotatedStatement::While(cond, body, i);
                Ok(
                    if let Some(p) = pre {
                        Block(
                            vec![
                                p,
                                while_stmt,
                            ],
                            i,
                        )
                    } else {
                        while_stmt
                    }
                )
            }).unwrap_or_else(|| self.function_statement())
    }

    fn function_statement(&mut self) -> Result<AnnotatedStatement, ParserError> {
        if self.peek_type() == &TokenType::Fun {
            let i = self.advance().error_info();
            self.function(i).map(Function)
        } else {
            self.variable_declaration()
        }
    }

    fn function(&mut self, error_info: ErrorInfo) -> Result<AnnotatedFunctionDef, ParserError> {
        let name = self.identifier()?;
        self.consume(TokenType::OpenParen, None)?;
        let mut args = Vec::new();
        while self.peek_type() != &TokenType::CloseParen {
            self.identifier().map(|n| args.push(n))?;
            if self.peek_type() != &TokenType::CloseParen {
                self.consume(TokenType::Comma, None)?;
            }
        }
        self.consume(TokenType::CloseParen, None)?;
        self.consume(TokenType::OpenBrace, None)?;
        let mut body = Vec::new();
        while self.peek_type() != &TokenType::CloseBrace {
            self.statement().map(|s| body.push(s))?;
        }
        self.consume(TokenType::CloseBrace, None)?;
        Ok(AnnotatedFunctionDef {
            name,
            params: args,
            body,
            error_info,
        })
    }

    // Everything below this line expects a terminating semicolon.
    fn variable_declaration(&mut self) -> Result<AnnotatedStatement, ParserError> {
        self.matches_single(TokenType::Var)
            .map(|i| {
                let name = self.identifier()?;
                let expr = self.matches_single(TokenType::Equal)
                    .map(|_| self.expression())
                    .unwrap_or(Ok(Atomic(Atom::Nil, i)))?;
                Ok(Variable(name.to_owned(), expr, i))
            })
            .unwrap_or_else(|| self.return_statement())
            .and_then(|e| {
                self.consume(TokenType::Semicolon, None)?;
                Ok(e)
            })
    }

    fn return_statement(&mut self) -> Result<AnnotatedStatement, ParserError> {
        self.matches_single(TokenType::Return)
            .map(|i| {
                if self.peek_type() == &TokenType::Semicolon {
                    Ok(Return(None, i))
                } else {
                    let expr = self.expression()?;
                    Ok(Return(Some(expr), i))
                }
            }).unwrap_or_else(|| self.print())
    }

    fn print(&mut self) -> Result<AnnotatedStatement, ParserError> {
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
        let expr = self.logical_or()?;
        self.verify_no_end()?;
        let next = self.peek().clone();
        match next.get_type() {
            TokenType::Equal => {
                self.consume(TokenType::Equal, None).unwrap();
                let value = self.assignment()?;
                match &expr {
                    Atomic(Atom::Identifier(name), _) => Ok(
                        Assign(name.clone(), Box::new(value), next.error_info())),
                    Property(expr, name, _) => Ok(
                        Set(expr.to_owned(), name.clone(), Box::new(value), next.error_info())),
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

    fn logical_or(&mut self) -> Result<AnnotatedExpression, ParserError> {
        self.binary(
            |e| match e {
                TokenType::Or => Some(BinaryOperator::Or),
                _ => None,
            },
            |e| e.logical_and(),
        )
    }

    fn logical_and(&mut self) -> Result<AnnotatedExpression, ParserError> {
        self.binary(
            |e| match e {
                TokenType::And => Some(BinaryOperator::And),
                _ => None,
            },
            |e| e.equality(),
        )
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
            None => self.function_call(),
        }
    }

    fn function_call(&mut self) -> Result<AnnotatedExpression, ParserError> {
        let mut expr = self.primary()?;
        loop {
            if self.peek_type() == &TokenType::OpenParen {
                let i = self.consume(TokenType::OpenParen, None).unwrap();
                let mut args: Vec<AnnotatedExpression> = Vec::new();
                while self.peek_type() != &TokenType::CloseParen {
                    // Commas aren't a valid expression combiner inside a function call.
                    self.assignment().map(|e| args.push(e))?;
                    if self.peek_type() == &TokenType::Comma {
                        self.advance();
                    }
                }
                self.consume(TokenType::CloseParen, None)?;
                expr = Ok(AnnotatedExpression::FunctionCall(Box::new(expr), args, i))?;
            } else if self.peek_type() == &TokenType::Dot {
                let i = self.consume(TokenType::Dot, None).unwrap();
                let id = self.identifier()?;
                expr = Ok(Property(Box::new(expr), id, i))?;
            } else {
                break;
            }
        }
        Ok(expr)
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
                self.consume(TokenType::OpenParen, Some("Expression".to_owned()))?;
                let expr = self.expression()?;
                self.consume(TokenType::CloseParen, None)?;
                Ok(AnnotatedExpression::Grouping(Box::new(expr), info))
            })
    }

    fn identifier(&mut self) -> Result<String, ParserError> {
        if self.is_at_end() {
            Err(ParserError::new("Expected Identifier, encountered EOF", self.eof_token()))
        } else {
            match self.peek() {
                Token { r#type: TokenType::Identifier(name), .. } => {
                    let owned = name.to_owned();
                    self.advance();
                    Ok(owned)
                }
                e => Err(ParserError::new(
                    format!("Expected identifier, got: '{:?}'", e),
                    self.peek().clone(),
                ))
            }
        }
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

    fn peek_type(&self) -> &TokenType {
        if self.is_at_end() {
            &TokenType::Eof
        } else {
            self.peek().get_type()
        }
    }

    fn synchronize(&mut self) {
        if self.is_at_end() {
            return;
        }
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

    fn verify_no_end(&self) -> Result<(), ParserError> {
        if self.is_at_end() {
            Err(ParserError::new("Unexpected EOF", self.eof_token()))
        } else {
            Ok(())
        }
    }

    fn eof_token(&self) -> Token {
        Token::new(self.tokens.last().unwrap().line, TokenType::Eof)
    }
}

#[cfg(test)]
mod tests {
    use crate::rslox1::ast::{Expression, FunctionDef, Program, Statement};
    use crate::rslox1::ast::Atom::Number;
    use crate::rslox1::ast::Expression::{Atomic, Binary, FunctionCall, Grouping, Property, Set, Ternary, Unary};
    use crate::rslox1::ast::Statement::While;
    use crate::rslox1::lexer::tokenize;
    use crate::rslox1::unsafe_test::unsafe_parse;

    use super::*;

    fn parse_program(program: Vec<&str>) -> Vec<Statement> {
        Program::from(&unsafe_parse(program)).statements
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
                        Box::new(Expression::identifier("x")),
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
                        Box::new(Expression::string("2")),
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
                        Box::new(Expression::identifier("z")),
                    )
                ),
                Box::new(Grouping(
                    Box::new(Ternary(
                        Box::new(Binary(
                            BinaryOperator::Greater,
                            Box::new(Expression::identifier("x")),
                            Box::new(Atomic(Number(12.0))),
                        )),
                        Box::new(Binary(
                            BinaryOperator::Plus,
                            Box::new(Expression::identifier("x")),
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
                Box::new(Expression::identifier("a")),
                Box::new(Expression::identifier("b")),
                Box::new(Ternary(
                    Box::new(Expression::identifier("c")),
                    Box::new(Expression::identifier("d")),
                    Box::new(Expression::identifier("e")),
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
                Box::new(Expression::identifier("x1")),
                Box::new(Expression::identifier("x2")),
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
                Box::new(Expression::identifier("x1")),
                Box::new(Expression::identifier("x2")),
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
        let prog = parse_program(vec![
            "var x = 1;",
            r#"x = "foo";"#]);
        let expected =
            vec![
                Statement::variable("x", Atomic(Number(1.0))),
                Statement::Expression(
                    Expression::Assign(
                        "x".to_owned(),
                        Box::new(Expression::string("foo")),
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

    #[test]
    fn missing_semicolon() {
        let tokens = tokenize("print 42").unwrap();
        let program = parse(&tokens).unwrap_err();
        assert_eq!(
            program.into_iter().map(|e| e.get_info().line).collect::<Vec<usize>>(),
            vec![1]
        );
    }

    #[test]
    fn if_stmt() {
        let statement = parse_single_statement("if (x > 2) print y;");
        let expected = Statement::IfElse {
            cond: Binary(
                BinaryOperator::Greater,
                Box::new(Expression::identifier("x")),
                Box::new(Atomic(Number(2.0))),
            ),
            if_stmt: Box::new(Statement::Print(Expression::identifier("y"))),
            else_stmt: None,
        };
        assert_eq!(statement, expected);
    }

    #[test]
    fn if_else_stmt() {
        let statement = parse_single_statement("if (x > 2) print y; else {var z = true; print false;}");
        let expected = Statement::IfElse {
            cond: Binary(
                BinaryOperator::Greater,
                Box::new(Expression::identifier("x")),
                Box::new(Atomic(Number(2.0))),
            ),
            if_stmt: Box::new(Statement::Print(Expression::identifier("y"))),
            else_stmt: Some(Box::new(Statement::Block(
                vec![
                    Statement::variable("z", Atomic(Atom::True)),
                    Statement::Print(Atomic(Atom::False)),
                ]
            )
            )),
        };
        assert_eq!(statement, expected);
    }

    #[test]
    fn logical_operators_precedence() {
        let expr = parse_expression("a or b and c;");
        let expected = Binary(
            BinaryOperator::Or,
            Box::new(Expression::identifier("a")),
            Box::new(
                Binary(
                    BinaryOperator::And,
                    Box::new(Expression::identifier("b")),
                    Box::new(Expression::identifier("c")),
                ),
            ),
        );
        assert_eq!(expr, expected)
    }

    #[test]
    fn empty_for_loop_desugaring() {
        let expr = parse_single_statement("for (;;) print 4;");
        let expected = While(
            Atomic(Atom::True),
            Box::new(Statement::Print(Atomic(Number(4.0)))),
        );
        assert_eq!(expr, expected)
    }

    #[test]
    fn function_call_atomic() {
        let expr = parse_expression(r#"f(1, "foo", x);"#);
        let expected = FunctionCall(
            Box::new(Expression::identifier("f")),
            vec![
                Atomic(Number(1.0)),
                Expression::string("foo"),
                Expression::identifier("x"),
            ]);
        assert_eq!(expr, expected);
    }

    #[test]
    fn function_call_complex() {
        let expr = parse_expression(r#"f(g(), h(42) + z());"#);
        let expected = FunctionCall(
            Box::new(Expression::identifier("f")),
            vec![
                FunctionCall(Box::new(Expression::identifier("g")), Vec::new()),
                Binary(
                    BinaryOperator::Plus,
                    Box::new(FunctionCall(
                        Box::new(Expression::identifier("h")),
                        vec![Atomic(Number(42.0))],
                    )),
                    Box::new(FunctionCall(Box::new(Expression::identifier("z")), Vec::new())),
                ),
            ]);
        assert_eq!(expr, expected);
    }

    #[test]
    fn function_declaration_simple() {
        let stmt = parse_single_statement(r#"fun test() { print "hello world!"; }"#);
        let expected = Statement::Function(FunctionDef {
            name: "test".to_owned(),
            params: Vec::new(),
            body: vec![Statement::Print(Expression::string("hello world!"))],
        });
        assert_eq!(stmt, expected)
    }

    #[test]
    fn trivial_class() {
        let stmt = parse_single_statement("class Foo {}");
        assert_eq!(stmt, Statement::class("Foo", Vec::new()))
    }

    #[test]
    fn class_with_methods() {
        let stmt = parse_single_statement("class Foo {\nbar(x) {\nprint x;\n}\n}");
        assert_eq!(stmt, Statement::class(
            "Foo",
            vec![
                FunctionDef {
                    name: "bar".to_owned(),
                    params: vec!["x".into()],
                    body: vec![
                        Statement::Print(Expression::identifier("x")),
                    ],
                },
            ]))
    }

    #[test]
    fn trivial_constructor() {
        assert_eq!(
            parse_program(vec![
                "class Foo {}",
                "var foo = Foo();",
            ]),
            vec![
                Statement::class("Foo", Vec::new()),
                Statement::variable(
                    "foo",
                    FunctionCall(
                        Box::new(Expression::identifier("Foo")),
                        Vec::new(),
                    ),
                ),
            ],
        )
    }

    #[test]
    fn trivial_property() {
        assert_eq!(
            parse_expression("x.y;"),
            Property(Box::new(Expression::identifier("x")), "y".to_owned()),
        )
    }

    #[test]
    fn trivial_property_assignment() {
        assert_eq!(
            parse_expression("x.y = z;"),
            Set(
                Box::new(Expression::identifier("x")),
                "y".to_owned(),
                Box::new(Expression::identifier("z")),
            )
        )
    }

    #[test]
    fn complex_property() {
        assert_eq!(
            parse_expression("a.b(3).c(d);"),
            FunctionCall(
                Box::new(
                    Property(
                        Box::new(FunctionCall(
                            Box::new(Property(
                                Box::new(Expression::identifier("a")),
                                "b".to_owned(),
                            )),
                            vec![Atomic(Number(3.0))],
                        )),
                        "c".to_owned(),
                    )),
                vec![Expression::identifier("d")],
            ),
        )
    }
}
