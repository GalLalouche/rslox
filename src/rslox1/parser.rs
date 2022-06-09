use crate::rslox1::expression::{BinaryOperator, Expression, Literal, UnaryOperator};
use crate::rslox1::expression::Expression::{Grouping, Ternary};
use crate::rslox1::lexer::{Token, TokenType};

#[derive(Debug)]
pub struct Parser<'a> {
    tokens: &'a [Token],
    current: usize,
}

#[derive(Debug, PartialEq, Clone)]
pub struct ParserError {
    message: String,
    token: TokenType,
}

type ParserResult<A> = Result<A, ParserError>;

impl<'a> Parser<'a> {
    pub fn parse(tokens: &'a [Token]) -> ParserResult<(Expression, &'a [Token])> {
        let mut parser = Parser { tokens, current: 0 };
        let expr = parser.expression()?;
        Ok((expr, &parser.tokens[parser.current..]))
    }

    fn expression(&mut self) -> ParserResult<Expression> {
        self.comma()
    }

    fn comma(&mut self) -> ParserResult<Expression> {
        self.binary(
            |e| match e {
                TokenType::Comma => Some(BinaryOperator::Comma),
                _ => None,
            },
            |e| e.ternary(),
        )
    }

    fn ternary(&mut self) -> ParserResult<Expression> {
        let expr = self.equality()?;
        if !self.is_at_end() && self.peek().get_type() == &TokenType::Question {
            self.advance();
            let if_true = self.equality()?;
            self.consume(&TokenType::Colon, None)?;
            let if_false = self.ternary()?;
            Ok(Ternary(Box::new(expr), Box::new(if_true), Box::new(if_false)))
        } else {
            Ok(expr)
        }
    }

    fn equality(&mut self) -> ParserResult<Expression> {
        self.binary(
            |e| match e {
                TokenType::BangEqual => Some(BinaryOperator::BangEqual),
                TokenType::EqualEqual => Some(BinaryOperator::EqualEqual),
                _ => None,
            },
            |e| e.comparison(),
        )
    }

    fn comparison(&mut self) -> ParserResult<Expression> {
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

    fn term(&mut self) -> ParserResult<Expression> {
        self.binary(
            |e| match e {
                TokenType::Minus => Some(BinaryOperator::Minus),
                TokenType::Plus => Some(BinaryOperator::Plus),
                _ => None,
            },
            |e| e.factor(),
        )
    }

    fn factor(&mut self) -> ParserResult<Expression> {
        self.binary(
            |e| match e {
                TokenType::Slash => Some(BinaryOperator::Div),
                TokenType::Star => Some(BinaryOperator::Mult),
                _ => None,
            },
            |e| e.unary(),
        )
    }

    fn unary(&mut self) -> ParserResult<Expression> {
        match self.matches(|e| match e {
            TokenType::Bang => Some(UnaryOperator::Bang),
            TokenType::Minus => Some(UnaryOperator::Minus),
            _ => None,
        }) {
            Some(operator) => {
                let right = self.unary()?;
                return Ok(Expression::Unary(operator, Box::new(right)));
            }
            None => self.primary(),
        }
    }

    fn primary(&mut self) -> ParserResult<Expression> {
        self.matches(|e| match e {
            TokenType::False => Some(Expression::Literal(Literal::False)),
            TokenType::True => Some(Expression::Literal(Literal::True)),
            TokenType::Nil => Some(Expression::Literal(Literal::Nil)),
            TokenType::StringLiteral(literal) =>
                Some(Expression::Literal(Literal::String(literal.to_owned()))),
            TokenType::NumberLiteral(literal) =>
                Some(Expression::Literal(Literal::Number(*literal))),
            TokenType::Identifier(name) => Some(Expression::identifier(name)),
            _ => None,
        }).map(|e| Ok(e))
            .unwrap_or_else(|| {
                self.consume(&TokenType::LeftParen, Some("Expression".to_owned()))?;
                let expr = self.expression()?;
                self.consume(&TokenType::RightParen, None)?;
                Ok(Grouping(Box::new(expr)))
            })
    }

    fn binary<F, Next>(&mut self, func: F, next: Next) -> ParserResult<Expression>
        where F: Fn(&TokenType) -> Option<BinaryOperator>,
              Next: Fn(&mut Parser) -> ParserResult<Expression> {
        let mut expr = next(self)?;
        loop {
            match self.matches(&func) {
                Some(operator) => {
                    let right = next(self)?;
                    expr = Expression::Binary(operator, Box::new(expr), Box::new(right));
                }
                None => break,
            }
        }
        Ok(expr)
    }

    fn consume(&mut self, expected: &TokenType, msg: Option<String>) -> ParserResult<()> {
        let expected_msg = msg.unwrap_or(expected.to_string());
        if self.is_at_end() {
            Parser::error(
                format!("Expected {}, but encountered end of file", expected_msg), TokenType::Eof)
        } else if self.peek().get_type() != expected {
            let p = self.peek();
            Parser::error(
                format!(
                    "Expected {}, but encountered {} at line {}",
                    expected_msg,
                    p.get_type(),
                    p.line,
                ), p.get_type().to_owned())
        } else {
            assert_ne!(expected, &TokenType::Eof);
            self.advance();
            Ok(())
        }
    }

    fn error<A>(message: String, token: TokenType) -> ParserResult<A> {
        Err(ParserError { message, token })
    }


    fn matches<F, A>(&mut self, func: F) -> Option<A> where F: Fn(&TokenType) -> Option<A> {
        if self.is_at_end() {
            return None;
        }
        let result = func(self.peek().get_type());
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
}

#[cfg(test)]
mod tests {
    use crate::rslox1::expression::Expression::{Binary, Grouping, Literal, Ternary, Unary};
    use crate::rslox1::expression::Literal::Number;
    use crate::rslox1::lexer::tokenize;

    use super::*;

    #[test]
    fn test_basic_expression() {
        let tokens = tokenize("(x + 3) * 5").unwrap();
        let (expr, rem) = Parser::parse(tokens.as_slice()).unwrap();
        let expected = Binary(
            BinaryOperator::Mult,
            Box::new(
                Grouping(Box::new(
                    Binary(
                        BinaryOperator::Plus,
                        Box::new(Expression::identifier("x")),
                        Box::new(Literal(Number(3.0))),
                    )
                ))
            ),
            Box::new(Literal(Number(5.0))),
        );
        assert_eq!(expr, expected);
        assert_eq!(rem.len(), 0);
    }

    #[test]
    fn test_comma_separated() {
        let tokens = tokenize("1, 2, 3").unwrap();
        let (expr, rem) = Parser::parse(tokens.as_slice()).unwrap();
        let expected =
            Binary(
                BinaryOperator::Comma,
                Box::new(
                    Binary(
                        BinaryOperator::Comma,
                        Box::new(Literal(Number(1.0))),
                        Box::new(Literal(Number(2.0))),
                    )
                ),
                Box::new(Literal(Number(3.0))),
            );
        assert_eq!(expr, expected);
        assert_eq!(rem.len(), 0);
    }

    #[test]
    fn test_ternary_operator() {
        let tokens = tokenize("-z == (x > 12 ? x + 2 : 1 + 2 * 3)").unwrap();
        let (expr, rem) = Parser::parse(tokens.as_slice()).unwrap();
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
                            Box::new(Literal(Number(12.0))),
                        )),
                        Box::new(Binary(
                            BinaryOperator::Plus,
                            Box::new(Expression::identifier("x")),
                            Box::new(Literal(Number(2.0))),
                        )),
                        Box::new(Binary(
                            BinaryOperator::Plus,
                            Box::new(Literal(Number(1.0))),
                            Box::new(
                                Binary(
                                    BinaryOperator::Mult,
                                    Box::new(Literal(Number(2.0))),
                                    Box::new(Literal(Number(3.0))),
                                ),
                            ),
                        )),
                    ))
                )),
            );
        assert_eq!(expr, expected);
        assert_eq!(rem.len(), 0);
    }

    #[test]
    fn nested_ternary_operator() {
        let tokens = tokenize("a ? b : c ? d : e").unwrap();
        let (expr, rem) = Parser::parse(tokens.as_slice()).unwrap();
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
        assert_eq!(rem.len(), 0);
    }
}
