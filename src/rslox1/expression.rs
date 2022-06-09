#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Identifier(String),
    Literal(Literal),
    Grouping(Box<Expression>),
    Unary(UnaryOperator, Box<Expression>),
    Binary(BinaryOperator, Box<Expression>, Box<Expression>),
    Ternary(Box<Expression>, Box<Expression>, Box<Expression>),
}

impl Expression {
    pub fn identifier<S: Into<String>>(str: S) -> Self { Expression::Identifier(str.into()) }
    pub fn pretty_print(&self) -> String {
        fn aux(e: &Expression, depth: usize) -> String {
            let indent = |s: &str| -> String {
                format!("{}{}", "\t".repeat(depth), s.to_owned())
            };
            match e {
                Expression::Identifier(name) => indent(name),
                Expression::Literal(lit) => match lit {
                    Literal::Number(n) => indent(n.to_string().as_ref()),
                    Literal::String(s) => indent(format!("\"{}\"", s).as_ref()),
                    Literal::True => indent("true"),
                    Literal::False => indent("false"),
                    Literal::Nil => indent("nil"),
                }
                Expression::Grouping(e) => indent(format!("(\n{})", aux(e, depth + 1)).as_ref()),
                Expression::Unary(op, e) =>
                    indent(format!("{}(\n{})", op.symbol(), aux(e, depth + 1)).as_ref()),
                Expression::Binary(op, e1, e2) =>
                    indent(
                        format!("{}(\n{},\n{})",
                                op.symbol(),
                                aux(e1, depth + 1),
                                aux(e2, depth + 1),
                        ).as_ref()),
                Expression::Ternary(cond, e1, e2) =>
                    indent(
                        format!("{}?\n{}:\n{})",
                                aux(cond, depth),
                                aux(e1, depth + 1),
                                aux(e2, depth + 1),
                        ).as_ref()),
            }
        }
        aux(self, 0)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Literal {
    Number(f64),
    String(String),
    True,
    False,
    Nil,
}

#[derive(Debug, PartialEq, Clone, Copy, Eq)]
pub enum UnaryOperator {
    Minus,
    Bang,
}

impl UnaryOperator {
    pub fn symbol(&self) -> &str {
        match self {
            UnaryOperator::Minus => "-",
            UnaryOperator::Bang => "!",
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy, Eq)]
pub enum BinaryOperator {
    Comma,

    Minus,
    Plus,
    Div,
    Mult,

    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    And,
    Or,
}

impl BinaryOperator {
    pub fn symbol(&self) -> &str {
        match self {
            BinaryOperator::Comma => ",",
            BinaryOperator::Minus => "-",
            BinaryOperator::Plus => "+",
            BinaryOperator::Div => "/",
            BinaryOperator::Mult => "*",
            BinaryOperator::BangEqual => "!=",
            BinaryOperator::Equal => "=",
            BinaryOperator::EqualEqual => "==",
            BinaryOperator::Greater => ">",
            BinaryOperator::GreaterEqual => ">=",
            BinaryOperator::Less => "<",
            BinaryOperator::LessEqual => "<=",
            BinaryOperator::And => "&&",
            BinaryOperator::Or => "||",
        }
    }
}