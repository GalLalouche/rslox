#[derive(Debug, PartialEq, Clone)]
pub struct Program {
    pub statements: Vec<Statement>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Block(Vec<Statement>),
    IfElse {cond: Expression, if_stmt: Box<Statement>, else_stmt: Option<Box<Statement>>},
    Variable(String, Expression),
    Expression(Expression),
    Print(Expression),
}

impl Statement {
    pub fn variable<S: Into<String>>(str: S, expr: Expression) -> Self {
        Statement::Variable(str.into(), expr)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Grouping(Box<Expression>),
    Assign(String, Box<Expression>),
    Unary(UnaryOperator, Box<Expression>),
    Binary(BinaryOperator, Box<Expression>, Box<Expression>),
    Ternary(Box<Expression>, Box<Expression>, Box<Expression>),
    Atomic(Atom),
}

impl Expression {
    pub fn pretty_print(&self) -> String {
        fn aux(e: &Expression, depth: usize) -> String {
            let indent = |s: &str| -> String {
                format!("{}{}", "\t".repeat(depth), s.to_owned())
            };
            match e {
                Expression::Atomic(lit) => match lit {
                    Atom::Identifier(name) => indent(name),
                    Atom::Number(n) => indent(n.to_string().as_ref()),
                    Atom::String(s) => indent(format!("\"{}\"", s).as_ref()),
                    Atom::True => indent("true"),
                    Atom::False => indent("false"),
                    Atom::Nil => indent("nil"),
                }
                Expression::Grouping(e) => indent(format!("(\n{})", aux(e, depth + 1)).as_ref()),
                Expression::Assign(t, e) =>
                    indent(format!("{:?} := (\n{})", t, aux(e, depth + 1)).as_ref()),
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
pub enum Atom {
    Identifier(String),
    Number(f64),
    String(String),
    True,
    False,
    Nil,
}

impl Atom {
    pub fn identifier<S: Into<String>>(str: S) -> Self { Atom::Identifier(str.into()) }
    pub fn string<S: Into<String>>(str: S) -> Self { Atom::String(str.into()) }
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