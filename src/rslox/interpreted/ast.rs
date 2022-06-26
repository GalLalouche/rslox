use crate::rslox::interpreted::ast::Statement::Function;

#[derive(Debug, PartialEq, Clone)]
pub struct Program {
    pub statements: Vec<Statement>,
}

impl Program {
    pub fn new(statements: Vec<Statement>) -> Self { Program { statements } }
}

#[derive(Debug, PartialEq, Clone)]
pub struct FunctionDef {
    pub name: String,
    pub params: Vec<String>,
    pub body: Vec<Statement>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Block(Vec<Statement>),
    Class(String, Vec<FunctionDef>),
    IfElse { cond: Expression, if_stmt: Box<Statement>, else_stmt: Option<Box<Statement>> },
    While(Expression, Box<Statement>),
    Variable(String, Expression),
    Function(FunctionDef),
    Expression(Expression),
    Print(Expression),
    Return(Option<Expression>),
}

impl Statement {
    pub fn variable<S: Into<String>>(str: S, expr: Expression) -> Self {
        Statement::Variable(str.into(), expr)
    }
    pub fn class<S: Into<String>>(name: S, args: Vec<FunctionDef>) -> Self {
        Statement::Class(name.into(), args)
    }
    pub fn function<S: Into<String>>(name: S, args: Vec<&str>, body: Vec<Statement>) -> Self {
        Function(FunctionDef {
            name: name.into(),
            params: args.into_iter().map(|e| e.into()).collect(),
            body,
        })
    }
}

pub type ScopeJumps = usize;

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Grouping(Box<Expression>),
    Property(Box<Expression>, String),
    Assign(String, Box<Expression>),
    Set(Box<Expression>, String, Box<Expression>),
    FunctionCall(Box<Expression>, Vec<Expression>),
    Unary(UnaryOperator, Box<Expression>),
    Binary(BinaryOperator, Box<Expression>, Box<Expression>),
    Ternary(Box<Expression>, Box<Expression>, Box<Expression>),
    Atomic(Atom),
    // Stupid hacks to avoid rewriting a new AST for this nonsense.
    ResolvedIdentifier(String, ScopeJumps),
    ResolvedAssignment(String, ScopeJumps, Box<Expression>),
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
                    Atom::This => indent("this"),
                }
                Expression::Grouping(e) => indent(format!("(\n{})", aux(e, depth + 1)).as_ref()),
                Expression::Property(e, name) =>
                    indent(format!("({}.{})", aux(e, depth), name).as_ref()),
                Expression::FunctionCall(f, args) =>
                    indent(format!(
                        "{}(\n{})",
                        aux(f, depth),
                        args.into_iter()
                            .map(|arg| aux(arg, depth + 1))
                            .intersperse(",\n".to_owned())
                            .collect::<String>(),
                    ).as_ref()),
                Expression::Assign(t, e) =>
                    indent(format!("{} := (\n{})", t, aux(e, depth + 1)).as_ref()),
                Expression::Set(g, t, e) =>
                    indent(format!("{}.{} := (\n{})", aux(g, depth), t, aux(e, depth + 1)).as_ref()),
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
                Expression::ResolvedIdentifier(name, jumps) =>
                    indent(format!("{} resolves {}", name, jumps).as_ref()),
                Expression::ResolvedAssignment(name, jumps, expr) =>
                    indent(format!(
                        "{} resolved {} := (\n{})",
                        name,
                        jumps,
                        aux(expr, depth + 1),
                    ).as_ref()),
            }
        }
        aux(self, 0)
    }
    pub fn identifier<S: Into<String>>(str: S) -> Self {
        Expression::Atomic(Atom::Identifier(str.into()))
    }
    pub fn resolved_identifier<S: Into<String>>(str: S, scope_jumps: ScopeJumps) -> Self {
        Expression::ResolvedIdentifier(str.into(), scope_jumps)
    }
    pub fn string<S: Into<String>>(str: S) -> Self { Expression::Atomic(Atom::String(str.into())) }
    pub fn property<S: Into<String>>(expr: Expression, str: S) -> Self {
        Expression::Property(Box::new(expr), str.into())
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
    This,
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