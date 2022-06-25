use std::ops::Deref;

use crate::rslox1::ast::{Atom, BinaryOperator, Expression, FunctionDef, Program, ScopeJumps, Statement, UnaryOperator};
use crate::rslox1::common::ErrorInfo;

#[derive(Debug, PartialEq, Clone)]
pub struct AnnotatedProgram {
    pub statements: Vec<AnnotatedStatement>,
}

impl AnnotatedProgram {
    pub fn new(statements: Vec<AnnotatedStatement>) -> Self {
        AnnotatedProgram { statements }
    }
}

impl From<&AnnotatedProgram> for Program {
    fn from(ae: &AnnotatedProgram) -> Self {
        Program { statements: ae.statements.iter().map(|e| e.into()).collect() }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct AnnotatedFunctionDef {
    pub name: String,
    pub params: Vec<String>,
    pub body: Vec<AnnotatedStatement>,
    pub error_info: ErrorInfo,
}

#[derive(Debug, PartialEq, Clone)]
pub enum AnnotatedStatement {
    Block(Vec<AnnotatedStatement>, ErrorInfo),
    Class(String, Vec<AnnotatedFunctionDef>, ErrorInfo),
    IfElse {
        cond: AnnotatedExpression,
        if_stmt: Box<AnnotatedStatement>,
        else_stmt: Option<Box<AnnotatedStatement>>,
        error_info: ErrorInfo,
    },
    While(AnnotatedExpression, Box<AnnotatedStatement>, ErrorInfo),
    Variable(String, AnnotatedExpression, ErrorInfo),
    Function(AnnotatedFunctionDef),
    Print(AnnotatedExpression, ErrorInfo),
    Return(Option<AnnotatedExpression>, ErrorInfo),
    Expression(AnnotatedExpression),
}

impl From<&AnnotatedFunctionDef> for FunctionDef {
    fn from(f: &AnnotatedFunctionDef) -> Self {
        match f {
            AnnotatedFunctionDef { name, params, body, .. } => FunctionDef {
                name: name.clone(),
                params: params.clone(),
                body: body.into_iter().map(|e| e.into()).collect(),
            }
        }
    }
}

impl From<&AnnotatedStatement> for Statement {
    fn from(ae: &AnnotatedStatement) -> Self {
        match ae {
            AnnotatedStatement::Block(ss, _) =>
                Statement::Block(ss.into_iter().map(|e| e.into()).collect()),
            AnnotatedStatement::Class(name, funcs, _) =>
                Statement::Class(name.to_owned(), funcs.iter().map(|e| e.into()).collect()),
            AnnotatedStatement::IfElse { cond, if_stmt, else_stmt, .. } =>
                Statement::IfElse {
                    cond: cond.into(),
                    if_stmt: Box::new(if_stmt.deref().into()),
                    else_stmt: else_stmt.as_ref().map(|e| Box::new(e.deref().into())),
                },
            AnnotatedStatement::While(cond, stmt, _) =>
                Statement::While(cond.into(), Box::new(stmt.as_ref().into())),
            AnnotatedStatement::Variable(n, e, _) => Statement::Variable(n.clone(), e.into()),
            AnnotatedStatement::Function(f) => Statement::Function(f.into()),
            AnnotatedStatement::Expression(e) => Statement::Expression(e.into()),
            AnnotatedStatement::Return(o, _) => Statement::Return(o.as_ref().map(|e| e.into())),
            AnnotatedStatement::Print(p, _) => Statement::Print(p.into()),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum AnnotatedExpression {
    Atomic(Atom, ErrorInfo),
    Grouping(Box<AnnotatedExpression>, ErrorInfo),
    Property(Box<AnnotatedExpression>, String, ErrorInfo),
    FunctionCall(Box<AnnotatedExpression>, Vec<AnnotatedExpression>, ErrorInfo),
    Assign(String, Box<AnnotatedExpression>, ErrorInfo),
    Set(Box<AnnotatedExpression>, String, Box<AnnotatedExpression>, ErrorInfo),
    Unary(UnaryOperator, Box<AnnotatedExpression>, ErrorInfo),
    Binary(BinaryOperator, Box<AnnotatedExpression>, Box<AnnotatedExpression>, ErrorInfo),
    Ternary(Box<AnnotatedExpression>, Box<AnnotatedExpression>, Box<AnnotatedExpression>, ErrorInfo),
    ResolvedIdentifier(String, ScopeJumps, ErrorInfo),
    ResolvedAssignment(String, ScopeJumps, Box<AnnotatedExpression>, ErrorInfo),
}

impl AnnotatedExpression {
    pub fn error_info(&self) -> ErrorInfo {
        *(match self {
            AnnotatedExpression::Atomic(_, i) => i,
            AnnotatedExpression::Grouping(_, i) => i,
            AnnotatedExpression::Property(_, _, i) => i,
            AnnotatedExpression::FunctionCall(_, _, i) => i,
            AnnotatedExpression::Assign(_, _, i) => i,
            AnnotatedExpression::Set(_, _, _, i) => i,
            AnnotatedExpression::Unary(_, _, i) => i,
            AnnotatedExpression::Binary(_, _, _, i) => i,
            AnnotatedExpression::Ternary(_, _, _, i) => i,
            AnnotatedExpression::ResolvedIdentifier(_, _, i) => i,
            AnnotatedExpression::ResolvedAssignment(_, _, _, i) => i,
        })
    }
}

impl From<&AnnotatedExpression> for Expression {
    fn from(ae: &AnnotatedExpression) -> Self {
        match ae {
            AnnotatedExpression::Atomic(e, _) => Expression::Atomic(e.to_owned()),
            AnnotatedExpression::Grouping(e, _) =>
                Expression::Grouping(Box::new(e.as_ref().into())),
            AnnotatedExpression::Property(e, n, _) => Expression::property(e.as_ref().into(), n),
            AnnotatedExpression::FunctionCall(f, args, _) =>
                Expression::FunctionCall(
                    Box::new(f.as_ref().into()),
                    args.into_iter().map(|e| e.into()).collect(),
                ),
            AnnotatedExpression::Assign(n, e, _) =>
                Expression::Assign(n.to_owned(), Box::new(e.as_ref().into())),
            AnnotatedExpression::Set(g, n, e, _) => Expression::Set(
                Box::new(g.as_ref().into()),
                n.to_owned(),
                Box::new(e.as_ref().into()),
            ),
            AnnotatedExpression::Unary(op, e, _) =>
                Expression::Unary(*op, Box::new(e.as_ref().into())),
            AnnotatedExpression::Binary(op, e1, e2, _) =>
                Expression::Binary(
                    *op,
                    Box::new(e1.as_ref().into()),
                    Box::new(e2.as_ref().into()),
                ),
            AnnotatedExpression::Ternary(cond, e1, e2, _) =>
                Expression::Ternary(
                    Box::new(cond.as_ref().into()),
                    Box::new(e1.as_ref().into()),
                    Box::new(e2.as_ref().into()),
                ),
            AnnotatedExpression::ResolvedIdentifier(name, jumps, _) =>
                Expression::ResolvedIdentifier(name.into(), *jumps),
            AnnotatedExpression::ResolvedAssignment(name, jumps, expr, _) =>
                Expression::ResolvedAssignment(name.into(), *jumps, Box::new(expr.as_ref().into())),
        }
    }
}
