use std::ops::Deref;

use crate::rslox1::ast::{Atom, BinaryOperator, Expression, Program, Statement, UnaryOperator};
use crate::rslox1::common::ErrorInfo;

#[derive(Debug, PartialEq, Clone)]
pub struct AnnotatedProgram {
    pub statements: Vec<AnnotatedStatement>,
}

impl From<&AnnotatedProgram> for Program {
    fn from(ae: &AnnotatedProgram) -> Self {
        Program { statements: ae.statements.iter().map(|e| e.into()).collect() }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum AnnotatedStatement {
    Block(Vec<AnnotatedStatement>, ErrorInfo),
    IfElse {
        cond: AnnotatedExpression,
        if_stmt: Box<AnnotatedStatement>,
        else_stmt: Option<Box<AnnotatedStatement>>,
        error_info: ErrorInfo,
    },
    Variable(String, AnnotatedExpression, ErrorInfo),
    Print(AnnotatedExpression, ErrorInfo),
    Expression(AnnotatedExpression),
}

impl From<&AnnotatedStatement> for Statement {
    fn from(ae: &AnnotatedStatement) -> Self {
        match ae {
            AnnotatedStatement::Block(ss, _) =>
                Statement::Block(ss.into_iter().map(|e| e.into()).collect()),
            AnnotatedStatement::IfElse { cond, if_stmt, else_stmt, .. } =>
                Statement::IfElse {
                    cond: cond.into(),
                    if_stmt: Box::new(if_stmt.deref().into()),
                    else_stmt: else_stmt.as_ref().map(|e| Box::new(e.deref().into())),
                },
            AnnotatedStatement::Variable(n, e, _) => Statement::Variable(n.clone(), e.into()),
            AnnotatedStatement::Expression(e) => Statement::Expression(e.into()),
            AnnotatedStatement::Print(p, _) => Statement::Print(p.into()),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum AnnotatedExpression {
    Atomic(Atom, ErrorInfo),
    Grouping(Box<AnnotatedExpression>, ErrorInfo),
    Assign(String, Box<AnnotatedExpression>, ErrorInfo),
    Unary(UnaryOperator, Box<AnnotatedExpression>, ErrorInfo),
    Binary(BinaryOperator, Box<AnnotatedExpression>, Box<AnnotatedExpression>, ErrorInfo),
    Ternary(Box<AnnotatedExpression>, Box<AnnotatedExpression>, Box<AnnotatedExpression>, ErrorInfo),
}

impl AnnotatedExpression {
    pub fn error_info(&self) -> ErrorInfo {
      *(match self {
          AnnotatedExpression::Atomic(_, i) => i,
          AnnotatedExpression::Grouping(_, i) => i,
          AnnotatedExpression::Assign(_, _, i) => i,
          AnnotatedExpression::Unary(_, _, i) => i,
          AnnotatedExpression::Binary(_, _, _, i) => i,
          AnnotatedExpression::Ternary(_, _, _, i) => i,
      })
    }
}

impl From<&AnnotatedExpression> for Expression {
    fn from(ae: &AnnotatedExpression) -> Self {
        match ae {
            AnnotatedExpression::Atomic(e, _) => Expression::Atomic(e.to_owned()),
            AnnotatedExpression::Grouping(e, _) =>
                Expression::Grouping(Box::new(e.as_ref().into())),
            AnnotatedExpression::Assign(n, e, _) =>
                Expression::Assign(n.to_owned(), Box::new(e.as_ref().into())),
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
        }
    }
}
