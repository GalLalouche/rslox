use std::collections::{HashMap, LinkedList};

use nonempty::NonEmpty;

use crate::rslox::common::error::{convert_errors, ErrorInfo, LoxError, LoxResult};
use crate::rslox::interpreted::annotated_ast::{AnnotatedExpression, AnnotatedFunctionDef, AnnotatedProgram, AnnotatedStatement};
use crate::rslox::interpreted::ast::{Atom, ScopeJumps};

pub fn resolve(ae: AnnotatedProgram) -> LoxResult<AnnotatedProgram> {
    convert_errors(resolve_go(ae))
}

fn resolve_go(ae: AnnotatedProgram) -> Result<AnnotatedProgram, NonEmpty<ResolverError>> {
    let mut resolver = Resolver::new();
    let mut errors = Vec::new();
    let length = ae.statements.len();
    let result: Vec<_> = ae.statements
        .into_iter()
        .filter_map(|e| resolver.resolve_stmt(e).map_err(|e| errors.push(e)).ok())
        .collect();
    if errors.is_empty() {
        assert_eq!(result.len(), length);
        Ok(AnnotatedProgram { statements: result })
    } else {
        Err(NonEmpty::flatten(NonEmpty::from_vec(errors).unwrap()))
    }
}

#[derive(Debug, PartialEq, Clone, Eq)]
enum ResolverError {
    Unresolved(String, ErrorInfo),
    SelfReference(String, ErrorInfo),
    InvalidReturn(ErrorInfo),
}

impl LoxError for ResolverError {
    fn get_info(&self) -> ErrorInfo {
        match self {
            ResolverError::Unresolved(_, i) => *i,
            ResolverError::SelfReference(_, i) => *i,
            ResolverError::InvalidReturn(i) => *i,
        }
    }
    fn get_message(&self) -> String {
        match self {
            ResolverError::Unresolved(name, _) => format!("Unresolved {}", name),
            ResolverError::SelfReference(name, _) => format!("Self reference {}", name),
            ResolverError::InvalidReturn(_) => "Invalid return".to_owned(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum CurrentFunction {
    Function,
    Method,
}

struct Resolver {
    scopes: LinkedList<HashMap<String, bool>>,
    function_scope: LinkedList<CurrentFunction>,
}

impl Resolver {
    pub fn new() -> Self {
        let mut result = Resolver {
            scopes: LinkedList::new(),
            function_scope: LinkedList::new(),
        };
        result.enter_scope(); // Global scope
        result.declare("clock");
        result.define("clock");
        result
    }

    pub fn resolve_stmt(
        &mut self,
        stmt: AnnotatedStatement,
    ) -> Result<AnnotatedStatement, NonEmpty<ResolverError>> {
        match stmt {
            AnnotatedStatement::Block(stmts, i) => {
                self.enter_scope();
                let mut result = Vec::new();
                for s in stmts {
                    self.resolve_stmt(s).map(|s| result.push(s))?;
                }
                self.exit_scope();
                Ok(AnnotatedStatement::Block(result, i))
            }
            AnnotatedStatement::IfElse { cond, if_stmt, else_stmt, error_info } => {
                let cond_ = self.resolve_expr(cond)?;
                let if_ = self.resolve_stmt(*if_stmt)?;
                let else_ = match else_stmt {
                    None => Ok(None),
                    Some(e) => self.resolve_stmt(*e).map(|e| Some(Box::new(e))),
                }?;
                Ok(AnnotatedStatement::IfElse {
                    cond: cond_,
                    if_stmt: Box::new(if_),
                    else_stmt: else_,
                    error_info,
                })
            }
            AnnotatedStatement::While(cond, body, i) => {
                let cond_ = self.resolve_expr(cond)?;
                let body_ = self.resolve_stmt(*body)?;
                Ok(AnnotatedStatement::While(cond_, Box::new(body_), i))
            }
            AnnotatedStatement::Variable(name, expr, i) => {
                self.declare(name.as_ref());
                let expr_ = self.resolve_expr(expr)?;
                self.define(name.as_ref());
                Ok(AnnotatedStatement::Variable(name.into(), expr_, i))
            }
            AnnotatedStatement::Class(name, funcs, i) => {
                self.declare(name.as_ref());
                self.define(name.as_ref());
                Ok(AnnotatedStatement::Class(name, funcs, i))
            }
            AnnotatedStatement::Function(AnnotatedFunctionDef { name, params, body, error_info }) => {
                self.function_scope.push_front(CurrentFunction::Function);
                self.declare(name.as_ref());
                self.define(name.as_ref());
                self.enter_scope();
                for p in &params {
                    self.declare(p.as_ref());
                    self.define(p.as_ref());
                }
                let mut result = Vec::new();
                for s in body {
                    self.resolve_stmt(s).map(|s| result.push(s))?;
                }
                self.exit_scope();
                self.function_scope.pop_front();
                Ok(AnnotatedStatement::Function(AnnotatedFunctionDef {
                    name,
                    params,
                    body: result,
                    error_info,
                }))
            }
            AnnotatedStatement::Print(expr, i) => {
                let expr_ = self.resolve_expr(expr)?;
                Ok(AnnotatedStatement::Print(expr_, i))
            }
            AnnotatedStatement::Return(expr, i) => {
                if self.function_scope.is_empty() {
                    Err(NonEmpty::new(ResolverError::InvalidReturn(i)))
                } else {
                    match expr {
                        None => Ok(AnnotatedStatement::Return(None, i)),
                        Some(e) => {
                            let e_ = self.resolve_expr(e)?;
                            Ok(AnnotatedStatement::Return(Some(e_), i))
                        }
                    }
                }
            }
            AnnotatedStatement::Expression(e) => {
                let e_ = self.resolve_expr(e)?;
                Ok(AnnotatedStatement::Expression(e_))
            }
        }
    }

    fn resolve_expr(
        &mut self,
        expr: AnnotatedExpression,
    ) -> Result<AnnotatedExpression, NonEmpty<ResolverError>> {
        match expr {
            AnnotatedExpression::Atomic(Atom::Identifier(name), i) => {
                self.count_jumps(name.as_ref(), &i)
                    .map(|j| {
                        AnnotatedExpression::ResolvedIdentifier(name, j, i)
                    }).map_err(|e| NonEmpty::new(e))
            }
            e @ AnnotatedExpression::Atomic(_, _) => Ok(e.clone()),
            AnnotatedExpression::ResolvedIdentifier(..) => panic!("This should not have happened"),
            AnnotatedExpression::ResolvedAssignment(..) => panic!("This should not have happened"),
            AnnotatedExpression::Grouping(mut e, i) => {
                // TODO macro?
                *e = self.resolve_expr(*e)?;
                Ok(AnnotatedExpression::Grouping(e, i))
            }
            AnnotatedExpression::Property(mut expr, name, i) => {
                *expr = self.resolve_expr(*expr)?;
                Ok(AnnotatedExpression::Property(expr, name, i))
            }
            AnnotatedExpression::FunctionCall(mut callee, args, i) => {
                *callee = self.resolve_expr(*callee)?;
                let mut args_ = Vec::new();
                for arg in args {
                    self.resolve_expr(arg).map(|e| args_.push(e))?;
                }
                Ok(AnnotatedExpression::FunctionCall(callee, args_, i))
            }
            AnnotatedExpression::Assign(name, mut expr, i) => {
                *expr = self.resolve_expr(*expr)?;
                self.count_jumps(&name, &i)
                    .map(|j| AnnotatedExpression::ResolvedAssignment(name, j, expr, i))
                    .map_err(|e| NonEmpty::new(e))
            }
            AnnotatedExpression::Set(mut g, name, mut expr, i) => {
                *expr = self.resolve_expr(*expr)?;
                *g = self.resolve_expr(*g)?;
                Ok(AnnotatedExpression::Set(g, name, expr, i))
            }
            AnnotatedExpression::Unary(op, mut expr, i) => {
                *expr = self.resolve_expr(*expr)?;
                Ok(AnnotatedExpression::Unary(op, expr, i))
            }
            AnnotatedExpression::Binary(op, mut e1, mut e2, i) => {
                *e1 = self.resolve_expr(*e1)?;
                *e2 = self.resolve_expr(*e2)?;
                Ok(AnnotatedExpression::Binary(op, e1, e2, i))
            }
            AnnotatedExpression::Ternary(mut cond, mut e1, mut e2, i) => {
                *cond = self.resolve_expr(*cond)?;
                *e1 = self.resolve_expr(*e1)?;
                *e2 = self.resolve_expr(*e2)?;
                Ok(AnnotatedExpression::Ternary(cond, e1, e2, i))
            }
        }
    }

    fn enter_scope(&mut self) {
        self.scopes.push_front(HashMap::new())
    }

    fn exit_scope(&mut self) {
        self.scopes.pop_front();
    }

    fn declare(&mut self, name: &str) {
        self.scopes.front_mut().unwrap().insert(name.to_owned(), false);
    }

    fn define(&mut self, name: &str) {
        self.scopes.front_mut().unwrap().insert(name.to_owned(), true).unwrap();
    }

    fn count_jumps(&self, name: &str, i: &ErrorInfo) -> Result<ScopeJumps, ResolverError> {
        let mut x = 0;
        for s in &self.scopes {
            match s.get(name) {
                None => x += 1,
                Some(true) => return Ok(x),
                Some(false) => return Err(ResolverError::SelfReference(name.to_owned(), *i))
            }
        }
        return Err(ResolverError::Unresolved(name.to_owned(), *i));
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Borrow;

    use crate::rslox::interpreted::ast::{Expression, FunctionDef, Program, Statement};
    use crate::rslox::interpreted::resolve::ResolverError::{InvalidReturn, Unresolved};
    use crate::rslox::interpreted::tests::{unsafe_parse, unsafe_resolve};

    use super::*;

    fn resolve_(program: Vec<&str>) -> Program {
        unsafe_resolve(program).borrow().into()
    }

    #[test]
    fn simple_test() {
        let p = resolve_(vec![
            r#"var a = "outer";"#,
            "{",
            r#"var a = "inner";"#,
            r#"print a;"#,
            r#"}  "#,
        ]);
        assert_eq!(
            p,
            Program::new(
                vec![
                    Statement::variable("a", Expression::string("outer")),
                    Statement::Block(vec![
                        Statement::variable("a", Expression::string("inner")),
                        Statement::Print(Expression::resolved_identifier("a", 0)),
                    ]),
                ]
            )
        )
    }

    #[test]
    fn book_test() {
        let p = resolve_(vec![
            r#"var a = "global";"#,
            "{",
            "  fun showA() {",
            "    print a;",
            "  }",
            "  showA();",
            r#"var a = "block";"#,
            "  showA();",
            "}",
        ]);
        assert_eq!(
            p,
            Program::new(
                vec![
                    Statement::variable("a", Expression::string("global")),
                    Statement::Block(vec![
                        Statement::Function(FunctionDef {
                            name: "showA".into(),
                            params: Vec::new(),
                            body: vec![Statement::Print(Expression::resolved_identifier("a", 2))],
                        }),
                        Statement::Expression(Expression::FunctionCall(
                            Box::new(Expression::resolved_identifier("showA", 0)),
                            Vec::new(),
                        )),
                        Statement::variable("a", Expression::string("block")),
                        Statement::Expression(Expression::FunctionCall(
                            Box::new(Expression::resolved_identifier("showA", 0)),
                            Vec::new(),
                        )),
                    ]),
                ]
            )
        )
    }

    fn error_line(program: Vec<&str>) -> ResolverError {
        let ast = unsafe_parse(program);
        resolve_go(ast).unwrap_err().head
    }

    #[test]
    fn invalid_reference() {
        assert_eq!(
            Unresolved("a".into(), ErrorInfo { line: 1 }),
            error_line(vec![
                "print a;",
                "var a = 5;",
            ]))
    }

    #[test]
    fn return_outside_of_function_is_an_error() {
        assert_eq!(
            InvalidReturn(ErrorInfo { line: 2 }),
            error_line(vec![
                "var a = 5;",
                "return a;",
            ]))
    }
}