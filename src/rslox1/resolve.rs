use std::collections::{HashMap, LinkedList};
use std::ops::Deref;

use nonempty::NonEmpty;

use crate::rslox1::annotated_ast::{AnnotatedExpression, AnnotatedProgram, AnnotatedStatement};
use crate::rslox1::ast::{Atom, ScopeJumps};
use crate::rslox1::common::{convert_errors, ErrorInfo, LoxError, LoxResult};

pub fn resolve(ae: &AnnotatedProgram) -> LoxResult<AnnotatedProgram> {
    convert_errors(resolve_go(ae))
}

fn resolve_go(ae: &AnnotatedProgram) -> Result<AnnotatedProgram, NonEmpty<ResolverError>> {
    let mut resolver = Resolver::new();
    let mut errors = Vec::new();
    let result: Vec<_> = ae.statements
        .iter()
        .filter_map(|e| resolver.resolve_stmt(e).map_err(|e| errors.push(e)).ok())
        .collect();
    if errors.is_empty() {
        assert_eq!(result.len(), ae.statements.len());
        Ok(AnnotatedProgram { statements: result })
    } else {
        Err(NonEmpty::flatten(NonEmpty::from_vec(errors).unwrap()))
    }
}

#[derive(Debug, PartialEq, Clone, Eq)]
enum ResolverError {
    Unresolved(String, ErrorInfo),
    SelfReference(String, ErrorInfo),
}

impl LoxError for ResolverError {
    fn get_info(&self) -> ErrorInfo {
        match self {
            ResolverError::Unresolved(_, i) => *i,
            ResolverError::SelfReference(_, i) => *i,
        }
    }
    fn get_message(&self) -> String {
        match self {
            ResolverError::Unresolved(name, _) => format!("Unresolved {}", name),
            ResolverError::SelfReference(name, _) => format!("Self reference {}", name),
        }
    }
}

struct Resolver {
    scopes: LinkedList<HashMap<String, bool>>,
}

impl Resolver {
    pub fn new() -> Self {
        let mut result = Resolver { scopes: LinkedList::new() };
        result.enter_scope(); // Global scope
        result.declare("clock");
        result.define("clock");
        result
    }

    pub fn resolve_stmt(
        &mut self,
        stmt: &AnnotatedStatement,
    ) -> Result<AnnotatedStatement, NonEmpty<ResolverError>> {
        match stmt {
            AnnotatedStatement::Block(stmts, i) => {
                self.enter_scope();
                let mut result = Vec::new();
                for s in stmts {
                    self.resolve_stmt(s).map(|s| result.push(s))?;
                }
                self.exit_scope();
                Ok(AnnotatedStatement::Block(result, *i))
            }
            AnnotatedStatement::IfElse { cond, if_stmt, else_stmt, error_info } => {
                let cond_ = self.resolve_expr(cond)?;
                let if_ = self.resolve_stmt(if_stmt)?;
                let else_ = match else_stmt {
                    None => Ok(None),
                    Some(e) =>
                        self.resolve_stmt(e.deref()).map(|e| Some(Box::new(e))),
                }?;
                Ok(AnnotatedStatement::IfElse {
                    cond: cond_,
                    if_stmt: Box::new(if_),
                    else_stmt: else_,
                    error_info: *error_info,
                })
            }
            AnnotatedStatement::While(cond, body, i) => {
                let cond_ = self.resolve_expr(cond)?;
                let body_ = self.resolve_stmt(body)?;
                Ok(AnnotatedStatement::While(cond_, Box::new(body_), *i))
            }
            AnnotatedStatement::Variable(name, expr, i) => {
                self.declare(name);
                let expr_ = self.resolve_expr(expr)?;
                self.define(name);
                Ok(AnnotatedStatement::Variable(name.into(), expr_, *i))
            }
            AnnotatedStatement::Function { name, params, body, error_info } => {
                self.declare(name);
                self.define(name);
                self.enter_scope();
                for p in params {
                    self.declare(p);
                    self.define(p);
                }
                let mut result = Vec::new();
                for s in body {
                    self.resolve_stmt(s).map(|s| result.push(s))?;
                }
                self.exit_scope();
                Ok(AnnotatedStatement::Function {
                    name: name.to_owned(),
                    params: params.to_owned(),
                    body: result,
                    error_info: *error_info,
                })
            }
            AnnotatedStatement::Print(expr, i) => {
                let expr_ = self.resolve_expr(expr)?;
                Ok(AnnotatedStatement::Print(expr_, *i))
            }
            AnnotatedStatement::Return(expr, i) => {
                match expr {
                    None => Ok(AnnotatedStatement::Return(None, *i)),
                    Some(e) => {
                        let e_ = self.resolve_expr(e)?;
                        Ok(AnnotatedStatement::Return(Some(e_), *i))
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
        expr: &AnnotatedExpression,
    ) -> Result<AnnotatedExpression, NonEmpty<ResolverError>> {
        match expr {
            AnnotatedExpression::Atomic(Atom::Identifier(name), i) => {
                self.count_jumps(name, i)
                    .map(|j| {
                        AnnotatedExpression::ResolvedIdentifier(name.to_owned(), j, *i)
                    }).map_err(|e| NonEmpty::new(e))
            }
            e @ AnnotatedExpression::Atomic(_, _) => Ok(e.clone()),
            AnnotatedExpression::ResolvedIdentifier(..) => panic!("This should not have happened"),
            AnnotatedExpression::ResolvedAssignment(..) => panic!("This should not have happened"),
            AnnotatedExpression::Grouping(e, i) => {
                let e_ = self.resolve_expr(e)?;
                Ok(AnnotatedExpression::Grouping(Box::new(e_), *i))
            }
            AnnotatedExpression::FunctionCall(callee, args, i) => {
                let callee_ = self.resolve_expr(callee)?;
                let mut args_ = Vec::new();
                for arg in args {
                    self.resolve_expr(arg).map(|e| args_.push(e))?;
                }
                Ok(AnnotatedExpression::FunctionCall(Box::new(callee_), args_, *i))
            }
            AnnotatedExpression::Assign(name, expr, i) => {
                let expr_ = self.resolve_expr(expr)?;
                self.count_jumps(name, i)
                    .map(|j| {
                        AnnotatedExpression::ResolvedAssignment(
                            name.to_owned(), j, Box::new(expr_), *i)
                    }).map_err(|e| NonEmpty::new(e))
            }
            AnnotatedExpression::Unary(op, expr, i) => {
                let expr_ = self.resolve_expr(expr)?;
                Ok(AnnotatedExpression::Unary(*op, Box::new(expr_), *i))
            }
            AnnotatedExpression::Binary(op, e1, e2, i) => {
                let e1_ = self.resolve_expr(e1)?;
                let e2_ = self.resolve_expr(e2)?;
                Ok(AnnotatedExpression::Binary(*op, Box::new(e1_), Box::new(e2_), *i))
            }
            AnnotatedExpression::Ternary(cond, e1, e2, i) => {
                let cond_ = self.resolve_expr(cond)?;
                let e1_ = self.resolve_expr(e1)?;
                let e2_ = self.resolve_expr(e2)?;
                Ok(AnnotatedExpression::Ternary(Box::new(cond_), Box::new(e1_), Box::new(e2_), *i))
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

    use crate::rslox1::ast::{Expression, Program, Statement};
    use crate::rslox1::resolve::ResolverError::Unresolved;
    use crate::rslox1::unsafe_test::{unsafe_parse, unsafe_resolve};

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
                        Statement::Function {
                            name: "showA".into(),
                            params: Vec::new(),
                            body: vec![Statement::Print(Expression::resolved_identifier("a", 2))],
                        },
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
        resolve_go(&ast).unwrap_err().head
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
}