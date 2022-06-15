use std::{io, mem};
use std::collections::HashMap;
use std::io::Write;

use crate::rslox1::annotated_ast::{AnnotatedExpression, AnnotatedProgram, AnnotatedStatement};
use crate::rslox1::ast::{Atom, BinaryOperator, UnaryOperator};
use crate::rslox1::common::{convert_error, ErrorInfo, LoxError, LoxResult};
use crate::rslox1::interpreter::InterpreterError::{NilReference, TypeError, UnrecognizedIdentifier};
use crate::rslox1::interpreter::LoxValue::{Bool, Nil, Number};

#[derive(Debug, PartialEq, Clone)]
pub enum LoxValue {
    Number(f64),
    String(String),
    Bool(bool),
    Nil,
}


impl LoxValue {
    pub fn type_name(&self) -> &'static str {
        match self {
            Number(_) => "Number",
            LoxValue::String(_) => "String",
            Bool(_) => "Bool",
            Nil => "Nil",
        }
    }

    pub fn stringify(&self) -> String {
        match self {
            Number(n) => n.to_string(),
            LoxValue::String(s) => s.replace("\\n", "\n").replace("\\t", "\t").replace("\\\\", "\\"),
            Bool(b) => b.to_string(),
            Nil => "nil".to_string(),
        }
    }

    pub fn truthiness(&self) -> bool {
        match self {
            Number(n) => *n != 0.0,
            LoxValue::String(s) => !s.is_empty(),
            Bool(b) => *b,
            Nil => false,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
enum InterpreterError {
    UnrecognizedIdentifier(String, ErrorInfo),
    TypeError(String, ErrorInfo),
    NilReference(ErrorInfo),
}

impl LoxError for InterpreterError {
    fn get_info(&self) -> ErrorInfo {
        match self {
            UnrecognizedIdentifier(_, i) => *i,
            TypeError(_, i) => *i,
            NilReference(i) => *i,
        }
    }

    fn get_message(&self) -> String {
        match self {
            UnrecognizedIdentifier(m, _) => format!("Unrecognized identifier: {}", m),
            TypeError(m, _) => format!("Type error: {}", m),
            NilReference(_) => "Nil reference".to_owned(),
        }
    }
}

type InterpretResult<A> = Result<A, InterpreterError>;

pub fn interpret(program: &AnnotatedProgram) -> LoxResult<Option<LoxValue>> {
    convert_error(interpret_go(&program, &mut io::stdout()))
}

struct Environment {
    parent: Option<Box<Environment>>,
    values: HashMap<String, LoxValue>,
}

impl Environment {
    pub fn new() -> Self { Environment { parent: None, values: HashMap::new() } }
    fn nest(&mut self) {
        let parent = Some(Box::new(Environment {
            parent: mem::take(&mut self.parent),
            values: mem::take(&mut self.values),
        }));
        self.parent = parent
    }
    fn unnest(&mut self) {
        match self.parent.as_deref_mut() {
            None => panic!("Cannot unnest if parent doesn't exist"),
            Some(p) => {
                self.values = mem::take(&mut p.values);
                self.parent = mem::take(&mut p.parent);
            }
        }
    }
    pub fn get(&self, key: &str) -> Option<&LoxValue> {
        self.values.get(key).or_else(|| self.parent.as_deref().and_then(|p| p.get(key)))
    }
    pub fn define(&mut self, key: String, value: LoxValue) {
        self.values.insert(key, value);
    }
    pub fn assign(&mut self, key: String, value: LoxValue) -> bool {
        if self.values.contains_key(&key) {
            self.values.insert(key, value);
            true
        } else {
            self.parent.as_deref_mut().map(|p| p.assign(key, value)).unwrap_or(false)
        }
    }
}

fn interpret_go(
    program: &AnnotatedProgram,
    writer: &mut impl Write,
) -> InterpretResult<Option<LoxValue>> {
    let mut environment = Environment::new();
    let mut final_expr: Option<LoxValue> = None;
    for statement in &program.statements {
        final_expr = interpret_statement(&mut environment, &statement, writer)?;
    }
    Ok(final_expr)
}

fn interpret_statement(
    environment: &mut Environment,
    statement: &AnnotatedStatement,
    writer: &mut impl Write,
) -> InterpretResult<Option<LoxValue>> {
    match statement {
        AnnotatedStatement::Variable(name, e, _) => {
            let expr = interpret_expr(environment, e)?;
            environment.define(name.to_owned(), expr);
            Ok(None)
        }
        AnnotatedStatement::IfElse { cond, if_stmt, else_stmt, .. } => {
            let cond_value = interpret_expr(environment, cond)?;
            if cond_value.truthiness() {
                interpret_statement(environment, if_stmt, writer)
            } else if let Some(s) = else_stmt {
                interpret_statement(environment, s, writer)
            } else {
                Ok(None)
            }
        }
        AnnotatedStatement::Block(ss, _) => {
            environment.nest();
            let mut final_expr = None;
            for s in ss {
                final_expr = interpret_statement(environment, s, writer)?;
            }
            environment.unnest();
            Ok(final_expr)
        }
        AnnotatedStatement::Expression(e) => interpret_expr(environment, e).map(|e| Some(e)),
        AnnotatedStatement::Print(e, _) => {
            let expr = interpret_expr(environment, e)?;
            write!(writer, "{}", expr.stringify()).expect("Not written");
            Ok(None)
        }
    }
}

// Changes from lox:
// * Screw truthiness. Only Bools are truthy. But not for OR and AND, so this is probably a bug :\
// * String comparisons using >, <, >=, <=.
fn interpret_expr(
    environment: &mut Environment,
    expression: &AnnotatedExpression,
) -> InterpretResult<LoxValue> {
    match expression {
        AnnotatedExpression::Atomic(l, i) => match l {
            Atom::Identifier(name) =>
                environment
                    .get(name)
                    .cloned()
                    .ok_or(UnrecognizedIdentifier(name.to_owned(), *i)),
            Atom::Number(n) => Ok(Number(n.to_owned())),
            Atom::String(s) => Ok(LoxValue::String(s.to_owned())),
            Atom::True => Ok(Bool(true)),
            Atom::False => Ok(Bool(false)),
            Atom::Nil => Ok(Nil),
        },
        AnnotatedExpression::Grouping(e, _) => interpret_expr(environment, e),
        AnnotatedExpression::Assign(name, expr, i) => {
            let value = interpret_expr(environment, expr)?;
            if environment.assign(name.to_owned(), value.to_owned()) {
                Ok(value)
            } else {
                Err(UnrecognizedIdentifier(name.to_owned(), i.to_owned()))
            }
        }
        AnnotatedExpression::Unary(op, e, i) => match op {
            UnaryOperator::Minus => {
                let x = interpret_expr(environment, e)?;
                match x {
                    Nil => Err(NilReference(*i)),
                    Number(n) => Ok(Number(n)),
                    e => unary_type_error(op, &e, i),
                }
            }
            UnaryOperator::Bang => {
                interpret_expr(environment, e).map(|e| Bool(!e.truthiness()))
            }
        }
        AnnotatedExpression::Binary(op, e1, e2, i) => {
            match op {
                BinaryOperator::And => {
                    let x1 = interpret_expr(environment, e1)?;
                    return if !x1.truthiness() {
                        Ok(x1)
                    } else {
                        interpret_expr(environment, e2)
                    };
                }
                // TODO lazy circuit
                BinaryOperator::Or => {
                    let x1 = interpret_expr(environment, e1)?;
                    return if x1.truthiness() {
                        Ok(x1)
                    } else {
                        interpret_expr(environment, e2)
                    };
                }
                _ => ()
            }
            let x1 = interpret_expr(environment, e1)?;
            let x2 = interpret_expr(environment, e2)?;
            match op {
                BinaryOperator::Comma => Ok(x2),
                BinaryOperator::Minus => match (&x1, &x2) {
                    (Number(n1), Number(n2)) => Ok(Number(n1 - n2)),
                    _ => binary_type_error(op, &x1, &x2, i),
                }
                BinaryOperator::Plus => match (&x1, &x2) {
                    (Number(n1), Number(n2)) => Ok(Number(n1 + n2)),
                    (LoxValue::String(s1), e2) =>
                        Ok(LoxValue::String(format!("{}{}", s1, e2.stringify()))),
                    (e1, LoxValue::String(s2)) =>
                        Ok(LoxValue::String(format!("{}{}", e1.stringify(), s2))),
                    _ => binary_type_error(op, &x1, &x2, i),
                }
                BinaryOperator::Mult => match (&x1, &x2) {
                    (Number(n1), Number(n2)) => Ok(Number(n1 * n2)),
                    _ => binary_type_error(op, &x1, &x2, i),
                }
                BinaryOperator::Div => match (&x1, &x2) {
                    (Number(n1), Number(n2)) => Ok(Number(n1 / n2)),
                    _ => binary_type_error(op, &x1, &x2, i),
                }

                BinaryOperator::BangEqual => equal_equal(&x1, &x2).map(|e| match e {
                    Bool(b) => Bool(!b),
                    _ => panic!("equal_equal should always return a bool"),
                }),
                BinaryOperator::EqualEqual => equal_equal(&x1, &x2),
                BinaryOperator::Greater
                | BinaryOperator::GreaterEqual
                | BinaryOperator::Less
                | BinaryOperator::LessEqual => binary_comparison(op, &x1, &x2, i),
                BinaryOperator::And => panic!("Should have already been handled"),
                BinaryOperator::Or => panic!("Should have already been handled"),
            }
        }
        AnnotatedExpression::Ternary(cond, e1, e2, _) => {
            let i_cond = interpret_expr(environment, cond)?;
            interpret_expr(environment, if i_cond.truthiness() { e1 } else { e2 })
        }
    }
}

fn binary_comparison(
    op: &BinaryOperator, v1: &LoxValue, v2: &LoxValue, error_info: &ErrorInfo,
) -> InterpretResult<LoxValue> {
    match (v1, v2) {
        (Nil, _) => Err(NilReference(*error_info)),
        (_, Nil) => Err(NilReference(*error_info)),
        (Number(n1), Number(n2)) => match op {
            BinaryOperator::Greater => Ok(Bool(n1 > n2)),
            BinaryOperator::GreaterEqual => Ok(Bool(n1 >= n2)),
            BinaryOperator::Less => Ok(Bool(n1 < n2)),
            BinaryOperator::LessEqual => Ok(Bool(n1 <= n2)),
            _ => panic!("Unexpected op {:?}", op),
        },
        (LoxValue::String(s1), LoxValue::String(s2)) => match op {
            BinaryOperator::Greater => Ok(Bool(s1 > s2)),
            BinaryOperator::GreaterEqual => Ok(Bool(s1 >= s2)),
            BinaryOperator::Less => Ok(Bool(s1 < s2)),
            BinaryOperator::LessEqual => Ok(Bool(s1 <= s2)),
            _ => panic!("Unexpected op {:?}", op),
        },
        _ => binary_type_error(&op, &v1, &v2, error_info),
    }
}

fn unary_type_error<A>(
    op: &UnaryOperator, v: &LoxValue, error_info: &ErrorInfo,
) -> InterpretResult<A> {
    Err(TypeError(format!("Cannot apply operator '{:?}' to '{:?}'", op, v), *error_info))
}

fn binary_type_error<A>(
    op: &BinaryOperator, v1: &LoxValue, v2: &LoxValue, error_info: &ErrorInfo,
) -> InterpretResult<A> {
    Err(TypeError(
        format!("Cannot apply operator '{:?}' to '{:?}' and '{:?}'", op, v1, v2), *error_info))
}

fn equal_equal(v1: &LoxValue, v2: &LoxValue) -> InterpretResult<LoxValue> {
    match (v1, v2) {
        (Number(n1), Number(n2)) => Ok(Bool(n1.eq(&n2))),
        (LoxValue::String(s1), LoxValue::String(s2)) => Ok(Bool(s1 == s2)),
        (Bool(b1), Bool(b2)) => Ok(Bool(b1 == b2)),
        (Nil, Nil) => Ok(Bool(true)),
        _ => Ok(Bool(false)),
    }
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use crate::rslox1::lexer::tokenize;
    use crate::rslox1::parser::parse;

    use super::*;

    fn printed_string(program: &str) -> String {
        let ast = parse(&tokenize(program).unwrap()).unwrap();
        let mut buff = Cursor::new(Vec::new());
        interpret_go(&ast, &mut buff).unwrap();
        buff.get_ref().into_iter().map(|i| *i as char).collect()
    }

    fn error_line(program: &str) -> usize {
        let ast = parse(&tokenize(program).unwrap()).unwrap();
        let mut buff = Cursor::new(Vec::new());
        interpret_go(&ast, &mut buff).unwrap_err().get_info().line
    }

    #[test]
    fn simple_program() {
        assert_eq!(printed_string("var x = 1;\nvar y = x + 1;\nprint y + 4;"), "6");
    }

    #[test]
    fn printing_assignments() {
        assert_eq!(printed_string("var x;\nprint x = 2;"), "2");
    }

    #[test]
    fn invalid_reference() {
        assert_eq!(error_line("print a;\nvar a = 5;"), 1)
    }

    #[test]
    fn string_concat() {
        assert_eq!(
            printed_string(
                "var x = 1;\nvar y = \"2\"; var z =3;\nprint x + y + z + \"\\n\" + 4 + \"hi\";"),
            "123\n4hi",
        )
    }

    #[test]
    fn if_else_stmt() {
        assert_eq!(printed_string(r#"if (1 > 2) "foo" / 3; else print 2;"#), "2")
    }

    #[test]
    fn and_short_circuit() {
        assert_eq!(printed_string(r#"print "hi" and 2;"#), "2");
        assert_eq!(printed_string(r#"print nil and 2;"#), "nil");
    }

    #[test]
    fn or_short_circuit() {
        assert_eq!(printed_string(r#"print "hi" or 2;"#), "hi");
        assert_eq!(printed_string(r#"print nil or 2;"#), "2");
    }
}