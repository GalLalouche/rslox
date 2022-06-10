use std::{fmt, io};
use std::collections::HashMap;
use std::io::Write;
use nonempty::NonEmpty;

use crate::rslox1::annotated_ast::{AnnotatedExpression, AnnotatedProgram, AnnotatedStatement};
use crate::rslox1::ast::{Atom, BinaryOperator, UnaryOperator};
use crate::rslox1::common::{convert_error, convert_errors, ErrorInfo, LoxError, LoxResult};
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

pub fn interpret(program: &AnnotatedProgram) -> LoxResult<()> {
    convert_error(interpret_go(&program, &mut io::stdout()))
}

fn interpret_go(program: &AnnotatedProgram, writer: &mut impl Write) -> InterpretResult<()> {
    let mut symbols: HashMap<String, LoxValue> = HashMap::new();
    for statement in &program.statements {
        interpret_statement(&mut symbols, &statement, writer)?;
    }
    Ok(())
}

fn interpret_statement(
    symbols: &mut HashMap<String, LoxValue>,
    statement: &AnnotatedStatement,
    writer: &mut impl Write,
) -> InterpretResult<()> {
    match statement {
        AnnotatedStatement::Variable(name, e, _) => {
            let expr = interpret_expr(symbols, e)?;
            symbols.insert(name.to_owned(), expr);
            Ok(())
        }
        AnnotatedStatement::Expression(e) => interpret_expr(symbols, e).map(|_| ()),
        AnnotatedStatement::Print(e, _) => {
            let expr = interpret_expr(symbols, e)?;
            write!(writer, "{}", match expr {
                Number(n) => n.to_string(),
                LoxValue::String(s) => s,
                Bool(b) => b.to_string(),
                Nil => "nil".to_string(),
            }).expect("Not written");
            Ok(())
        }
    }
}

// Changes from lox:
// * Screw truthiness. Only Bools are truthy.
// * String comparisons using >, <, >=, <=.
fn interpret_expr(
    symbols: &mut HashMap<String, LoxValue>,
    expression: &AnnotatedExpression,
) -> InterpretResult<LoxValue> {
    match expression {
        AnnotatedExpression::Atomic(l, i) => match l {
            Atom::Identifier(name) =>
                symbols
                    .get(name)
                    .cloned()
                    .ok_or(UnrecognizedIdentifier(name.to_owned(), *i)),
            Atom::Number(n) => Ok(Number(n.to_owned())),
            Atom::String(s) => Ok(LoxValue::String(s.to_owned())),
            Atom::True => Ok(Bool(true)),
            Atom::False => Ok(Bool(false)),
            Atom::Nil => Ok(Nil),
        },
        AnnotatedExpression::Grouping(e, _) => interpret_expr(symbols, e),
        AnnotatedExpression::Unary(op, e, i) => match op {
            UnaryOperator::Minus => {
                let x = interpret_expr(symbols, e)?;
                match x {
                    Nil => Err(NilReference(*i)),
                    Number(n) => Ok(Number(n)),
                    e => unary_type_error(op, &e, i),
                }
            }
            UnaryOperator::Bang => {
                let x = interpret_expr(symbols, e)?;
                match x {
                    Nil => Err(NilReference(*i)),
                    Bool(b) => Ok(Bool(!b)),
                    e => unary_type_error(op, &e, i),
                }
            }
        }
        AnnotatedExpression::Binary(op, e1, e2, i) => {
            let x1 = interpret_expr(symbols, e1)?;
            let x2 = interpret_expr(symbols, e2)?;
            match op {
                BinaryOperator::Comma => Ok(x2),
                BinaryOperator::Minus => match (&x1, &x2) {
                    (Number(n1), Number(n2)) => Ok(Number(n1 - n2)),
                    _ => binary_type_error(op, &x1, &x2, i),
                }
                BinaryOperator::Plus => match (&x1, &x2) {
                    (Number(n1), Number(n2)) => Ok(Number(n1 + n2)),
                    (LoxValue::String(s1), LoxValue::String(s2)) =>
                        Ok(LoxValue::String(format!("{}{}", s1, s2))),
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

                BinaryOperator::BangEqual => equalequal(&x1, &x2).map(|e| match e {
                    Bool(b) => Bool(!b),
                    _ => panic!("equalequal should always return a bool"),
                }),
                BinaryOperator::EqualEqual => equalequal(&x1, &x2),
                BinaryOperator::Greater
                | BinaryOperator::GreaterEqual
                | BinaryOperator::Less
                | BinaryOperator::LessEqual => binary_comparison(op, &x1, &x2, i),
                // TODO lazy circuit
                BinaryOperator::And => match (&x1, &x2) {
                    (Nil, _) => Err(NilReference(*i)),
                    (_, Nil) => Err(NilReference(*i)),
                    (Bool(b1), Bool(b2)) => Ok(Bool(*b1 && *b2)),
                    _ => binary_type_error(op, &x1, &x2, i)
                }
                // TODO lazy circuit
                BinaryOperator::Or => match (&x1, &x2) {
                    (Nil, _) => Err(NilReference(*i)),
                    (_, Nil) => Err(NilReference(*i)),
                    (Bool(b1), Bool(b2)) => Ok(Bool(*b1 || *b2)),
                    _ => binary_type_error(op, &x1, &x2, i)
                }
            }
        }
        AnnotatedExpression::Ternary(cond, e1, e2, i) => {
            let i_cond = interpret_expr(symbols, cond)?;
            match i_cond {
                Nil => Err(NilReference(*i)),
                Bool(b) => if b { interpret_expr(symbols, e1) } else { interpret_expr(symbols, e2) }
                _ => Err(TypeError(
                    format!("Cannot apply ternary operator to non-Bool cond '{:?}'", i_cond), *i)),
            }
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

fn equalequal(v1: &LoxValue, v2: &LoxValue) -> InterpretResult<LoxValue> {
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

    #[test]
    fn simple_program() {
        let ast = parse(&tokenize("var x = 1;\nvar y = x + 1;\nprint y + 4;").unwrap()).unwrap();
        let mut buff = Cursor::new(Vec::new());
        interpret_go(&ast, &mut buff).unwrap();

        let string: String = buff.get_ref().into_iter().map(|i| *i as char).collect();
        assert_eq!(string, "6");
    }
}