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

fn interpret_go(program: &AnnotatedProgram, writer: &mut impl Write) -> InterpretResult<()> {
    let mut environment = Environment::new();
    for statement in &program.statements {
        interpret_statement(&mut environment, &statement, writer)?;
    }
    Ok(())
}

fn interpret_statement(
    environment: &mut Environment,
    statement: &AnnotatedStatement,
    writer: &mut impl Write,
) -> InterpretResult<()> {
    match statement {
        AnnotatedStatement::Variable(name, e, _) => {
            let expr = interpret_expr(environment, e)?;
            environment.define(name.to_owned(), expr);
            Ok(())
        }
        AnnotatedStatement::Block(ss, _) => {
            environment.nest();
            for s in ss {
                interpret_statement(environment, s, writer)?;
            }
            environment.unnest();
            Ok(())
        }
        AnnotatedStatement::Expression(e) => interpret_expr(environment, e).map(|_| ()),
        AnnotatedStatement::Print(e, _) => {
            let expr = interpret_expr(environment, e)?;
            write!(writer, "{}", expr.stringify()).expect("Not written");
            Ok(())
        }
    }
}

// Changes from lox:
// * Screw truthiness. Only Bools are truthy.
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
                let x = interpret_expr(environment, e)?;
                match x {
                    Nil => Err(NilReference(*i)),
                    Bool(b) => Ok(Bool(!b)),
                    e => unary_type_error(op, &e, i),
                }
            }
        }
        AnnotatedExpression::Binary(op, e1, e2, i) => {
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
            let i_cond = interpret_expr(environment, cond)?;
            match i_cond {
                Nil => Err(NilReference(*i)),
                Bool(b) =>
                    if b { interpret_expr(environment, e1) } else { interpret_expr(environment, e2) },
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

    #[test]
    fn simple_program() {
        let ast = parse(&tokenize("var x = 1;\nvar y = x + 1;\nprint y + 4;").unwrap()).unwrap();
        let mut buff = Cursor::new(Vec::new());
        interpret_go(&ast, &mut buff).unwrap();

        let string: String = buff.get_ref().into_iter().map(|i| *i as char).collect();
        assert_eq!(string, "6");
    }

    #[test]
    fn printing_assignments() {
        let ast = parse(&tokenize("var x;\nprint x = 2;").unwrap()).unwrap();
        let mut buff = Cursor::new(Vec::new());
        interpret_go(&ast, &mut buff).unwrap();

        let string: String = buff.get_ref().into_iter().map(|i| *i as char).collect();
        assert_eq!(string, "2");
    }

    #[test]
    fn invalid_reference() {
        let ast = parse(&tokenize("print a;\nvar a = 5;").unwrap()).unwrap();
        let mut buff = Cursor::new(Vec::new());
        assert_eq!(
            interpret_go(&ast, &mut buff).unwrap_err().get_info().line,
            1,
        )
    }

    #[test]
    fn string_concat() {
        let ast = parse(&tokenize("var x = 1;\nvar y = \"2\"; var z =3;\nprint x + y + z + \"\\n\" + 4 + \"hi\";").unwrap()).unwrap();
        let mut buff = Cursor::new(Vec::new());
        interpret_go(&ast, &mut buff).unwrap();
        let string: String = buff.get_ref().into_iter().map(|i| *i as char).collect();
        assert_eq!(string, "123\n4hi")
    }

    #[test]
    fn blocks() {
        let ast = parse(&tokenize("var x = 1;\nvar y = 2; var z;\n{var y = 3;\nz = x + y;\n}\nprint x + y + z;").unwrap()).unwrap();
        let mut buff = Cursor::new(Vec::new());
        interpret_go(&ast, &mut buff).unwrap();
        let string: String = buff.get_ref().into_iter().map(|i| *i as char).collect();
        assert_eq!(string, "7")
    }
}