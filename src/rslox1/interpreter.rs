use std::io;
use std::io::Write;

use crate::rslox1::annotated_ast::{AnnotatedExpression, AnnotatedProgram, AnnotatedStatement};
use crate::rslox1::ast::{Atom, BinaryOperator, UnaryOperator};
use crate::rslox1::common::{convert_error, ErrorInfo, LoxResult};
use crate::rslox1::interpreter::environment::Environment;
use crate::rslox1::interpreter::lox_value::LoxValue;
use crate::rslox1::interpreter::LoxValue::{Bool, Callable, Native, Nil, Number};
use crate::rslox1::interpreter::result::{binary_type_error, InterpreterErrorOrControlFlow, InterpretResult, unary_type_error};
use crate::rslox1::interpreter::result::InterpreterErrorOrControlFlow::{ArityError, NilReference, Returned, TypeError, UnrecognizedIdentifier};

pub mod lox_value;
mod result;
mod environment;

pub fn interpret(program: &AnnotatedProgram) -> LoxResult<Option<LoxValue>> {
    convert_error(interpret_go(&program, &mut io::stdout()))
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
            let expr = interpret_expr(environment, e, writer)?;
            environment.define(name.to_owned(), expr);
            Ok(None)
        }
        AnnotatedStatement::Function { name, params, body, .. } => {
            let callable = Callable {
                arity: params.len(),
                params: params.clone(),
                body: body.clone(),
            };
            environment.define(name.to_owned(), callable);
            Ok(None)
        }
        AnnotatedStatement::IfElse { cond, if_stmt, else_stmt, .. } => {
            let cond_value = interpret_expr(environment, cond, writer)?;
            if cond_value.truthiness() {
                interpret_statement(environment, if_stmt, writer)
            } else if let Some(s) = else_stmt {
                interpret_statement(environment, s, writer)
            } else {
                Ok(None)
            }
        }
        AnnotatedStatement::While(cond, stmt, _) => {
            loop {
                let cond_value = interpret_expr(environment, cond, writer).map(|e| e.truthiness())?;
                if !cond_value {
                    break;
                }
                interpret_statement(environment, stmt, writer)?;
            }
            Ok(None)
        }
        AnnotatedStatement::Block(ss, _) => {
            environment.nest();
            let result = try {
                let mut final_expr = None;
                for s in ss {
                    final_expr = interpret_statement(environment, s, writer)?;
                }
                final_expr
            };
            environment.unnest();
            result
        }
        AnnotatedStatement::Expression(e) => interpret_expr(environment, e, writer).map(|e| Some(e)),
        AnnotatedStatement::Return(e, i) => match e {
            None => Err(Returned(Nil, *i)),
            Some(expr) =>
                interpret_expr(environment, expr, writer)
                    .and_then(|result| Err(Returned(result, *i)))
        },
        AnnotatedStatement::Print(e, _) => {
            let expr = interpret_expr(environment, e, writer)?;
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
    writer: &mut impl Write,
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
        AnnotatedExpression::Grouping(e, _) => interpret_expr(environment, e, writer),
        AnnotatedExpression::FunctionCall(f, args, i) => {
            let check_arity = |arity| {
                if arity == args.len() {
                    Ok(())
                } else {
                    Err(ArityError { actual: args.len(), expected: arity, error_info: *i })
                }
            };
            let function = interpret_expr(environment, f, writer)?;
            let arg_values =
                args.into_iter()
                    .map(|e| interpret_expr(environment, e, writer))
                    .collect::<Result<Vec<LoxValue>, InterpreterErrorOrControlFlow>>()?;
            let result = match function {
                Native { arity, func, .. } => {
                    check_arity(arity)?;
                    func(arg_values)
                }
                Callable { arity, params, body } => {
                    check_arity(arity)?;
                    let params_argument = &params;
                    let args = &arg_values;
                    environment.nest();
                    let result = try {
                        for (param_name, arg) in params_argument.into_iter().zip(args) {
                            environment.define(param_name.to_owned(), arg.clone());
                        }
                        for stmt in body {
                            interpret_statement(environment, &stmt, writer)?;
                        }
                        Nil
                    };
                    environment.unnest();
                    match result {
                        Err(Returned(value, _)) => Ok(value),
                        e => e
                    }
                }
                e => Err(TypeError(
                    format!("Cannot invoke uncallable value '{:?}'", e), *i))
            };
            result
        }
        AnnotatedExpression::Assign(name, expr, i) => {
            let value = interpret_expr(environment, expr, writer)?;
            if environment.assign(name.to_owned(), value.to_owned()) {
                Ok(value)
            } else {
                Err(UnrecognizedIdentifier(name.to_owned(), i.to_owned()))
            }
        }
        AnnotatedExpression::Unary(op, e, i) => match op {
            UnaryOperator::Minus => {
                let x = interpret_expr(environment, e, writer)?;
                match x {
                    Nil => Err(NilReference(*i)),
                    Number(n) => Ok(Number(n)),
                    e => unary_type_error(op, &e, i),
                }
            }
            UnaryOperator::Bang => {
                interpret_expr(environment, e, writer).map(|e| Bool(!e.truthiness()))
            }
        }
        AnnotatedExpression::Binary(op, e1, e2, i) => {
            match op {
                BinaryOperator::And => {
                    let x1 = interpret_expr(environment, e1, writer)?;
                    return if !x1.truthiness() {
                        Ok(x1)
                    } else {
                        interpret_expr(environment, e2, writer)
                    };
                }
                BinaryOperator::Or => {
                    let x1 = interpret_expr(environment, e1, writer)?;
                    return if x1.truthiness() {
                        Ok(x1)
                    } else {
                        interpret_expr(environment, e2, writer)
                    };
                }
                _ => ()
            }
            let x1 = interpret_expr(environment, e1, writer)?;
            let x2 = interpret_expr(environment, e2, writer)?;
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

                BinaryOperator::BangEqual => Ok(match x1.equal_equal(&x2) {
                    Bool(b) => Bool(!b),
                    _ => panic!("equal_equal should always return Bool"),
                }),
                BinaryOperator::EqualEqual => Ok(x1.equal_equal(&x2)),
                BinaryOperator::Greater
                | BinaryOperator::GreaterEqual
                | BinaryOperator::Less
                | BinaryOperator::LessEqual => binary_comparison(op, &x1, &x2, i),
                BinaryOperator::And => panic!("Should have already been handled"),
                BinaryOperator::Or => panic!("Should have already been handled"),
            }
        }
        AnnotatedExpression::Ternary(cond, e1, e2, _) => {
            let i_cond = interpret_expr(environment, cond, writer)?;
            interpret_expr(environment, if i_cond.truthiness() { e1 } else { e2 }, writer)
        }
    }
}

//noinspection DuplicatedCode
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

#[cfg(test)]
mod tests {
    use std::io::Cursor;
    use crate::rslox1::common::LoxError;

    use crate::rslox1::lexer::tokenize;
    use crate::rslox1::parser::parse;

    use super::*;

    fn printed_string(program: Vec<&str>) -> String {
        let ast = parse(&tokenize(program.join("\n").as_ref()).unwrap()).unwrap();
        let mut buff = Cursor::new(Vec::new());
        interpret_go(&ast, &mut buff).unwrap();
        buff.get_ref().into_iter().map(|i| *i as char).collect()
    }

    fn error_line(program: Vec<&str>) -> usize {
        let ast = parse(&tokenize(program.join("\n").as_ref()).unwrap()).unwrap();
        let mut buff = Cursor::new(Vec::new());
        interpret_go(&ast, &mut buff).unwrap_err().get_info().line
    }

    #[test]
    fn simple_program() {
        assert_eq!(
            "6",
            printed_string(vec![
                "var x = 1;",
                "var y = x + 1;",
                "print y + 4;",
            ]), )
    }

    #[test]
    fn printing_assignments() {
        assert_eq!(
            "2",
            printed_string(vec![
                "var x;",
                "print x = 2;",
            ]));
    }

    #[test]
    fn invalid_reference() {
        assert_eq!(
            1,
            error_line(vec![
                "print a;",
                "var a = 5;",
            ]))
    }

    #[test]
    fn string_concat() {
        assert_eq!(
            "123\n4hi",
            printed_string(vec![
                "var x = 1;",
                r#"var y = "2";"#,
                "var z = 3;",
                "print x + y + z + \"\\n\" + 4 + \"hi\";",
            ]))
    }

    #[test]
    fn if_else_stmt() {
        assert_eq!(
            "2",
            printed_string(vec![r#"if (1 > 2) "foo" / 3; else print 2;"#]))
    }

    #[test]
    fn and_short_circuit() {
        assert_eq!(printed_string(vec![r#"print "hi" and 2;"#]), "2");
        assert_eq!(printed_string(vec![r#"print nil and 2;"#]), "nil");
    }

    #[test]
    fn or_short_circuit() {
        assert_eq!(printed_string(vec![r#"print "hi" or 2;"#]), "hi");
        assert_eq!(printed_string(vec![r#"print nil or 2;"#]), "2");
    }

    #[test]
    fn while_loop() {
        assert_eq!(
            "10",
            printed_string(vec![
                "var x = 0;",
                "while (x < 10)",
                "x = x + 1;",
                "print x;",
            ]));
    }

    #[test]
    fn for_loop() {
        assert_eq!(
            "10",
            printed_string(vec![
                "var x;",
                "for (var y = 0; y < 10; x = y = y + 1) {}",
                "print x;",
            ]));
    }

    #[test]
    fn native_clock() {
        assert_eq!(
            "true",
            printed_string(vec![
                "var x = clock();",
                "var y = clock();",
                "print x <= y;",
            ]))
    }

    #[test]
    fn basic_function_declaration() {
        assert_eq!(
            "hello world!",
            printed_string(vec![
                "fun test() {",
                r#"print "hello world!";"#,
                "}",
                "test();",
            ]));
    }

    #[test]
    fn returning_function_declaration() {
        assert_eq!(
            "6",
            printed_string(vec![
                "fun one() {",
                "  return 1;",
                "}",
                "fun plus_two(x) {",
                "  return 2+x;",
                "}",
                "print one() + plus_two(3);",
            ]));
    }

    #[test]
    fn fibonacci() {
        assert_eq!(
            "8",
            printed_string(vec![
                "fun fib(n) {",
                "  if (n <= 1) {",
                "    return n;",
                "  }",
                "  return fib(n - 2) + fib(n - 1);",
                "}",
                "print fib(6);",
            ]));
    }
}