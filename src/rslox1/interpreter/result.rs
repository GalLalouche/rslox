use crate::rslox1::ast::{BinaryOperator, UnaryOperator};
use crate::rslox1::common::{ErrorInfo, LoxError};
use crate::rslox1::interpreter::lox_value::LoxValue;
use crate::rslox1::interpreter::result::InterpreterErrorOrControlFlow::{ArityError, NilReference, Returned, TypeError, UnrecognizedIdentifier};

#[derive(Debug, PartialEq, Clone)]
pub enum InterpreterErrorOrControlFlow {
    UnrecognizedIdentifier(String, ErrorInfo),
    ArityError { expected: usize, actual: usize, error_info: ErrorInfo },
    TypeError(String, ErrorInfo),
    NilReference(ErrorInfo),

    // Not actual errors
    Returned(LoxValue, ErrorInfo),
}

impl LoxError for InterpreterErrorOrControlFlow {
    fn get_info(&self) -> ErrorInfo {
        match self {
            UnrecognizedIdentifier(_, i) => *i,
            TypeError(_, i) => *i,
            NilReference(i) => *i,
            ArityError { error_info, .. } => *error_info,
            Returned(_, i) => *i,
        }
    }

    fn get_message(&self) -> String {
        match self {
            ArityError { actual, expected, .. } =>
                format!("Incorrect callable arity: expected '{}', but got '{}'", expected, actual),
            UnrecognizedIdentifier(m, _) => format!("Unrecognized identifier: {}", m),
            TypeError(m, _) => format!("Type error: {}", m),
            NilReference(_) => "Nil reference".to_owned(),
            Returned(..) => "Return outside of function".to_owned(),
        }
    }
}

pub type InterpretResult<A> = Result<A, InterpreterErrorOrControlFlow>;

pub fn unary_type_error<A>(
    op: &UnaryOperator, v: &LoxValue, error_info: &ErrorInfo,
) -> InterpretResult<A> {
    Err(TypeError(format!("Cannot apply operator '{:?}' to '{:?}'", op, v), *error_info))
}

pub fn binary_type_error<A>(
    op: &BinaryOperator, v1: &LoxValue, v2: &LoxValue, error_info: &ErrorInfo,
) -> InterpretResult<A> {
    Err(TypeError(
        format!("Cannot apply operator '{:?}' to '{:?}' and '{:?}'", op, v1, v2), *error_info))
}
