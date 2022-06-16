use crate::rslox1::annotated_ast::AnnotatedStatement;
use crate::rslox1::interpreter::lox_value::LoxValue::{Bool, Callable, Native, Number, Nil};
use crate::rslox1::interpreter::result::InterpreterErrorOrControlFlow;

#[derive(Debug, PartialEq, Clone)]
pub enum LoxValue {
    // User-defined functions may depend on the environment, so we can have their implementation
    // here without drowning in lifetime parameters shenanigans. So instead, we just keep the
    // statements here.
    Callable { arity: usize, params: Vec<String>, body: Vec<AnnotatedStatement> },
    // Native functions can be defined using basic closures, since by definition they don't need to
    // rely on Environment. Of course, they can't be defined using plain Lox statements since if
    // they could, we wouldn't them to define them as native, now would we?
    Native {
        name: &'static str,
        arity: usize,
        func: fn(Vec<LoxValue>) -> Result<LoxValue, InterpreterErrorOrControlFlow>,
    },
    Number(f64),
    String(String),
    Bool(bool),
    Nil,
}

impl LoxValue {
    pub fn callable(arity: usize, params: Vec<String>, body: Vec<AnnotatedStatement>) -> Self {
        Callable { arity, params, body }
    }
    pub fn type_name(&self) -> &'static str {
        match self {
            Native { .. } => "Native",
            Callable { .. } => "Callable",
            Number(_) => "Number",
            LoxValue::String(_) => "String",
            Bool(_) => "Bool",
            Nil => "Nil",
        }
    }

    pub fn stringify(&self) -> String {
        match self {
            Native { name, .. } => name.clone().into(),
            Callable { arity, .. } => format!("Callable ({})", arity),
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
            _ => true,
        }
    }

    pub fn equal_equal(&self, other: &LoxValue) -> LoxValue {
        match (self, other) {
            (Callable {..}, _) => todo!(),
            (Native {..}, _) => todo!(),
            (Number(n1), Number(n2)) => Bool(n1.eq(&n2)),
            (LoxValue::String(s1), LoxValue::String(s2)) => Bool(s1 == s2),
            (Bool(b1), Bool(b2)) => Bool(b1 == b2),
            (Nil, Nil) => Bool(true),
            _ => Bool(false),
        }
    }
}
