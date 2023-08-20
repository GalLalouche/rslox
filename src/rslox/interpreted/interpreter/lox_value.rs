use std::collections::HashMap;
use std::fmt::Debug;

use crate::rslox::common::utils::{RcRc, rcrc};
use crate::rslox::interpreted::annotated_ast::AnnotatedStatement;
use crate::rslox::interpreted::interpreter::environment::Environment;
use crate::rslox::interpreted::interpreter::lox_value::LoxValue::{Bool, Callable, Class, Instance, Native, Nil, Number};
use crate::rslox::interpreted::interpreter::result::InterpreterErrorOrControlFlow;

#[derive(Debug, Clone)]
pub struct LoxFunction {
    pub arity: usize,
    pub params: Vec<String>,
    pub body: Vec<AnnotatedStatement>,
}

#[derive(Debug, Clone)]
pub struct LoxClass {
    pub name: String,
    pub closure: Closure,
    pub funcs: HashMap<String, RcRc<LoxFunction>>,
}

type Closure = RcRc<Environment>;
pub type LoxRef = RcRc<LoxValue>;

#[derive(Debug, Clone)]
pub struct LoxInstance {
    fields: HashMap<String, LoxRef>,
    class: RcRc<LoxClass>,
}

impl LoxInstance {
    pub fn new(class: RcRc<LoxClass>) -> Self {
        LoxInstance { fields: HashMap::new(), class }
    }
    pub fn set_field(&mut self, name: String, value: LoxRef) {
        self.fields.insert(name, value);
    }
    pub fn get(&self, name: &str) -> Option<LoxRef> {
        self.fields.get(name).cloned().or_else(|| self.class.borrow().funcs.get(name).map(|f| rcrc(Callable {
            closure: self.class.borrow().closure.clone(),
            func: f.borrow().clone(),
        })))
    }
}

#[derive(Debug, Clone)]
pub enum LoxValue {
    // User-defined functions may depend on the environment, so we can have their implementation
    // here without drowning in lifetime parameters shenanigans. So instead, we just keep the
    // statements here.
    Callable {
        closure: Closure,
        func: LoxFunction,
    },
    // Native functions can be defined using basic Rust closures, since by definition they don't
    // need to rely on Environment. Of course, they can't be defined using plain Lox statements since
    // if they could, we wouldn't them to define them as native, now would we?
    Native {
        name: &'static str,
        arity: usize,
        func: fn(Vec<LoxRef>) -> Result<LoxRef, InterpreterErrorOrControlFlow>,
    },
    Class(RcRc<LoxClass>),
    Instance {
        instance: LoxInstance,
    },
    Number(f64),
    String(String),
    Bool(bool),
    Nil,
}

impl LoxValue {
    pub fn callable(
        arity: usize,
        params: Vec<String>,
        body: Vec<AnnotatedStatement>,
        closure: Closure,
    ) -> Self { Callable { func: LoxFunction { arity, params, body }, closure } }

    pub fn instance(
        class: RcRc<LoxClass>,
    ) -> Self { Instance { instance: LoxInstance::new(class) } }

    pub fn type_name(&self) -> &'static str {
        match self {
            Native { .. } => "Native",
            Callable { .. } => "Callable",
            Number(_) => "Number",
            LoxValue::String(_) => "String",
            Bool(_) => "Bool",
            Nil => "Nil",
            Class { .. } => "Class",
            Instance { .. } => "Instance",
        }
    }

    pub fn stringify(&self) -> String {
        match self {
            Native { name, .. } => name.to_owned().into(),
            Callable { func: LoxFunction { arity, .. }, .. } => format!("Callable ({})", arity),
            Number(n) => n.to_string(),
            LoxValue::String(s) => s.replace("\\n", "\n").replace("\\t", "\t").replace("\\\\", "\\"),
            Bool(b) => b.to_string(),
            Nil => "nil".to_owned(),
            Class(cls) => cls.borrow().name.to_owned(),
            Instance { instance } => format!("{} instance", instance.class.borrow().name),
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
            (Callable { .. }, _) => todo!(),
            (Native { .. }, _) => todo!(),
            (Number(n1), Number(n2)) => Bool(n1.eq(&n2)),
            (LoxValue::String(s1), LoxValue::String(s2)) => Bool(s1 == s2),
            (Bool(b1), Bool(b2)) => Bool(b1 == b2),
            (Nil, Nil) => Bool(true),
            _ => Bool(false),
        }
    }

    pub fn set(&mut self, name: &str, value: &LoxRef) -> Result<LoxValue, String> {
        if let Instance { instance } = self {
            instance.set_field(name.to_owned(), value.clone());
            Ok(Nil)
        } else {
            Err(format!("Cannot set field on non-instance type {:?}", self))
        }
    }
}
