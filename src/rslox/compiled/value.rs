use std::borrow::BorrowMut;
use std::collections::HashSet;
use std::convert::TryFrom;
use std::ops::Deref;

use crate::rslox::compiled::chunk::{Chunk, InternedString};
use crate::rslox::compiled::gc::GcWeak;
use crate::rslox::compiled::op_code::StackLocation;
use crate::rslox::compiled::tests::DeepEq;

#[derive(Debug, Clone)]
pub enum Value {
    Number(f64),
    Bool(bool),
    Nil,
    String(InternedString),
    Closure(GcWeak<Function>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub name: InternedString,
    pub arity: usize,
    pub chunk: Chunk,
    pub upvalues: HashSet<UpValue>,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub struct UpValue {
    pub index: StackLocation,
    pub is_local: bool,
}

impl Function {
    pub fn stringify(&self) -> String { format!("<fn {}>", self.name.to_owned()) }
}

impl DeepEq for Function {
    fn deep_eq(&self, other: &Self) -> bool {
        self.name.to_owned() == other.name.to_owned() && self.arity == other.arity &&
            self.chunk.deep_eq(&other.chunk)
    }
}

impl PartialEq<Self> for Value {
    fn eq(&self, other: &Self) -> bool {
        match (&self, &other) {
            (Value::Number(n1), Value::Number(n2)) => n1 == n2,
            (Value::Bool(b1), Value::Bool(b2)) => b1 == b2,
            (Value::Nil, Value::Nil) => true,
            (Value::String(s1), Value::String(s2)) => s1 == s2,
            _ => false,
        }
    }
}

impl Value {
    pub fn is_string(&self) -> bool {
        match &self {
            Value::String(_) => true,
            _ => false,
        }
    }
    pub fn is_function(&self) -> bool {
        match &self {
            Value::Closure(_) => true,
            _ => false,
        }
    }

    pub fn stringify(&self) -> String {
        match self {
            Value::Number(f) => f.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Nil => "nil".to_owned(),
            Value::String(s) => s.unwrap_upgrade().to_string(),
            Value::Closure(f) => f.unwrap_upgrade().stringify(),
        }
    }
    pub fn is_truthy(&self) -> bool {
        !self.is_falsey()
    }
    pub fn is_falsey(&self) -> bool {
        match &self {
            Value::Nil => true,
            Value::Bool(false) => true,
            _ => false,
        }
    }
}

impl<'a> TryFrom<&'a Value> for &'a f64 {
    type Error = String;

    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match &value {
            Value::Number(f) => Ok(&f),
            e => Err(format!("Expected Value::Number, but found {:?}", e)),
        }
    }
}

impl<'a> TryFrom<&'a mut Value> for &'a mut f64 {
    type Error = String;

    fn try_from(value: &'a mut Value) -> Result<Self, Self::Error> {
        match value.borrow_mut() {
            Value::Number(f) => Ok(f),
            e => Err(format!("Expected Value::Number, but found {:?}", e)),
        }
    }
}

impl<'a> TryFrom<&'a mut Value> for &'a mut bool {
    type Error = String;

    fn try_from(value: &'a mut Value) -> Result<Self, Self::Error> {
        match value.borrow_mut() {
            Value::Bool(b) => Ok(b),
            e => Err(format!("Expected Value::Bool, but found {:?}", e)),
        }
    }
}

impl<'a> TryFrom<&'a Value> for &'a bool {
    type Error = String;

    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match &value {
            Value::Bool(b) => Ok(&b),
            e => Err(format!("Expected Value::Bool, but found {:?}", e)),
        }
    }
}

impl<'a> TryFrom<&'a Value> for InternedString {
    type Error = String;

    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match &value {
            Value::String(s) => Ok(s.clone()),
            e => Err(format!("Expected Value::String, but found {:?}", e)),
        }
    }
}

impl InternedString {
    pub fn to_owned(&self) -> String { self.unwrap_upgrade().deref().clone() }
}