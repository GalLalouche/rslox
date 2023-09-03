use std::convert::TryFrom;
use std::ops::Deref;

use crate::rslox::common::utils::{RcRc, rcrc};
use crate::rslox::compiled::chunk::{Chunk, InternedString};
use crate::rslox::compiled::gc::{GcWeak, GcWeakMut};
use crate::rslox::compiled::tests::DeepEq;

#[derive(Debug, Clone)]
pub enum Value {
    Number(f64),
    Bool(bool),
    Nil,
    String(InternedString),
    Closure(GcWeak<Function>, RcRc<Vec<GcWeakMut<Value>>>),
    UpvaluePtr(GcWeakMut<Value>),
    OpenUpvalue(RcRc<Value>),
}


#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub name: InternedString,
    pub arity: usize,
    pub chunk: Chunk,
}

impl Function {
    pub fn stringify(&self) -> String { format!("<fn {}>", self.name.to_owned()) }
}

impl DeepEq for Function {
    fn deep_eq(&self, other: &Self) -> bool {
        self.name.to_owned() == other.name.to_owned()
            && self.arity == other.arity
            && self.chunk.deep_eq(&other.chunk)
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
            Value::Closure(..) => true,
            _ => false,
        }
    }
    pub fn set(&mut self, value: Value) {
        match self {
            Value::UpvaluePtr(ref mut v) => *v.unwrap_upgrade().borrow_mut() = value,
            Value::OpenUpvalue(ref mut v) => *v.borrow_mut() = value,
            _ => *self = value,
        }
    }

    pub fn stringify(&self) -> String {
        match self {
            Value::Number(f) => f.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Nil => "nil".to_owned(),
            Value::String(s) => s.unwrap_upgrade().to_string(),
            Value::Closure(f, _) => f.unwrap_upgrade().stringify(),
            Value::UpvaluePtr(value) => value.unwrap_upgrade().borrow().stringify(),
            Value::OpenUpvalue(value) => value.borrow().stringify(),
        }
    }

    // If self is already an open value, returns a weak wrapped rcrc. Otherwise, converts self to a
    // managed OpenValue, and returns the new weak managed rcrc.
    pub fn as_open_upvalue(&mut self) -> GcWeakMut<Value> {
        match self.deref() {
            Value::OpenUpvalue(v) => return v.into(),
            Value::UpvaluePtr(_) => panic!("UpvaluePtr should not be made into an open upvalue (I think?)"),
            _ => ()
        }
        let old = std::mem::replace(self, Value::Nil);
        let managed = rcrc(old);
        *self = Value::OpenUpvalue(managed.clone());
        (&managed).into()
    }

    pub fn pp_debug(&self) -> String {
        match self {
            Value::UpvaluePtr(v) => format!("upv: {}", v.unwrap_upgrade().borrow().pp_debug()),
            Value::OpenUpvalue(v) => format!("opv: {}", v.borrow().pp_debug()),
            e => e.stringify(),
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
    pub fn is_upvalue_ptr(&self) -> bool {
        match self {
            Value::UpvaluePtr(_) => true,
            _ => false,
        }
    }
    pub fn upvalue_ptr(value: GcWeakMut<Value>) -> Self {
        assert!(!value.unwrap_upgrade().borrow().is_upvalue_ptr());
        Value::UpvaluePtr(value)
    }
}

impl TryFrom<&Value> for f64 {
    type Error = String;

    fn try_from(value: &Value) -> Result<Self, Self::Error> {
        match &value {
            Value::Number(f) => Ok(*f),
            Value::UpvaluePtr(v) => Self::try_from(v.unwrap_upgrade().borrow().deref()),
            Value::OpenUpvalue(v) => Self::try_from(v.borrow().deref()),
            e => Err(format!("Expected Value::Number, but found {:?}", e)),
        }
    }
}

impl TryFrom<&Value> for (GcWeak<Function>, GcWeakMut<Vec<GcWeakMut<Value>>>) {
    type Error = String;

    fn try_from(value: &Value) -> Result<Self, Self::Error> {
        match &value {
            Value::Closure(f, uv) => Ok((f.clone(), uv.into())),
            e => Err(format!("Expected Value::Closure, but found {:?}", e)),
        }
    }
}

impl<'a> TryFrom<&'a mut Value> for &'a mut bool {
    type Error = String;

    fn try_from(value: &'a mut Value) -> Result<Self, Self::Error> {
        match value {
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
