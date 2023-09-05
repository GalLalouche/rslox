use std::convert::{TryFrom, TryInto};

use crate::rslox::common::utils::{RcRc, rcrc};
use crate::rslox::compiled::chunk::{Chunk, InternedString};
use crate::rslox::compiled::gc::{GcWeak, GcWeakMut};
use crate::rslox::compiled::op_code::StackLocation;
use crate::rslox::compiled::tests::DeepEq;

#[derive(Debug, Clone)]
pub enum Value {
    Number(f64),
    Bool(bool),
    Nil,
    String(InternedString),
    Closure(GcWeak<Function>, Upvalues),
    UpvaluePtr(GcWeakMut<PointedUpvalue>),
}

#[derive(Debug, Clone)]
pub enum PointedUpvalue {
    Open(StackLocation, GcWeakMut<Vec<Value>>),
    Closed(GcWeakMut<Value>),
}

#[derive(Debug, Clone)]
pub struct Upvalues {
    upvalues: RcRc<Vec<GcWeakMut<PointedUpvalue>>>,
}

impl Upvalues {
    pub fn new(upvalues: Vec<GcWeakMut<PointedUpvalue>>) -> Self {
        Upvalues { upvalues: rcrc(upvalues) }
    }

    pub fn get(&self, index: StackLocation) -> GcWeakMut<PointedUpvalue> {
        self.upvalues.borrow()[index].clone()
    }

    // The &mut self is here to protected against modifications, since we do modify the internal
    // upvalue.
    pub fn set(&mut self, index: StackLocation, value: Value) {
        self.upvalues.borrow()[index].unwrap_upgrade().borrow_mut().set(value)
    }
}

impl PointedUpvalue {
    pub fn set(&mut self, value: Value) {
        assert!(!value.is_upvalue_ptr());
        match self {
            PointedUpvalue::Open(i, s) => s.unwrap_upgrade().borrow_mut()[*i] = value,
            PointedUpvalue::Closed(_) => todo!(),
        }
    }

    fn stringify(&self) -> String {
        match self {
            PointedUpvalue::Open(i, s) => s.unwrap_upgrade().borrow()[*i].stringify(),
            PointedUpvalue::Closed(_) => todo!(),
        }
    }

    fn pp_debug(&self) -> String { todo!() }

    fn try_into_aux<A, F: FnOnce(&Value) -> Result<A, String>>(&self, f: F) -> Result<A, String> {
        match self {
            PointedUpvalue::Open(i, s) => {
                f(s.unwrap_upgrade().borrow().get(*i).unwrap())
            }
            PointedUpvalue::Closed(_) => todo!(),
        }
    }
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
            Value::UpvaluePtr(ref mut v) => v.unwrap_upgrade().borrow_mut().set(value),
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
        }
    }

    pub fn pp_debug(&self) -> String {
        match self {
            Value::UpvaluePtr(v) => format!("upv: {}", v.unwrap_upgrade().borrow().pp_debug()),
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
}

impl TryFrom<&Value> for f64 {
    type Error = String;

    fn try_from(value: &Value) -> Result<Self, Self::Error> {
        match &value {
            Value::Number(f) => Ok(*f),
            Value::UpvaluePtr(v) => v.unwrap_upgrade().borrow().try_into_aux(|e| e.try_into()),
            e => Err(format!("Expected Value::Number, but found {:?}", e)),
        }
    }
}

// TODO The closures really shouldn't be mut... perhaps wrap in a struct?
impl<'a> TryFrom<&'a Value> for (GcWeak<Function>, Upvalues) {
    type Error = String;

    fn try_from(value: &Value) -> Result<Self, Self::Error> {
        match &value {
            Value::Closure(f, uv) => Ok((f.clone(), uv.clone())),
            Value::UpvaluePtr(v) => v.unwrap_upgrade().borrow().try_into_aux(|e| e.try_into()),
            e => Err(format!("Expected Value::Closure, but found {:?}", e)),
        }
    }
}

impl<'a> TryFrom<&'a Value> for bool {
    type Error = String;

    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match &value {
            Value::Bool(b) => Ok(*b),
            Value::UpvaluePtr(v) => v.unwrap_upgrade().borrow().try_into_aux(|e| e.try_into()),
            e => Err(format!("Expected Value::Bool, but found {:?}", e)),
        }
    }
}

impl<'a> TryFrom<&'a Value> for InternedString {
    type Error = String;

    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match &value {
            Value::String(s) => Ok(s.clone()),
            Value::UpvaluePtr(v) => v.unwrap_upgrade().borrow().try_into_aux(|e| e.try_into()),
            e => Err(format!("Expected Value::String, but found {:?}", e)),
        }
    }
}

impl InternedString {
    pub fn to_owned(&self) -> String {
        use std::ops::Deref;
        self.unwrap_upgrade().deref().clone()
    }
}
