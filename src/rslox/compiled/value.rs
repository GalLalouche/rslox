use std::convert::{TryFrom, TryInto};
use std::ops::Deref;

use crate::rslox::common::utils::{RcRc, rcrc};
use crate::rslox::compiled::chunk::Chunk;
use crate::rslox::compiled::op_code::StackLocation;
use crate::rslox::compiled::tests::DeepEq;
use crate::rslox::compiled::weak::{GcWeak, GcWeakMut};

use super::op_code::InternedString;

/// Note that Value implements a *shallow* clone. This follows the semantics of lox, since primitive
/// values ([Value::Bool] and [Value::Number], basically) have value semantics, and other types,
/// be they [Value::String], [Value::UpvaluePtr], or heap pointers (e.g., for closure or class
/// instances), follow reference semantics.
///
/// Note that other than the above mentioned primitives,
/// [Value] doesn't own its data! Strings are owned either by individual function chunks, or by the
/// VM for temporary strings. Closed over upvalues, i.e., upvalues whose reference is no longer on
/// the stack in managed by the VM as well. Classes are not implemented yet.
#[derive(Debug, Clone)]
pub enum Value {
    Number(f64),
    Bool(bool),
    Nil,
    TemporaryPlaceholder,
    String(InternedString),
    Closure(GcWeak<Function>, Upvalues),
    UpvaluePtr(GcWeakMut<PointedUpvalue>),
}

impl Value {
    pub fn is_string(&self) -> bool {
        match &self {
            Value::String(_) => true,
            Value::UpvaluePtr(v) => v.unwrap_upgrade().borrow().apply(|v| v.is_string()),
            _ => false,
        }
    }

    pub fn set(&mut self, value: Value) {
        assert_ne!(value, Value::TemporaryPlaceholder);
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
            Value::UpvaluePtr(value) => value.unwrap_upgrade().borrow().apply(|e| e.stringify()),
            Value::TemporaryPlaceholder => panic!("TemporaryPlaceholder found!")
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
            Value::TemporaryPlaceholder => panic!("TemporaryPlaceholder found!"),
            Value::Nil => true,
            Value::Bool(false) => true,
            Value::UpvaluePtr(v) => v.unwrap_upgrade().borrow().apply(|v| v.is_falsey()),
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

impl TryFrom<&Value> for f64 {
    type Error = String;

    fn try_from(value: &Value) -> Result<Self, Self::Error> {
        match &value {
            Value::Number(f) => Ok(*f),
            Value::UpvaluePtr(v) => v.unwrap_upgrade().borrow().apply(|e| e.try_into()),
            e => Err(format!("Expected Value::Number, but found {:?}", e)),
        }
    }
}

impl<'a> TryFrom<&'a Value> for (GcWeak<Function>, Upvalues) {
    type Error = String;

    fn try_from(value: &Value) -> Result<Self, Self::Error> {
        match &value {
            Value::Closure(f, uv) => Ok((f.clone(), uv.clone())),
            Value::UpvaluePtr(v) => v.unwrap_upgrade().borrow().apply(|e| e.try_into()),
            e => Err(format!("Expected Value::Closure, but found {:?}", e)),
        }
    }
}

impl<'a> TryFrom<&'a Value> for bool {
    type Error = String;

    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match &value {
            Value::Bool(b) => Ok(*b),
            Value::UpvaluePtr(v) => v.unwrap_upgrade().borrow().apply(|e| e.try_into()),
            e => Err(format!("Expected Value::Bool, but found {:?}", e)),
        }
    }
}

impl<'a> TryFrom<&'a Value> for InternedString {
    type Error = String;

    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match &value {
            Value::String(s) => Ok(s.clone()),
            Value::UpvaluePtr(v) => v.unwrap_upgrade().borrow().apply(|e| e.try_into()),
            e => Err(format!("Expected Value::String, but found {:?}", e)),
        }
    }
}

impl InternedString {
    pub fn to_owned(&self) -> String { self.unwrap_upgrade().deref().clone() }
}

/// Like [Value], [PointedUpvalue] also performs shallow cloning. Since these are literally
/// pointers ([PointedUpvalue::Open] is a stack pointers, and [PointedUpvalue::Closed] points to
/// the heap), this makes sense. Notable, [PointedUpvalue::Closed] is the only place in this code
/// base that actually *owns* its values! This will probably changed when classes are implemented.
///
/// This struct is not very type safe, but since we want to change open upvalues to closed upvalues
/// Without anyone knowing about it, this is the way to do it. In effect, this is an ad-hoc linear
/// type, moving from open to closed.
#[derive(Debug, Clone)]
pub enum PointedUpvalue {
    Open(StackLocation, GcWeakMut<Vec<Value>>),
    Closed(RcRc<Value>),
}

impl PointedUpvalue {
    pub fn close(&mut self) {
        match self {
            PointedUpvalue::Open(i, v) => {
                assert!(!v.unwrap_upgrade().borrow().is_empty());
                let value = std::mem::replace(
                    &mut v.unwrap_upgrade().borrow_mut()[*i], Value::TemporaryPlaceholder);
                *self = PointedUpvalue::Closed(rcrc(value));
            }
            PointedUpvalue::Closed(_) => panic!("Can't close a closed value!")
        }
    }
}

impl PointedUpvalue {
    pub fn set(&mut self, value: Value) {
        assert!(!value.is_upvalue_ptr());
        match self {
            PointedUpvalue::Open(i, s) => s.unwrap_upgrade().borrow_mut()[*i] = value,
            PointedUpvalue::Closed(v) => v.borrow_mut().set(value),
        }
    }

    pub fn pp_debug(&self) -> String {
        match self {
            PointedUpvalue::Open(i, _) => format!("open{}", i).to_owned(),
            PointedUpvalue::Closed(_) => "closed".to_owned(),
        }
    }

    fn apply<B, F: FnOnce(&Value) -> B>(&self, f: F) -> B {
        match self {
            PointedUpvalue::Open(i, s) => f(s.unwrap_upgrade().borrow().get(*i).unwrap()),
            PointedUpvalue::Closed(v) => f(v.borrow().deref()),
        }
    }
}

/// A compiled function, as opposed to a [Value::Closure] which is a specific runtime value,
/// including its, well, closure.
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

/// Since closures, i.e., function values, follow reference semantics (i.e., one can assign the same
/// closure to multiple values), this clone is also shallow. Of course, closures also share data,
/// so this is mandatory:
/// ```
/// fun foo(x) {
///   fun bar() {
///     x = x + 1;
///     print x;
///   }
///   f = bar;
///   g = bar;
/// }
/// foo(42);
/// f();
/// g();
/// ```
/// In the above example, both f and g refer to the same underlying x, and so both modify it.
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
