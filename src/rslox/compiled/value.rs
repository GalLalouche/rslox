use std::convert::{TryFrom, TryInto};
use std::ops::Deref;
use std::rc::Weak;

use crate::format_interned;
use crate::rslox::common::utils::{RcRc, rcrc, WeakRc};
use crate::rslox::compiled::chunk::Chunk;
use crate::rslox::compiled::memory::{InternedString, Pointer};
use crate::rslox::compiled::op_code::StackLocation;
use crate::rslox::compiled::tests::DeepEq;

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
    // We can use a Weak reference to the function, since it exists in the bytecode and will never
    // be collected.
    Closure(Weak<Function>, Upvalues),
    UpvaluePtr(Pointer<PointedUpvalue>),
}

impl Pointer<PointedUpvalue> {
    fn deep_apply<B, F: FnOnce(&Value) -> B>(&self, f: F) -> B { self.apply(|p| p.apply(f)) }
    fn deep_set(&mut self, new_value: Value) { self.mutate(|p| p.set(new_value)) }
}

impl Value {
    pub fn is_string(&self) -> bool {
        match &self {
            Value::String(_) => true,
            Value::UpvaluePtr(v) => v.deep_apply(|v| v.is_string()),
            _ => false,
        }
    }

    pub fn set(&mut self, value: Value) {
        assert_ne!(value, Value::TemporaryPlaceholder);
        match self {
            Value::UpvaluePtr(ref mut v) => v.deep_set(value),
            _ => *self = value,
        }
    }

    pub fn stringify(&self) -> String {
        match self {
            Value::Number(f) => f.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Nil => "nil".to_owned(),
            Value::String(s) => s.to_owned(),
            Value::Closure(f, _) => f.upgrade().unwrap().stringify(),
            Value::UpvaluePtr(value) => value.deep_apply(|e| e.stringify()),
            Value::TemporaryPlaceholder => panic!("TemporaryPlaceholder found!")
        }
    }

    pub fn pp_debug(&self) -> String {
        match self {
            Value::UpvaluePtr(v) => format!("upv: {}", v.deep_apply(|e| e.pp_debug())),
            e => e.stringify(),
        }
    }

    pub fn is_truthy(&self) -> bool { !self.is_falsey() }
    pub fn is_falsey(&self) -> bool {
        match &self {
            Value::TemporaryPlaceholder => panic!("TemporaryPlaceholder found!"),
            Value::Nil => true,
            Value::Bool(false) => true,
            Value::UpvaluePtr(v) => v.deep_apply(|v| v.is_falsey()),
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
            Value::UpvaluePtr(v) => v.deep_apply(|e| e.try_into()),
            e => Err(format!("Expected Value::Number, but found {:?}", e)),
        }
    }
}

impl<'a> TryFrom<&'a Value> for (Weak<Function>, Upvalues) {
    type Error = String;

    fn try_from(value: &Value) -> Result<Self, Self::Error> {
        match &value {
            Value::Closure(f, uv) => Ok((f.clone(), uv.clone())),
            Value::UpvaluePtr(v) => v.deep_apply(|e| e.try_into()),
            e => Err(format!("Expected Value::Closure, but found {:?}", e)),
        }
    }
}

impl<'a> TryFrom<&'a Value> for bool {
    type Error = String;

    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match &value {
            Value::Bool(b) => Ok(*b),
            Value::UpvaluePtr(v) => v.deep_apply(|e| e.try_into()),
            e => Err(format!("Expected Value::Bool, but found {:?}", e)),
        }
    }
}

impl<'a> TryFrom<&'a Value> for InternedString {
    type Error = String;

    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match &value {
            Value::String(s) => Ok(s.clone()),
            Value::UpvaluePtr(v) => v.deep_apply(|e| e.try_into()),
            e => Err(format!("Expected Value::String, but found {:?}", e)),
        }
    }
}

/// An encapsulating wrapper on top of [PointedUpvalueImpl].
#[derive(Debug, Clone)]
pub struct PointedUpvalue(PointedUpvalueImpl);

pub type IsUsed = bool;
/// Like [Value], [PointedUpvalueImpl] also performs shallow cloning. Since these are literally
/// pointers ([PointedUpvalueImpl::Open] is a stack pointers, and [PointedUpvalueImpl::Closed]
/// points to the heap), this makes sense. Notably, [PointedUpvalueImpl::Closed] is the only place
/// in this code base that actually *owns* its values! This will probably changed when classes are
/// implemented.
///
/// This enum is not very type safe, but since we want to change open upvalues to closed upvalues
/// without anyone knowing about it, this is the way to do it. In effect, this is an ad-hoc linear
/// type, moving from open to closed.
#[derive(Debug, Clone)]
enum PointedUpvalueImpl {
    Open(StackLocation, WeakRc<Vec<Value>>),
    Closed(RcRc<Value>, IsUsed),
}

impl PointedUpvalue {
    pub fn open(index: usize, stack: WeakRc<Vec<Value>>) -> Self {
        PointedUpvalue(PointedUpvalueImpl::Open(index, stack))
    }

    pub fn close(&mut self) {
        match &mut self.0 {
            PointedUpvalueImpl::Open(i, ref mut v) => {
                let value = std::mem::replace(
                    &mut v.upgrade().unwrap().borrow_mut()[*i], Value::TemporaryPlaceholder);
                *self = PointedUpvalue(PointedUpvalueImpl::Closed(rcrc(value), false as IsUsed));
            }
            PointedUpvalueImpl::Closed(..) => panic!("Can't close a closed value!")
        }
    }

    pub fn set(&mut self, value: Value) {
        assert!(!value.is_upvalue_ptr());
        match &mut self.0 {
            PointedUpvalueImpl::Open(i, s) => s.upgrade().unwrap().borrow_mut()[*i] = value,
            PointedUpvalueImpl::Closed(v,..) => v.borrow_mut().set(value),
        }
    }

    pub fn pp_debug(&self) -> String {
        match &self.0 {
            PointedUpvalueImpl::Open(i, _) => format!("open{}", i).to_owned(),
            PointedUpvalueImpl::Closed(..) => "closed".to_owned(),
        }
    }

    pub fn open_location(&self) -> StackLocation {
        match self.0 {
            PointedUpvalueImpl::Open(i, ..) => i,
            PointedUpvalueImpl::Closed(..) => panic!("Closed index has no index location"),
        }
    }

    fn apply<B, F: FnOnce(&Value) -> B>(&self, f: F) -> B {
        match &self.0 {
            PointedUpvalueImpl::Open(i, s) => f(s.upgrade().unwrap().borrow().get(*i).unwrap()),
            PointedUpvalueImpl::Closed(v, ..) => f(v.borrow().deref()),
        }
    }
}

/// A compiled function, as opposed to a [Value::Closure] which is a specific runtime value,
/// including its, well, closure.
#[derive(Debug, PartialEq)]
pub struct Function {
    pub name: InternedString,
    pub arity: usize,
    pub chunk: Chunk,
}

impl Function {
    pub fn stringify(&self) -> String { format_interned!("<fn {}>", self.name) }
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
    upvalues: RcRc<Vec<Pointer<PointedUpvalue>>>,
}

impl Upvalues {
    pub fn new(upvalues: Vec<Pointer<PointedUpvalue>>) -> Self {
        Upvalues { upvalues: rcrc(upvalues) }
    }

    pub fn get(&self, index: StackLocation) -> Pointer<PointedUpvalue> {
        self.upvalues.borrow()[index].clone()
    }

    // The &mut self is here to protected against modifications, since we do modify the internal
    // upvalue.
    pub fn set(&mut self, index: StackLocation, value: Value) {
        self.upvalues.borrow_mut()[index].deep_set(value)
    }
}
