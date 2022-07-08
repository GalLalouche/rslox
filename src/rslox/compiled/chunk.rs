use std::borrow::{Borrow, BorrowMut};
use std::collections::HashSet;
use std::convert::TryFrom;
use std::ops::Deref;
use std::rc::{Rc, Weak};

use convert_case::{Case, Casing};

use crate::rslox::compiled::tests::DeepEq;

pub type Ptr = usize;

// Overriding for Borrow
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct GcRc<A>(Rc<A>);

impl<A> Deref for GcRc<A> {
    type Target = A;

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

impl Borrow<str> for GcRc<String> {
    fn borrow(&self) -> &str {
        self.deref().as_ref()
    }
}

// Weak that is garbage collected, and is therefore deref-able to plain old value, with the risk of
// panic-ing for catching programmer errors. Basically here for PartialEq implementation. I'm sure
// there's a good reason why it's not implemented for plain old Weak :\
#[derive(Debug, Clone)]
pub struct GcWeak<A>(Weak<A>);

impl<A> GcWeak<A> {
    pub fn unwrap_upgrade(&self) -> Rc<A> {
        self.0.upgrade().unwrap()
    }
}

impl<A> From<&Rc<A>> for GcWeak<A> {
    fn from(rc: &Rc<A>) -> Self {
        GcWeak(Rc::downgrade(rc))
    }
}

impl<A> PartialEq for GcWeak<A> {
    fn eq(&self, other: &Self) -> bool {
        assert!(self.0.upgrade().is_some());
        assert!(other.0.upgrade().is_some());
        self.0.ptr_eq(&other.0)
    }
}

type CodeLocation = usize;
type StackLocation = usize;
#[derive(Debug, Clone, PartialEq)]
pub enum OpCode {
    Return,
    Pop,
    Print,
    DefineGlobal(GcWeak<String>),
    DefineLocal(StackLocation),
    Constant(Ptr),
    Bool(bool),
    // since std::String is already heap managed, we don't need a separate pointer here.
    // Hurray for real languages!
    // While "Weak", this is never expected to actually point to null as Strings are only
    // "uninterested" when garbage collected.
    String(GcWeak<String>),
    GlobalIdentifier(GcWeak<String>),
    LocalIdentifier(StackLocation),
    Nil,
    Add,
    Subtract,
    Multiply,
    Divide,
    Negate,
    Not,
    Equals,
    Less,
    Greater,
    UnpatchedJump,
    JumpIfFalse(CodeLocation),
}

impl Eq for &OpCode {}

impl DeepEq for OpCode {
    fn deep_eq(&self, other: &Self) -> bool {
        match (&self, &other) {
            (OpCode::DefineGlobal(s1), OpCode::DefineGlobal(s2)) =>
                s1.unwrap_upgrade() == s2.unwrap_upgrade(),
            (OpCode::String(s1), OpCode::String(s2)) =>
                s1.unwrap_upgrade() == s2.unwrap_upgrade(),
            _ => self == other
        }
    }
}

impl OpCode {
    pub fn to_upper_snake(&self) -> String {
        format!("OP_{:13}",
                format!("{:?}", self)
                    .to_case(Case::UpperSnake)
                    .chars()
                    .into_iter()
                    .take_while(|e| e.is_alphanumeric())
                    .collect::<String>())
    }
}

pub type Line = usize;

#[derive(Debug, Clone)]
pub enum Value {
    Number(f64),
    Bool(bool),
    Nil,
    String(GcWeak<String>),
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
    pub fn is_nil(&self) -> bool {
        match &self {
            Value::Nil => true,
            _ => false,
        }
    }

    pub fn stringify(&self) -> String {
        match self {
            Value::Number(f) => f.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Nil => "nil".to_owned(),
            Value::String(s) => s.unwrap_upgrade().to_string(),
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

impl<'a> TryFrom<&'a Value> for GcWeak<String> {
    type Error = String;

    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match &value {
            Value::String(s) => Ok(s.clone()),
            e => Err(format!("Expected Value::String, but found {:?}", e)),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Chunk {
    pub code: Vec<(OpCode, Line)>,
    pub number_constants: Vec<f64>,
    pub interned_strings: HashSet<Rc<String>>,
    globals: HashSet<GcRc<String>>,
}

impl Chunk {
    pub fn new() -> Self {
        Chunk {
            code: Vec::new(),
            number_constants: Vec::new(),
            interned_strings: HashSet::new(),
            globals: HashSet::new(),
        }
    }
    pub fn write(&mut self, op: OpCode, line: Line) {
        self.code.push((op, line));
    }
    pub fn write_constant(&mut self, value: f64, line: Line) {
        let ptr = self.add_constant(value);
        self.write(OpCode::Constant(ptr), line)
    }
    pub fn define_global(&mut self, str: String) -> GcWeak<String> {
        (&self.globals.get_or_insert(GcRc(Rc::new(str))).0).into()
    }
    pub fn get(&self, i: usize) -> Option<&(OpCode, Line)> {
        self.code.get(i)
    }
    pub fn get_global(&self, str: &str) -> Option<GcWeak<String>> {
        self.globals.get(str).map(|e| (&e.0).into())
    }
    pub fn add_string(&mut self, str: String, line: Line) {
        let entry = self.interned_strings.get_or_insert(Rc::new(str));
        self.code.push((OpCode::String(entry.into()), line))
    }
    pub fn add_constant(&mut self, value: f64) -> usize {
        self.number_constants.push(value);
        return self.number_constants.len() - 1;
    }
    pub fn get_constant(&self, ptr: &Ptr) -> Option<f64> {
        self.number_constants.get(*ptr).cloned()
    }
}

impl DeepEq for Chunk {
    fn deep_eq(&self, other: &Self) -> bool {
        self.code.deep_eq(&other.code) && self.number_constants == other.number_constants &&
            self.interned_strings == other.interned_strings &&
            self.globals == other.globals
    }
}
