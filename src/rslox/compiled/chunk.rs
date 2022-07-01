use std::borrow::BorrowMut;
use std::collections::HashSet;
use std::convert::TryFrom;
use std::rc::{Rc, Weak};

use convert_case::{Case, Casing};

pub type Ptr = usize;

#[derive(Debug, Clone)]
pub enum OpCode {
    Return,
    Constant(Ptr),
    Bool(bool),
    // since std::String is already heap managed, we don't need a separate pointer here.
    // Hurray for real languages!
    // While "Weak", this is never expected to actually point to null as Strings are only
    // "uninterened" when garbage collected.
    String(Weak<String>),
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
}

impl PartialEq<Self> for OpCode {
    fn eq(&self, other: &Self) -> bool {
        match (&self, &other) {
            (OpCode::Return, OpCode::Return) => true,
            (OpCode::Constant(p1), OpCode::Constant(p2)) => p1 == p2,
            (OpCode::Bool(b1), OpCode::Bool(b2)) => b1 == b2,
            (OpCode::String(s1), OpCode::String(s2)) => {
                assert!(s1.upgrade().is_some());
                assert!(s2.upgrade().is_some());
                s1.ptr_eq(s2)
            },
            (OpCode::Nil, OpCode::Nil) => true,
            (OpCode::Add, OpCode::Add) => true,
            (OpCode::Subtract, OpCode::Subtract) => true,
            (OpCode::Multiply, OpCode::Multiply) => true,
            (OpCode::Divide, OpCode::Divide) => true,
            (OpCode::Negate, OpCode::Negate) => true,
            (OpCode::Not, OpCode::Not) => true,
            (OpCode::Equals, OpCode::Equals) => true,
            (OpCode::Less, OpCode::Less) => true,
            (OpCode::Greater, OpCode::Greater) => true,
            _ => false,
        }
    }
}

impl Eq for &OpCode {}

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
    String(Weak<String>),
}

impl PartialEq<Self> for Value {
    fn eq(&self, other: &Self) -> bool {
        match (&self, &other) {
            (Value::Number(n1), Value::Number(n2)) => n1 == n2,
            (Value::Bool(b1), Value::Bool(b2)) => b1 == b2,
            (Value::Nil, Value::Nil) => true,
            (Value::String(s1), Value::String(s2)) => {
                assert!(s1.upgrade().is_some());
                assert!(s2.upgrade().is_some());
                s1.ptr_eq(s2)
            },
            _ => false,
        }
    }
}
impl Value {
    pub fn is_nil(&self) -> bool {
        match &self {
            Value::Nil => true,
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

#[derive(Debug, Clone, PartialEq)]
pub struct Chunk {
    pub code: Vec<(OpCode, Line)>,
    pub number_constants: Vec<f64>,
    pub interned_strings: HashSet<Rc<String>>,
}

impl Chunk {
    pub fn new() -> Self {
        Chunk { code: Vec::new(), number_constants: Vec::new(), interned_strings: HashSet::new() }
    }
    pub fn write(&mut self, op: OpCode, line: Line) {
        self.code.push((op, line));
    }
    pub fn write_constant(&mut self, value: f64, line: Line) {
        let ptr = self.add_constant(value);
        self.write(OpCode::Constant(ptr), line)
    }
    pub fn get(&self, i: usize) -> Option<&(OpCode, Line)> {
        self.code.get(i)
    }
    pub fn add_string(&mut self, str: String, line: Line) {
        let entry = self.interned_strings.get_or_insert(Rc::new(str));
        self.code.push((OpCode::String(Rc::downgrade(entry)), line))
    }
    pub fn add_constant(&mut self, value: f64) -> usize {
        self.number_constants.push(value);
        return self.number_constants.len() - 1;
    }
    pub fn get_constant(&self, ptr: &Ptr) -> Option<f64> {
        self.number_constants.get(*ptr).cloned()
    }
}