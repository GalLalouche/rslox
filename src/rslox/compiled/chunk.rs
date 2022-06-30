use std::borrow::BorrowMut;
use std::convert::TryFrom;
use convert_case::{Case, Casing};

pub type Ptr = usize;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum OpCode {
    Return,
    Constant(Ptr),
    Bool(bool),
    Nil,
    Add,
    Subtract,
    Multiply,
    Divide,
    Negate,
    Not,
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

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Number(f64),
    Bool(bool),
    Nil,
}

impl Value {
    pub fn is_nil(&self) -> bool {
        match &self {
            Value::Nil => true,
            _ => false,
        }
    }
}

impl <'a> TryFrom<&'a Value> for &'a f64 {
    type Error = String;

    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match &value {
            Value::Number(f) => Ok(&f),
            e => Err(format!("Expected Value::Number, but found {:?}", e)),
        }
    }
}

impl <'a> TryFrom<&'a mut Value> for &'a mut f64 {
    type Error = String;

    fn try_from(value: &'a mut Value) -> Result<Self, Self::Error> {
        match value.borrow_mut() {
            Value::Number(f) => Ok(f),
            e => Err(format!("Expected Value::Number, but found {:?}", e)),
        }
    }
}

impl <'a> TryFrom<&'a mut Value> for &'a mut bool {
    type Error = String;

    fn try_from(value: &'a mut Value) -> Result<Self, Self::Error> {
        match value.borrow_mut() {
            Value::Bool(b) => Ok(b),
            e => Err(format!("Expected Value::Bool, but found {:?}", e)),
        }
    }
}

impl <'a> TryFrom<&'a Value> for &'a bool {
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
    pub constants: Vec<f64>,
}

impl Chunk {
    pub fn new() -> Self {
        Chunk { code: Vec::new(), constants: Vec::new() }
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

    pub fn add_constant(&mut self, value: f64) -> usize {
        self.constants.push(value);
        return self.constants.len() - 1;
    }
    pub fn get_constant(&self, ptr: &Ptr) -> Option<f64> {
        self.constants.get(*ptr).cloned()
    }
}