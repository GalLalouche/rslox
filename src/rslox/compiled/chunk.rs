use convert_case::{Case, Casing};

pub type Ptr = usize;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum OpCode {
    Return,
    Constant(Ptr),
    Add,
    Substract,
    Multiply,
    Divide,
    Negate,
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
pub type Value = f64;

#[derive(Debug, Clone, PartialEq)]
pub struct Chunk {
    pub code: Vec<(OpCode, Line)>,
    pub constants: Vec<Value>,
}

impl Chunk {
    pub fn new() -> Self {
        Chunk { code: Vec::new(), constants: Vec::new() }
    }
    pub fn write(&mut self, op: OpCode, line: Line) {
        self.code.push((op, line));
    }
    pub fn write_constant(&mut self, value: Value, line: Line) {
        let ptr = self.add_constant(value);
        self.write(OpCode::Constant(ptr), line)
    }
    pub fn get(&self, i: usize) -> Option<&(OpCode, Line)> {
        self.code.get(i)
    }

    pub fn add_constant(&mut self, value: Value) -> usize {
        self.constants.push(value);
        return self.constants.len() - 1;
    }
    pub fn get_constant(&self, ptr: &Ptr) -> Option<Value> {
        self.constants.get(*ptr).cloned()
    }
}