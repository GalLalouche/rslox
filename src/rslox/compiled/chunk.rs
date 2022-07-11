use std::fmt::Debug;

use crate::rslox::compiled::op_code::{CodeLocation, OpCode};

pub type Line = usize;

#[derive(Debug, Clone, PartialEq)]
pub struct Chunk {
    pub code: Vec<(OpCode, Line)>,
}

impl Chunk {
    pub fn new() -> Self { Chunk { code: Vec::new() } }
    pub fn write(&mut self, op: OpCode, line: Line) -> CodeLocation {
        self.code.push((op, line));
        self.current_location()
    }
    pub fn current_location(&self) -> CodeLocation { self.code.len() - 1 }
    pub fn next_location(&self) -> CodeLocation { self.current_location() + 1 }
    pub fn get(&self, i: usize) -> Option<&(OpCode, Line)> {
        self.code.get(i)
    }
}