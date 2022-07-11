use std::fmt::Debug;

use crate::rslox::compiled::op_code::{CodeLocation, OpCode};
use crate::rslox::compiled::tests::DeepEq;

pub type Line = usize;

#[derive(Debug, Clone, PartialEq)]
pub struct Chunk(pub Vec<(OpCode, Line)>);

impl Chunk {
    pub fn new() -> Self { Chunk(Vec::new()) }
    pub fn write(&mut self, op: OpCode, line: Line) -> CodeLocation {
        self.0.push((op, line));
        self.current_location()
    }
    pub fn current_location(&self) -> CodeLocation { self.0.len() - 1 }
    pub fn next_location(&self) -> CodeLocation { self.current_location() + 1 }
    pub fn get(&self, i: usize) -> Option<&(OpCode, Line)> { self.0.get(i) }
}

impl DeepEq for Chunk {
    fn deep_eq(&self, other: &Self) -> bool { self.0.deep_eq(&other.0) }
}
