use std::fmt::Debug;
use std::slice::Iter;

use crate::rslox::compiled::op_code::{CodeLocation, OpCode};
use crate::rslox::compiled::tests::DeepEq;

pub type Line = usize;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Code(Vec<(OpCode, Line)>);

impl Code {
    pub fn write(&mut self, op: OpCode, line: Line) -> CodeLocation {
        self.0.push((op, line));
        self.current_location()
    }

    pub fn instructions(&self) -> &Vec<(OpCode, Line)> { &self.0 }
    pub fn current_location(&self) -> CodeLocation { self.len() - 1 }
    pub fn next_location(&self) -> CodeLocation { self.len() }
    pub fn swap_last_two_instructions(&mut self) -> () {
        let len = self.0.len();
        assert!(len >= 2);
        self.0.swap(len -1, len -2);
    }

    pub fn len(&self) -> usize { self.0.len() }
    pub fn get(&self, i: usize) -> Option<&(OpCode, Line)> { self.0.get(i) }
    pub fn get_mut(&mut self, i: usize) -> Option<&mut (OpCode, Line)> { self.0.get_mut(i) }
    pub fn remove(&mut self, i: usize) -> (OpCode, Line) { self.0.remove(i) }
    pub fn pop(&mut self) -> (OpCode, Line) { self.0.pop().unwrap() }
    pub fn iter(&self) -> Iter<'_, (OpCode, Line)> { self.0.iter() }
    pub fn last(&self) -> Option<&(OpCode, Line)> { self.0.last() }
}

impl DeepEq for Code {
    fn deep_eq(&self, other: &Self) -> bool { self.0.deep_eq(&other.0) }
}
