use std::borrow::Borrow;
use std::fmt::Debug;
use std::ops::Deref;
use std::rc::{Rc, Weak};

use crate::rslox::compiled::code::Code;
use crate::rslox::compiled::op_code::{CodeLocation, OpCode, StackLocation};
use crate::rslox::compiled::tests::DeepEq;
use crate::rslox::compiled::value::Function;

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
    fn borrow(&self) -> &str { self.deref().as_ref() }
}

pub type Line = usize;

// Unlike the book, I don't use constants for numbers.

#[derive(Debug, PartialEq, Default)]
pub struct Chunk {
    code: Code,
    functions: Vec<Rc<Function>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub struct Upvalue {
    pub index: StackLocation,
    pub is_local: bool,
}

impl Chunk {
    pub fn write(&mut self, op: OpCode, line: Line) -> CodeLocation {
        self.code.write(op, line)
    }
    pub fn swap_last_two_instructions(&mut self) -> () {
        self.code.swap_last_two_instructions();
    }
    pub fn add_function(
        &mut self, function: Function, line: Line, upvalues: Vec<Upvalue>) -> CodeLocation {
        let index = self.functions.len();
        let result = self.write(OpCode::Function(index, upvalues), line);
        self.functions.push(Rc::new(function));
        result
    }
    pub fn get_mut(&mut self, i: usize) -> Option<&mut (OpCode, Line)> { self.code.get_mut(i) }
    pub fn remove(&mut self, i: usize) -> (OpCode, Line) { self.code.remove(i) }
    pub fn pop(&mut self) -> (OpCode, Line) { self.code.pop() }

    pub fn get_code(&self) -> &Code { &self.code }
    pub fn function_count(&self) -> usize { self.functions.len() }
    pub fn get_function(&self, i: usize) -> Weak<Function> { Rc::downgrade(&self.functions[i]) }

    pub fn to_tuple(self) -> (Code, Vec<Rc<Function>>) { (self.code, self.functions) }

    pub fn mark(&self) {
       for c in self.code.iter() {
          match &c.0 {
              OpCode::String(s) => s.mark(),
              OpCode::DefineGlobal(g) => g.mark(),
              OpCode::GetGlobal(g) => g.mark(),
              OpCode::SetGlobal(g) => g.mark(),
              OpCode::Return | OpCode::Pop | OpCode::PopN(_) | OpCode::Print |
              OpCode::Function(_, _) | OpCode::CloseUpvalue | OpCode::DefineLocal(_) |
              OpCode::Number(_) | OpCode::Bool(_) | OpCode::GetUpvalue(_) | OpCode::SetUpvalue(_) |
              OpCode::GetLocal(_) | OpCode::SetLocal(_) | OpCode::Nil | OpCode::Call(_) |
              OpCode::Add | OpCode::Subtract | OpCode::Multiply | OpCode::Divide | OpCode::Negate |
              OpCode::Not | OpCode::Equals | OpCode::Less | OpCode::Greater |
              OpCode::UnpatchedJump | OpCode::Jump(_) | OpCode::JumpIfFalse(_) => ()
          }
       }
        for f in self.functions.iter() {
            f.name.mark();
            f.chunk.mark();
        }
    }
}

impl DeepEq for Chunk {
    fn deep_eq(&self, other: &Self) -> bool {
        self.code.deep_eq(&other.code) &&
            self.functions.deep_eq(&other.functions)
    }
}
