use std::borrow::Borrow;
use std::collections::HashSet;
use std::fmt::Debug;
use std::ops::Deref;
use std::rc::Rc;

use nonempty::NonEmpty;

use crate::rslox::compiled::code::Code;
use crate::rslox::compiled::gc::GcWeak;
use crate::rslox::compiled::op_code::{CodeLocation, OpCode};
use crate::rslox::compiled::tests::DeepEq;
use crate::rslox::compiled::value::{Function, Upvalue};

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

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Chunk {
    code: Code,
    interned_strings: HashSet<Rc<String>>,
    functions: Vec<Rc<Function>>,
}

pub type InternedString = GcWeak<String>;
pub type InternedStrings = HashSet<Rc<String>>;

impl Chunk {
    pub fn intern_string(&mut self, str: String) -> InternedString {
        GcWeak::from(self.interned_strings.get_or_insert(Rc::new(str)))
    }
    pub fn write(&mut self, op: OpCode, line: Line) -> CodeLocation {
        self.code.write(op, line)
    }
    pub fn swap_last_two_instructions(&mut self) -> () {
        self.code.swap_last_two_instructions();
    }
    pub fn add_function(
        &mut self, function: Function, line: Line, upvalues: Vec<Upvalue>) -> CodeLocation {
        let index = self.functions.len();
        let result = self.write(OpCode::Function(index), line);
        self.functions.push(Rc::new(function));
        if let Some(ne) = NonEmpty::from_vec(upvalues) {
            self.write(OpCode::Upvalues(ne), line);
        }
        result
    }
    pub fn get_mut(&mut self, i: usize) -> Option<&mut (OpCode, Line)> { self.code.get_mut(i) }
    pub fn remove(&mut self, i: usize) -> (OpCode, Line) { self.code.remove(i) }
    pub fn pop(&mut self) -> (OpCode, Line) { self.code.pop() }

    pub fn get_code(&self) -> &Code { &self.code }
    pub fn get_interned_strings(&self) -> &InternedStrings { &self.interned_strings }
    pub fn function_count(&self) -> usize { self.functions.len() }
    pub fn get_function(&self, i: usize) -> GcWeak<Function> {
        GcWeak::from(&self.functions[i].clone())
    }

    pub fn to_tuple(self) -> (Code, InternedStrings, Vec<Rc<Function>>) {
        (self.code, self.interned_strings, self.functions)
    }
}

impl DeepEq for Chunk {
    fn deep_eq(&self, other: &Self) -> bool {
        self.code.deep_eq(&other.code) && self.interned_strings == other.interned_strings &&
            self.functions.deep_eq(&other.functions)
    }
}
