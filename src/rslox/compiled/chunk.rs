use std::borrow::Borrow;
use std::collections::HashSet;
use std::fmt::Debug;
use std::ops::Deref;
use std::rc::Rc;

use crate::rslox::compiled::code::Code;
use crate::rslox::compiled::gc::GcWeak;
use crate::rslox::compiled::op_code::{CodeLocation, OpCode};
use crate::rslox::compiled::tests::DeepEq;

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

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Chunk {
    code: Code,
    interned_strings: HashSet<Rc<String>>,
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
    pub fn next_location(&self) -> CodeLocation { self.code.next_location() }
    pub fn get(&self, i: usize) -> Option<&(OpCode, Line)> { self.code.get(i) }
    pub fn get_mut(&mut self, i: usize) -> Option<&mut (OpCode, Line)> { self.code.get_mut(i) }
    pub fn remove(&mut self, i: usize) -> (OpCode, Line) { self.code.remove(i) }
    // This ensures all operations are done by the above methods, except the last phase of
    // deconstructing.
    pub fn to_tuple(self) -> (Code, InternedStrings) { (self.code, self.interned_strings) }
    pub fn get_code(&self) -> &Code { &self.code }
    pub fn get_interned_strings(&self) -> &InternedStrings { &self.interned_strings }
}

impl DeepEq for Chunk {
    fn deep_eq(&self, other: &Self) -> bool {
        self.code.deep_eq(&other.code) && self.interned_strings == other.interned_strings
    }
}
