use std::borrow::Borrow;
use std::collections::HashSet;
use std::fmt::Debug;
use std::ops::Deref;
use std::rc::Rc;

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

#[derive(Debug, Clone, PartialEq)]
pub struct Chunk {
    pub code: Vec<(OpCode, Line)>,
    pub interned_strings: HashSet<Rc<String>>,
    globals: HashSet<GcRc<String>>,
}

impl Chunk {
    pub fn new() -> Self {
        Chunk {
            code: Vec::new(),
            interned_strings: HashSet::new(),
            globals: HashSet::new(),
        }
    }
    pub fn write(&mut self, op: OpCode, line: Line) -> CodeLocation {
        self.code.push((op, line));
        self.current_location()
    }
    pub fn current_location(&self) -> CodeLocation { self.code.len() - 1 }
    pub fn next_location(&self) -> CodeLocation { self.current_location() + 1 }
    pub fn define_global(&mut self, str: String) -> GcWeak<String> {
        (&self.globals.get_or_insert(GcRc(Rc::new(str))).0).into()
    }
    pub fn get(&self, i: usize) -> Option<&(OpCode, Line)> {
        self.code.get(i)
    }
    pub fn get_global(&self, str: &str) -> Option<Rc<String>> {
        self.globals.get(str).map(|e| e.0.clone())
    }
    pub fn add_string(&mut self, str: String, line: Line) {
        let entry = self.interned_strings.get_or_insert(Rc::new(str));
        self.code.push((OpCode::String(entry.into()), line))
    }
}

impl DeepEq for Chunk {
    fn deep_eq(&self, other: &Self) -> bool {
        self.code.deep_eq(&other.code) &&
            self.interned_strings == other.interned_strings &&
            self.globals == other.globals
    }
}
