use std::borrow::Borrow;
use std::collections::HashSet;
use std::fmt::Debug;
use std::ops::Deref;
use std::rc::Rc;

use crate::rslox::compiled::code::Code;
use crate::rslox::compiled::gc::GcWeak;
use crate::rslox::compiled::op_code::OpCode;
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
    pub code: Code,
    pub interned_strings: HashSet<Rc<String>>,
    globals: HashSet<GcRc<String>>,
}

impl Chunk {
    pub fn define_global(&mut self, str: String) -> GcWeak<String> {
        (&self.globals.get_or_insert(GcRc(Rc::new(str))).0).into()
    }
    pub fn get_global(&self, str: &str) -> Option<Rc<String>> {
        self.globals.get(str).map(|e| e.0.clone())
    }
    pub fn intern_string(&mut self, str: String, line: Line) {
        let entry = self.interned_strings.get_or_insert(Rc::new(str));
        self.code.write(OpCode::String(entry.into()), line);
    }
}

impl DeepEq for Chunk {
    fn deep_eq(&self, other: &Self) -> bool {
        self.code.deep_eq(&other.code) &&
            self.interned_strings == other.interned_strings &&
            self.globals == other.globals
    }
}
