use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::ops::Deref;
use std::rc::Rc;
use crate::rslox::compiled::chunk::{Chunk, Line};

use crate::rslox::compiled::gc::GcWeak;
use crate::rslox::compiled::op_code::{OpCode};
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

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Program {
    pub chunk: Chunk,
    pub interned_strings: HashSet<Rc<String>>,
    pub interned_functions: HashMap<Rc<String>, Rc<Function>>,
    globals: HashSet<GcRc<String>>,
}

impl Program {
    pub fn define_global(&mut self, str: String) -> GcWeak<String> {
        (&self.globals.get_or_insert(GcRc(Rc::new(str))).0).into()
    }
    pub fn get_global(&self, str: &str) -> Option<Rc<String>> {
        self.globals.get(str).map(|e| e.0.clone())
    }
    pub fn intern_string(&mut self, str: String) -> Rc<String> {
        self.interned_strings.get_or_insert(Rc::new(str)).clone()
    }
    pub fn intern_function(&mut self, func: Function) -> Rc<Function> {
        let key = self.intern_string(func.name.clone());
        assert!(!self.interned_functions.contains_key(&key));
        let result = Rc::new(func);
        self.interned_functions.insert(key, result.clone());
        result
    }
}

impl DeepEq for Program {
    fn deep_eq(&self, other: &Self) -> bool {
        self.chunk.deep_eq(&other.chunk) &&
            self.interned_strings == other.interned_strings &&
            self.globals == other.globals
    }
}
