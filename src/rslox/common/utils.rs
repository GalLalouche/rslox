use std::cell::RefCell;
use std::fmt::Debug;
use std::rc::Rc;

pub type RcRc<A> = Rc<RefCell<A>>;

pub fn rcrc<A>(a: A) -> RcRc<A> {
    Rc::new(RefCell::new(a))
}

pub trait SliceExt<A> {
    fn unwrap_single(&self) -> &A;
}

impl<A: Debug> SliceExt<A> for [A] {
    fn unwrap_single(&self) -> &A {
        assert_eq!(self.len(), 1, "Expected slice with single element, got {:?}", self);
        self.first().unwrap()
    }
}


