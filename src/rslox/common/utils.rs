use std::cell::RefCell;
use std::fmt::Debug;
use std::rc::Rc;
use nonempty::NonEmpty;

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

impl<A: Debug> SliceExt<A> for NonEmpty<A> {
    fn unwrap_single(&self) -> &A {
        assert!(self.tail().is_empty(), "Expected NonEmpty with single element, got {:?}", self);
        self.first()
    }
}

pub fn debug_mk_string<'a, A: Debug + 'a, I>(i: &'a I) -> String
    where &'a I: IntoIterator<Item=&'a A>
{
    i.into_iter().map(|e: &A| format!("{:?}", e)).collect::<Vec<_>>().join("\n")
}
