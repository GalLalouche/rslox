use std::cell::RefCell;
use std::fmt::{Debug, Formatter};
use std::rc::{Rc, Weak};

use crate::rslox::common::utils::RcRc;

// Weak that is garbage collected, and is therefore deref-able to plain old value, with the risk of
// panic-ing for catching programmer errors. Basically here for PartialEq implementation. I'm sure
// there's a good reason why it's not implemented for plain old Weak :\
#[derive(Clone)]
pub struct GcWeak<A>(Weak<A>);

impl<A> GcWeak<A> {
    pub fn unwrap_upgrade(&self) -> Rc<A> {
        self.0.upgrade().expect("GcWeak value was already collected")
    }
}

impl<A: Eq> GcWeak<A> {
    pub fn compare_values(&self, other: &GcWeak<A>) -> bool {
        self.0.upgrade().unwrap() == other.0.upgrade().unwrap()
    }
}

impl<A> From<&Rc<A>> for GcWeak<A> {
    fn from(rc: &Rc<A>) -> Self {
        GcWeak(Rc::downgrade(rc))
    }
}

impl<A: Debug> Debug for GcWeak<A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GcWeak")
            .field("0", &self.0.upgrade())
            .finish()
    }
}

impl<A> PartialEq for GcWeak<A> {
    fn eq(&self, other: &Self) -> bool {
        assert!(self.0.upgrade().is_some());
        assert!(other.0.upgrade().is_some());
        self.0.ptr_eq(&other.0)
    }
}


#[derive(Clone)]
pub struct GcWeakMut<A>(Weak<RefCell<A>>);

impl<A> GcWeakMut<A> {
    pub fn unwrap_upgrade(&self) -> RcRc<A> {
        self.0.upgrade().expect("GcWeakMut value was already collected")
    }

    pub fn null() -> Self { GcWeakMut(Weak::new()) }
}

impl<A: Debug> Debug for GcWeakMut<A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GcWeakMut")
            .field("0", &self.0.upgrade())
            .finish()
    }
}

impl<A> From<&RcRc<A>> for GcWeakMut<A> {
    fn from(rc: &RcRc<A>) -> Self { GcWeakMut(Rc::downgrade(rc)) }
}

impl<A> PartialEq for GcWeakMut<A> {
    fn eq(&self, other: &Self) -> bool {
        assert!(self.0.upgrade().is_some());
        assert!(other.0.upgrade().is_some());
        self.0.ptr_eq(&other.0)
    }
}
