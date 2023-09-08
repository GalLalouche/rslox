use std::cell::{Ref, RefCell, RefMut};
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::rc::{Rc, Weak};

use crate::rslox::common::utils::{RcRc, rcrc};
use crate::rslox::compiled::tests::DeepEq;

pub type IsUsed = bool;

#[derive(Debug)]
pub struct Managed<A>(RcRc<(A, IsUsed)>);

impl<A> Managed<A> {
    pub fn new(value: A) -> Self { Managed(rcrc((value, false as IsUsed))) }
    pub fn ptr(&self) -> Pointer<A> { Pointer(Rc::downgrade(&self.0)) }
    pub fn as_ref(&self) -> Ref<A> { Ref::map(self.0.borrow(), |e| &e.0) }
    pub fn as_ref_mut(&mut self) -> RefMut<A> { RefMut::map(self.0.borrow_mut(), |e| &mut e.0) }
    pub fn get_and_reset_mark(&self) -> bool {
        let result = self.0.borrow().1;
        self.0.borrow_mut().1 = false;
        result
    }
}

impl<A: PartialEq> PartialEq for Managed<A> {
    fn eq(&self, other: &Self) -> bool {
        self.0.borrow().deref().0 == other.0.borrow().deref().0
    }
}

impl<A: Eq> Eq for Managed<A> {}

impl<A: DeepEq> DeepEq for Managed<A> {
    fn deep_eq(&self, other: &Self) -> bool {
        self.0.borrow().deref().0.deep_eq(&other.0.borrow().deref().0)
    }
}

impl<A: Hash> Hash for Managed<A> {
    fn hash<H: Hasher>(&self, state: &mut H) { self.0.borrow().deref().0.hash(state) }
}

// Weak that is garbage collected, and is therefore deref-able to plain old value, with the risk of
// panic-ing for catching programmer errors. Basically here for PartialEq implementation. I'm sure
// there's a good reason why it's not implemented for plain old Weak :\
#[derive(Clone)]
pub struct Pointer<A>(Weak<RefCell<(A, bool)>>);

impl<A> Pointer<A> {
    pub fn apply<B, F: FnOnce(&A) -> B>(&self, func: F) -> B {
        func(&self.unwrap_upgrade().borrow().0)
    }
    pub fn mutate<F: FnOnce(&mut A) -> ()>(&mut self, func: F) {
        let rc = self.unwrap_upgrade();
        assert!(!rc.borrow().1, "mutation should not occur while marking");
        func(RefMut::map(rc.borrow_mut(), |e| &mut e.0).deref_mut());
    }
    fn unwrap_upgrade(&self) -> RcRc<(A, IsUsed)> {
        self.0.upgrade().expect("Pointer was already collected")
    }
    pub fn mark(&self) { self.unwrap_upgrade().borrow_mut().1 = true; }
}

impl<A: ToOwned<Owned=A>> Pointer<A> {
    // Half the places the use to_owned can probably just return &str.
    pub fn to_owned(&self) -> A { self.apply(|e| e.to_owned()) }
}

pub type InternedString = Pointer<String>;

#[macro_export] macro_rules! format_interned {
    ($fmt:tt, $str:expr) => {{
        use std::ops::Deref;
        let rc = $str.rc_for_macro__();
        let borrowed = rc.borrow();
        let str_ref = &borrowed.deref().0;
        format!($fmt, str_ref)
    }};
    ($fmt:tt, $str1:tt, $str2:tt) => {{
        use std::ops::Deref;
        let rc1 = $str1.rc_for_macro__();
        let borrowed1 = rc1.borrow();
        let str_ref1 = &borrowed1.deref().0;
        let rc2 = $str2.rc_for_macro__();
        let borrowed2 = rc2.borrow();
        let str_ref2 = &borrowed2.deref().0;
        format!($fmt, str_ref1, str_ref2)
    }};
}

impl InternedString {
    #[doc(hidden)]
    pub fn rc_for_macro__(&self) -> RcRc<(String, IsUsed)> { self.unwrap_upgrade() }
}

impl<A: PartialEq> Pointer<A> {
    pub fn compare_values(&self, other: &Pointer<A>) -> bool {
        self.0.upgrade().unwrap() == other.0.upgrade().unwrap()
    }
}

impl<A: Debug> Debug for Pointer<A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Pointer")
            .field("0", &self.0.upgrade())
            .finish()
    }
}

impl<A> PartialEq for Pointer<A> {
    fn eq(&self, other: &Self) -> bool {
        assert!(self.0.upgrade().is_some());
        assert!(other.0.upgrade().is_some());
        self.0.ptr_eq(&other.0)
    }
}

impl<A> Eq for Pointer<A> {}

impl<A> Hash for Pointer<A> {
    fn hash<H: Hasher>(&self, state: &mut H) { self.0.as_ptr().hash(state) }
}