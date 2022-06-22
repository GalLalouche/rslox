use std::cell::RefCell;
use std::rc::Rc;

pub type RcRc<A> = Rc<RefCell<A>>;
pub fn rcrc<A>(a: A) -> RcRc<A>  {
    Rc::new(RefCell::new(a))
}