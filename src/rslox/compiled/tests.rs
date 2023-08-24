use std::fmt::Debug;
use std::ops::Deref;
use std::rc::Rc;

use crate::rslox::common::tests::unsafe_tokenize;
use crate::rslox::compiled::chunk::Chunk;
use crate::rslox::compiled::compiler::compile;

#[cfg(test)]
pub fn unsafe_compile(program: Vec<&str>) -> Chunk {
    compile(unsafe_tokenize(program)).expect("Failed to compile")
}

pub trait DeepEq: PartialEq {
    fn deep_eq(&self, other: &Self) -> bool;
}

impl <A: DeepEq> DeepEq for Vec<A> {
    fn deep_eq(&self, other: &Self) -> bool {
        self.len() == other.len() &&
        self.into_iter().zip(other.into_iter()).all(|e| e.0.deep_eq(e.1))
    }
}

impl <A: DeepEq> DeepEq for Rc<A> {
    fn deep_eq(&self, other: &Self) -> bool {
        self.deref().deep_eq(other.deref())
    }
}

impl <A: DeepEq, B: DeepEq> DeepEq for (A, B) {
    fn deep_eq(&self, other: &Self) -> bool {
        self.0.deep_eq(&other.0) && self.1.deep_eq(&other.1)
    }
}

impl DeepEq for usize {
    fn deep_eq(&self, other: &Self) -> bool {
        self == other
    }
}

#[cfg(test)]
pub fn _eq_vec_msg<A>(left: Vec<A>, right: Vec<A>) -> Option<String> where A: PartialEq + Debug + Clone {
    if left == right {
        return None;
    }
    let split = |v: &Vec<A>| -> String {
        v.iter().map(|a| format!("{:?}", a)).intersperse("\n".to_owned()).collect::<String>()
    };
    let left_split = split(&left);
    let right_split = split(&right);
    if left.len() != right.len() {
        return Some(format!(
            "different lengths...\nleft vector:\n{}\nright vector:\n{}\n",
            left_split,
            right_split,
        ));
    }

    let mut result = format!(
        "different values...\nleft vector:\n{}\nright vector:\n{}\n",
        left_split,
        right_split,
    );
    for (i, (l, r)) in left.iter().zip(right.iter()).enumerate() {
        if l != r {
            result.push_str(format!("At index '{}',\nleft : {:?}\nright: {:?}\n", i, l, r).as_ref())
        }
    }
    Some(result)
}

#[cfg(test)]
#[macro_export] macro_rules! assert_deep_eq {
    ($expected: expr, $actual: expr $(,)?) => {{
        use crate::rslox::compiled::tests::DeepEq;
        if !&$expected.deep_eq(&$actual) {
            panic!("Deep EQ test failed\nexpected:{:?}\nactual  :{:?}\n", $expected, $actual)
        }
    }}
}

#[cfg(test)]
#[macro_export] macro_rules! assert_msg_contains {
    ($msg: expr, $str: expr) => {{
        if !$msg.contains($str) {
            panic!("'{}' Does not contain {}", $msg, $str)
        }
    }}
}
