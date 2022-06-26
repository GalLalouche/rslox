use std::fmt::Debug;

use crate::rslox::common::lexer::{Token, tokenize};

#[cfg(test)]
pub fn unsafe_tokenize(program: Vec<&str>) -> Vec<Token> {
    tokenize(program.join("\n").as_ref()).expect("Failed to tokenize")
}

#[cfg(test)]
pub fn eq_vec_msg<A>(left: Vec<A>, right: Vec<A>) -> Option<String> where A: PartialEq + Debug + Clone {
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
#[macro_export] macro_rules! assert_eq_vec {
    ($expected: expr, $actual: expr $(,)?) => {{
        if let Some(s) = crate::rslox::common::tests::eq_vec_msg($expected, $actual) {
            assert!(false, "{}", s);
        }
    }}
}
