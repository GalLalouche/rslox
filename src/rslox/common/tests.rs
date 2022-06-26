use crate::rslox::common::lexer::{Token, tokenize};

#[cfg(test)]
pub fn unsafe_tokenize(program: Vec<&str>) -> Vec<Token> {
    tokenize(program.join("\n").as_ref()).expect("Failed to tokenize")
}
