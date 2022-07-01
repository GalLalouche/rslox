use crate::rslox::common::tests::unsafe_tokenize;
use crate::rslox::compiled::chunk::Chunk;
use crate::rslox::compiled::parser::parse;

#[cfg(test)]
pub fn unsafe_parse(program: Vec<&str>) -> Chunk {
    parse(unsafe_tokenize(program)).expect("Failed to parse")
}
