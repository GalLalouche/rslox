use crate::rslox::common::tests::unsafe_tokenize;
use crate::rslox::interpreted::annotated_ast::AnnotatedProgram;
use crate::rslox::interpreted::parser::parse;
use crate::rslox::interpreted::resolve::resolve;

#[cfg(test)]
pub fn unsafe_parse(program: Vec<&str>) -> AnnotatedProgram {
    parse(&unsafe_tokenize(program)).expect("Failed to parse")
}

#[cfg(test)]
pub fn unsafe_resolve(program: Vec<&str>) -> AnnotatedProgram {
    resolve(unsafe_parse(program)).expect("Failed to resolve")
}
