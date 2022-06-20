#[cfg(test)]
use crate::rslox1::annotated_ast::AnnotatedProgram;
#[cfg(test)]
use crate::rslox1::lexer::{Token, tokenize};
#[cfg(test)]
use crate::rslox1::parser::parse;
#[cfg(test)]
use crate::rslox1::resolve::resolve;

#[cfg(test)]
pub fn unsafe_tokenize(program: Vec<&str>) -> Vec<Token> {
    tokenize(program.join("\n").as_ref()).expect("Failed to tokenize")
}

#[cfg(test)]
pub fn unsafe_parse(program: Vec<&str>) -> AnnotatedProgram {
    parse(&unsafe_tokenize(program)).expect("Failed to parse")
}

#[cfg(test)]
pub fn unsafe_resolve(program: Vec<&str>) -> AnnotatedProgram {
    resolve(&unsafe_parse(program)).expect("Failed to resolve")
}