use std::fs::read_to_string;
use crate::rslox1::lexer::run;

pub fn run_file(file: &str) -> () {
    run(&read_to_string(file).expect("Could not read file"));
}