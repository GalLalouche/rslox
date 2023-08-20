use std::fs::read_to_string;
use crate::rslox::interpreted::prompt::run;

pub fn run_file(file: &str) -> () {
    let _ = run(&read_to_string(file).expect(format!("Cannot open file {}", file).as_ref()));
}