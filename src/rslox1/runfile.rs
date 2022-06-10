use std::fs::read_to_string;

use crate::rslox1::prompt::run;

pub fn run_file(file: &str) -> () {
    run(&read_to_string(file).expect(format!("Cannot open file {}", file).as_ref()));
}