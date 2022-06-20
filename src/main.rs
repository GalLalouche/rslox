#![feature(iter_intersperse)]
#![feature(option_result_contains)]
#![feature(try_blocks)]

use std::env;

use crate::rslox1::prompt::run_prompt;
use crate::rslox1::runfile::run_file;

pub mod rslox1;

fn main() {
    let args: Vec<String> = env::args().collect();
    println!("{:?}", args);
    if args.len() > 2 {
        panic!("Usage: rslox1 [script]");
    } else if args.len() == 2 {
        run_file(&args[1]);
    } else {
        run_prompt();
    }
}
