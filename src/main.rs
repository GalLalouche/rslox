#![feature(hash_set_entry)]
#![feature(iter_intersperse)]
#![feature(option_result_contains)]
#![feature(try_blocks)]
#![feature(type_ascription)]

#[macro_use]
extern crate num_derive;
extern crate num_traits;
extern crate core;

use std::env;

use rslox::interpreted::prompt::run_prompt;
use rslox::interpreted::runfile::run_file;

pub mod rslox;

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
