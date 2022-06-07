use std::io;
use std::io::BufRead;

use crate::rslox1::lexer::{LexResult, run};

pub fn run_prompt() -> () {
    let stdin = io::stdin();
    let mut line_read: String = "".to_owned();
    loop {
        print!("> ");
        stdin.lock().read_line(&mut line_read).expect("Failed to read line from input");
        match run(&line_read) {
            Ok(_) => println!(),
            Err(r) => println!("{}", r),
        }
        line_read.clear();
    }
}