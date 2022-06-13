use std::io;
use std::io::BufRead;

use crate::rslox1::common::LoxResult;
use crate::rslox1::interpreter::interpret;
use crate::rslox1::lexer::tokenize;
use crate::rslox1::parser::parse;

pub fn run_prompt() -> () {
    let stdin = io::stdin();
    let mut line_read: String = "".to_owned();
    loop {
        print!("> ");
        stdin.lock().read_line(&mut line_read).expect("Failed to read line from input");
        match run(&line_read) {
            Ok(_) => println!(),
            Err(r) => println!("{:?}", r),
        }
        line_read.clear();
    }
}

pub fn run(line: &str) -> LoxResult<()> {
    let tokens = tokenize(line)?;
    let expr = parse(&tokens)?;
    interpret(&expr)?;
    Ok(())
}