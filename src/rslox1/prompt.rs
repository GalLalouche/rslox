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
        match run_and_print_expr(&line_read) {
            Ok(_) => println!(),
            Err(r) => println!("{:?}", r),
        }
        line_read.clear();
    }
}

fn run_and_print_expr(line: &str) -> LoxResult<()> {
    run_aux(line, true)
}

pub fn run(line: &str) -> LoxResult<()> {
    run_aux(line, false)
}

fn run_aux(line: &str, print_expr: bool) -> LoxResult<()> {
    let tokens = tokenize(line)?;
    let expr = parse(&tokens)?;
    if let Some(e) = interpret(&expr)? {
        if print_expr {
            println!("{}", e.stringify());
        }
    };
    Ok(())
}