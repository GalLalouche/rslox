use std::fmt::Debug;
use nonempty::NonEmpty;
use crate::rslox::common::lexer::Token;

pub trait LoxError: Debug {
    fn get_info(&self) -> ErrorInfo;
    fn get_message(&self) -> String;
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct ErrorInfo {
    pub line: usize,
}

pub type LoxResult<A> = Result<A, NonEmpty<Box<dyn LoxError>>>;

pub trait ErrorReport<A> {
    fn to_non_empty(self) -> NonEmpty<A>;
}

pub fn convert_errors<A, E: LoxError + 'static>(result: Result<A, NonEmpty<E>>) -> LoxResult<A> {
    result.map_err(|e| e.map::<Box<dyn LoxError>, _>(|a| Box::new(a)))
}

pub fn convert_error<A, E: LoxError + 'static>(result: Result<A, E>) -> LoxResult<A> {
    convert_errors(result.map_err(|e| NonEmpty::new(e)))
}

#[derive(Debug, PartialEq, Clone)]
pub struct ParserError {
    pub message: String,
    pub token: Token,
}

impl ParserError {
    pub fn new<S: Into<String>>(message: S, token: Token) -> Self {
        ParserError { message: message.into(), token }
    }
}

impl LoxError for ParserError {
    fn get_info(&self) -> ErrorInfo {
        ErrorInfo { line: self.token.line }
    }

    fn get_message(&self) -> String {
        self.message.to_owned()
    }
}

pub trait ToNonEmpty<B> {
    fn to_nonempty(self) -> B;
}

impl <A, Err> ToNonEmpty<Result<A, NonEmpty<Err>>> for Result<A, Err> {
    fn to_nonempty(self) -> Result<A, NonEmpty<Err>> {
        self.map_err(NonEmpty::new)
    }
}