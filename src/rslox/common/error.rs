use std::fmt::Debug;
use nonempty::NonEmpty;

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
