use std::convert::TryInto;

use crate::rslox::compiled::chunk::{Chunk, Line, OpCode, Value};
use std::stringify;

#[derive(Debug, Clone, PartialEq, Eq)]
enum VmResult {
    CompileError { message: String, line: Line },
    RuntimeError { message: String, line: Line },
}

impl VmResult {
    pub fn line(&self) -> Line {
        match &self {
            VmResult::CompileError { line, .. } => *line,
            VmResult::RuntimeError { line, .. } => *line,
        }
    }
}

fn try_number(value: &Value, msg: &str, line: &Line) -> Result<f64, VmResult> {
    let f: &f64 =
        value.try_into().map_err(|err: String| VmResult::RuntimeError { message: format!("{} ({})", err, msg), line: *line })?;
    Ok(*f)
}

fn try_number_mut<'a>(value: &'a mut Value, msg: &str, line: &Line) -> Result<&'a mut f64, VmResult> {
    value.try_into().map_err(|err: String| VmResult::RuntimeError { message: format!("{} ({})", err, msg), line: *line })
}

#[derive(Debug)]
struct VirtualMachine {
    chunk: Chunk,
    stack: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq)]
struct TracedCommand {
    assembly: String,
    stack_state: Vec<Value>,
}

impl TracedCommand {
    pub fn new<S: Into<String>>(assembly: S, stack_state: Vec<Value>) -> Self {
        TracedCommand { assembly: assembly.into(), stack_state }
    }
}

impl VirtualMachine {
    pub fn new(chunk: Chunk) -> Self { VirtualMachine { chunk, stack: Vec::new() } }

    // In the book, the printing is a side-effect. That's not very testable. From a performance
    // point of view, there's nothing interesting about avoiding logs, so let's always do it.
    // (Where's that lazy Writer monad when you need it, amirite?)
    pub fn disassemble(mut self) -> Result<Vec<TracedCommand>, VmResult> {
        let mut result = Vec::new();
        let mut index: usize = 0;
        let mut previous_line: Line = 0;
        let Chunk { code, constants } = self.chunk;
        for (op, line) in code {
            let prefix = format!(
                "{:>4}",
                if index > 0 && line == previous_line {
                    "   |".to_owned()
                } else {
                    line.to_string()
                },
            );

            macro_rules! binary {
                ($l:tt) => {{
                    let v1 = try_number(&self.stack.pop().unwrap(), stringify!($l), &line)?;
                    let v2 = try_number_mut(self.stack.last_mut().unwrap(), stringify!($l), &line)?;
                    *v2 $l v1;
                    "".to_owned()
                }}
            }
            let command = format!("{} {}{}", prefix, op.to_upper_snake(), match op {
                OpCode::Return => "".to_owned(),
                OpCode::Constant(ptr) => {
                    let value = constants.get(ptr).unwrap();
                    self.stack.push(Value::Number(*value));
                    format!(" {} '{}'", ptr, value)
                }
                OpCode::Bool(bool) => {
                    self.stack.push(Value::Bool(bool));
                    format!("'{}'", bool)
                }
                OpCode::Nil => {
                    self.stack.push(Value::Nil);
                    format!("nil")
                }
                OpCode::Equals => {
                    let v1 = self.stack.pop().unwrap();
                    let v2 = self.stack.last_mut().unwrap();
                    *v2 = Value::Bool(match (&v1, &v2) {
                        (Value::Number(f1), Value::Number(f2)) => f1 == f2,
                        (Value::Bool(b1), Value::Bool(b2)) => b1 == b2,
                        (Value::Nil, Value::Nil) => true,
                        _ => false,
                    });
                    "".to_owned()
                }
                OpCode::Greater => {
                    let v1 = try_number(&self.stack.pop().unwrap(), "Greater lhs", &line)?;
                    let v2 = try_number_mut(self.stack.last_mut().unwrap(), "Greater rhs", &line)?;
                    *(self.stack.last_mut().unwrap()) = Value::Bool(v1 < *v2);
                    "".to_owned()
                }
                OpCode::Less => {
                    let v1 = try_number(&self.stack.pop().unwrap(), "Less lhs", &line)?;
                    let v2 = try_number_mut(self.stack.last_mut().unwrap(), "Less rhs", &line)?;
                    *(self.stack.last_mut().unwrap()) = Value::Bool(v1 > *v2);
                    "".to_owned()
                }
                OpCode::Add => {
                    binary!(+=)
                }
                OpCode::Subtract => {
                    binary!(-=)
                }
                OpCode::Multiply => {
                    binary!(*=)
                }
                OpCode::Divide => {
                    binary!(/=)
                }
                OpCode::Negate => {
                    let v = try_number_mut(self.stack.last_mut().unwrap(), "Negate", &line)?;
                    *v *= -1.0;
                    "".to_owned()
                }
                OpCode::Not => {
                    let v = self.stack.last_mut().unwrap();
                    let result = match &v {
                        Value::Nil => true,
                        Value::Bool(false) => true,
                        _ => false,
                    };
                    *v = Value::Bool(result);
                    "".to_owned()
                }
            });
            result.push(TracedCommand::new(command, self.stack.clone()));

            index += 1;
            previous_line = line;
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use crate::assert_eq_vec;
    use crate::rslox::compiled::chunk::OpCode;
    use crate::rslox::compiled::tests::unsafe_parse;

    use super::*;

    fn final_res(lines: Vec<&str>) -> Value {
        let stack = VirtualMachine::new(unsafe_parse(lines)).disassemble().unwrap();
        let e = &stack.last().unwrap().stack_state;
        assert_eq!(e.len(), 1);
        e.last().unwrap().clone()
    }

    fn single_error(lines: Vec<&str>) -> VmResult {
        VirtualMachine::new(unsafe_parse(lines)).disassemble().unwrap_err()
    }

    #[test]
    fn basic_bytecode() {
        let mut chunks = Chunk::new();
        let constant = chunks.add_constant(1.2);
        chunks.write(OpCode::Constant(constant), 123);

        chunks.write(OpCode::Negate, 124);
        chunks.write(OpCode::Return, 124);

        assert_eq!(
            VirtualMachine::new(chunks).disassemble().unwrap(),
            vec![
                TracedCommand::new(" 123 OP_CONSTANT      0 '1.2'", vec![Value::Number(1.2)]),
                TracedCommand::new(" 124 OP_NEGATE       ", vec![Value::Number(-1.2)]),
                TracedCommand::new("   | OP_RETURN       ", vec![Value::Number(-1.2)]),
            ]
        )
    }

    #[test]
    fn binary_op() {
        let mut chunks = Chunk::new();
        let constant = chunks.add_constant(1.0);
        chunks.write(OpCode::Constant(constant), 123);

        let constant = chunks.add_constant(2.0);
        chunks.write(OpCode::Constant(constant), 123);

        chunks.write(OpCode::Add, 123);


        let constant = chunks.add_constant(6.0);
        chunks.write(OpCode::Constant(constant), 123);

        chunks.write(OpCode::Divide, 123);
        chunks.write(OpCode::Negate, 123);
        chunks.write(OpCode::Return, 123);

        assert_eq_vec!(
            VirtualMachine::new(chunks).disassemble().unwrap(),
            vec![
                TracedCommand::new(" 123 OP_CONSTANT      0 '1'", vec![Value::Number(1.0)]),
                TracedCommand::new("   | OP_CONSTANT      1 '2'", vec![Value::Number(1.0), Value::Number(2.0)]),
                TracedCommand::new("   | OP_ADD          ", vec![Value::Number(3.0)]),
                TracedCommand::new("   | OP_CONSTANT      2 '6'", vec![Value::Number(3.0), Value::Number(6.0)]),
                TracedCommand::new("   | OP_DIVIDE       ", vec![Value::Number(0.5)]),
                TracedCommand::new("   | OP_NEGATE       ", vec![Value::Number(-0.5)]),
                TracedCommand::new("   | OP_RETURN       ", vec![Value::Number(-0.5)]),
            ]
        )
    }

    #[test]
    fn trivial_precedence_final() {
        assert_eq!(
            final_res(vec![
                "-1+2.5"
            ]),
            Value::Number(1.5),
        )
    }

    #[test]
    fn precedence_final() {
        assert_eq!(
            final_res(vec![
                "-1*-3+2/-4"
            ]),
            Value::Number(2.5),
        )
    }

    #[test]
    fn precedence_parens() {
        assert_eq!(
            final_res(vec![
                "-1*-(3+2)/-4"
            ]),
            Value::Number(-1.25),
        )
    }

    #[test]
    fn basic_run_time_error() {
        assert_eq!(
            single_error(vec![
                "-false",
            ]).line(),
            1,
        )
    }

    #[test]
    fn single_bang() {
        assert_eq!(
            final_res(vec![
                "!false",
            ]),
            Value::Bool(true),
        )
    }

    #[test]
    fn multiple_bang() {
        assert_eq!(
            final_res(vec![
                "!!!!true",
            ]),
            Value::Bool(true),
        )
    }

    #[test]
    fn not_equal() {
        assert_eq!(
            final_res(vec![
                "3 != 4",
            ]),
            Value::Bool(true),
        )
    }

    #[test]
    fn greater_equals() {
        assert_eq!(
            final_res(vec![
                "3 >= 4",
            ]),
            Value::Bool(false),
        )
    }

    #[test]
    fn less() {
        assert_eq!(
            final_res(vec![
                "-5 < -4",
            ]),
            Value::Bool(true),
        )
    }

    #[test]
    fn complex_equality() {
        assert_eq!(
            final_res(vec![
                "!(5 - 4 > 3 * 2 == !nil)",
            ]),
            Value::Bool(true),
        )
    }
}