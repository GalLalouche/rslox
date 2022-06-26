use crate::rslox::compiled::chunk::{Chunk, OpCode, Value};

#[derive(Debug, Copy, Clone, PartialEq)]
enum InterpretResult {
    CompileError,
    RuntimeError,
}

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
    pub fn disassemble(&mut self) -> Result<Vec<TracedCommand>, InterpretResult> {
        let mut result = Vec::new();
        let mut index = 0;
        for (op, line) in &self.chunk.code {
            let prefix = format!(
                "{:>4}",
                if index > 0 && *line == self.chunk.get(index - 1).unwrap().1 {
                    "   |".to_owned()
                } else {
                    line.to_string()
                },
            );

            macro_rules! binary {
                ($l:tt) => {{
                    let v1 = self.stack.pop().unwrap();
                    *self.stack.last_mut().unwrap() $l v1;
                    "".to_owned()
                }}
            }
            let command = format!("{} {}{}", prefix, op.to_upper_snake(), match op {
                OpCode::Return => "".to_owned(),
                OpCode::Constant(ptr) => {
                    let value = self.chunk.get_constant(ptr).unwrap();
                    self.stack.push(value);
                    format!(" {} '{}'", ptr, value)
                }
                OpCode::Add => {
                    binary!(+=)
                }
                OpCode::Substract => {
                    binary!(-=)
                }
                OpCode::Multiply => {
                    binary!(*=)
                }
                OpCode::Divide => {
                    binary!(/=)
                }
                OpCode::Negate => {
                    *self.stack.last_mut().unwrap() *= -1.0;
                    "".to_owned()
                }
            });
            index += 1;
            result.push(self.with_stack_state(command));
        }
        Ok(result)
    }

    fn with_stack_state<S: Into<String>>(&self, str: S) -> TracedCommand {
        TracedCommand::new(str, self.stack.clone())
    }
}

#[cfg(test)]
mod tests {
    use crate::assert_eq_vec;
    use crate::rslox::compiled::chunk::OpCode;

    use super::*;

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
                TracedCommand::new(" 123 OP_CONSTANT      0 '1.2'", vec![1.2]),
                TracedCommand::new(" 124 OP_NEGATE       ", vec![-1.2]),
                TracedCommand::new("   | OP_RETURN       ", vec![-1.2]),
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
                TracedCommand::new(" 123 OP_CONSTANT      0 '1'", vec![1.0]),
                TracedCommand::new("   | OP_CONSTANT      1 '2'", vec![1.0, 2.0]),
                TracedCommand::new("   | OP_ADD          ", vec![3.0]),
                TracedCommand::new("   | OP_CONSTANT      2 '6'", vec![3.0, 6.0]),
                TracedCommand::new("   | OP_DIVIDE       ", vec![0.5]),
                TracedCommand::new("   | OP_NEGATE       ", vec![-0.5]),
                TracedCommand::new("   | OP_RETURN       ", vec![-0.5]),
            ]
        )
    }
}
