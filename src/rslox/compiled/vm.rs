use std::collections::HashMap;
use std::convert::TryInto;
use std::io::Write;
use std::ops::Deref;
use std::rc::Rc;
use std::stringify;

use crate::rslox::compiled::chunk::{Chunk, GcWeak, Line, OpCode, Value};

#[derive(Debug, Clone, PartialEq, Eq)]
struct VmError(String, Line);

fn try_number(value: &Value, msg: &str, line: &Line) -> Result<f64, VmError> {
    let f: &f64 =
        value.try_into().map_err(|err: String| VmError(format!("{} ({})", err, msg), *line))?;
    Ok(*f)
}

fn try_number_mut<'a>(value: &'a mut Value, msg: &str, line: &Line) -> Result<&'a mut f64, VmError> {
    value.try_into().map_err(|err: String| VmError(format!("{} ({})", err, msg), *line))
}

#[derive(Debug)]
struct VirtualMachine {
    chunk: Chunk,
    stack: Vec<Value>,
    globals: HashMap<String, Value>,
}

// Copies all interned data locally.
#[derive(Debug, Clone, PartialEq)]
pub enum TracedValue {
    Number(f64),
    Bool(bool),
    Nil,
    String(String),
}

impl From<&Value> for TracedValue {
    fn from(v: &Value) -> Self {
        match v {
            Value::Number(n) => TracedValue::Number(*n),
            Value::Bool(b) => TracedValue::Bool(*b),
            Value::Nil => TracedValue::Nil,
            Value::String(s) => TracedValue::String(s.unwrap_upgrade().deref().to_owned()),
        }
    }
}

impl TracedValue {
    pub fn string<S: Into<String>>(str: S) -> Self {
        TracedValue::String(str.into())
    }
}

#[derive(Debug, Clone, PartialEq)]
struct TracedCommand {
    assembly: String,
    stack_state: Vec<TracedValue>,
}

impl TracedCommand {
    pub fn new<S: Into<String>>(assembly: S, stack_state: Vec<TracedValue>) -> Self {
        TracedCommand { assembly: assembly.into(), stack_state }
    }
}

impl VirtualMachine {
    pub fn new(chunk: Chunk) -> Self {
        VirtualMachine { chunk, stack: Vec::new(), globals: HashMap::new() }
    }

    // In the book, the printing is a side-effect. That's not very testable. From a performance
    // point of view, there's nothing interesting about avoiding logs, so let's always do it.
    // (Where's that lazy Writer monad when you need it, amirite?)
    pub fn disassemble(mut self, writer: &mut impl Write) -> Result<Vec<TracedCommand>, VmError> {
        let mut result = Vec::new();
        let mut previous_line: Line = 0;
        let Chunk { code, number_constants: constants, mut interned_strings, .. } = self.chunk;
        let mut ip: usize = 0;
        while ip < code.len() {
            let (op, line) = code.get(ip).unwrap();
            let prefix = format!(
                "{:>4}",
                if ip > 0 && line == &previous_line {
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
                OpCode::Pop => {
                    self.stack.pop().unwrap();
                    "".to_owned()
                }
                OpCode::Print => {
                    let expr = self.stack.pop().unwrap();
                    write!(writer, "{}", expr.stringify()).expect("Not written");
                    "".to_owned()
                }
                OpCode::Constant(ptr) => {
                    let value = constants.get(*ptr).unwrap();
                    self.stack.push(Value::Number(*value));
                    format!(" {} '{}'", ptr, value)
                }
                OpCode::UnpatchedJump => {
                    panic!("Jump should have been patched at line: '{}'", line)
                }
                OpCode::JumpIfFalse(index) => {
                    assert!(*index > ip, "Jump target '{}' was smaller than ip '{}'", index, ip);
                    let should_skip = self.stack.pop().unwrap().is_falsey();
                    if should_skip {
                        ip = *index - 1; // ip will increase by one after we exit this pattern match.
                    }
                    format!("{}", index)
                }
                OpCode::Jump(index) => {
                    ip = *index - 1; // ip will increase by one after we exit this pattern match.
                    format!("{}", index)
                }
                OpCode::GetGlobal(name) => {
                    let rc = name.unwrap_upgrade();
                    let value = self.globals.get(rc.deref())
                        .ok_or(VmError(format!("Unrecognized identifier '{}'", rc), *line))?;
                    self.stack.push(value.clone());
                    format!("'{}'", name.unwrap_upgrade())
                }
                OpCode::DefineGlobal(name) => {
                    let value = self.stack.pop().unwrap();
                    self.globals.insert(name.unwrap_upgrade().deref().to_owned(), value);
                    format!("'{}'", name.unwrap_upgrade())
                }
                OpCode::SetGlobal(name) => {
                    // We not pop on assignment, to allow for chaining.
                    let value = self.stack.last().unwrap();
                    self.globals.insert(name.unwrap_upgrade().deref().to_owned(), value.clone());
                    format!("'{}'", name.unwrap_upgrade())
                }
                OpCode::DefineLocal(index) => {
                    (*self.stack.get_mut(*index).unwrap()) = self.stack.last().unwrap().clone();
                    format!("{}", index)
                }
                OpCode::GetLocal(index) => {
                    self.stack.push(self.stack.get(*index).unwrap().clone());
                    format!("{}", index)
                }
                OpCode::SetLocal(index) => {
                    // We not pop on assignment, to allow for chaining.
                    let value = self.stack.last().unwrap();
                    *self.stack.get_mut(*index).unwrap() = value.clone();
                    format!("{}", index)
                }
                OpCode::Bool(bool) => {
                    self.stack.push(Value::Bool(*bool));
                    format!("'{}'", bool)
                }
                OpCode::Nil => {
                    self.stack.push(Value::Nil);
                    format!("nil")
                }
                OpCode::String(s) => {
                    let result = format!("'{}'", s.unwrap_upgrade());
                    self.stack.push(Value::String(s.clone()));
                    result
                }
                OpCode::Equals => {
                    let v1 = self.stack.pop().unwrap();
                    let v2 = self.stack.last_mut().unwrap();
                    *v2 = Value::Bool(&v1 == v2);
                    "".to_owned()
                }
                OpCode::Greater => {
                    let v1 = try_number(&self.stack.pop().unwrap(), "Greater lhs", &line)?;
                    let v2 = try_number_mut(self.stack.last_mut().unwrap(), "Greater rhs", &line)?;
                    *(self.stack.last_mut().unwrap()) = Value::Bool(*v2 > v1);
                    "".to_owned()
                }
                OpCode::Less => {
                    let v1 = try_number(&self.stack.pop().unwrap(), "Less lhs", &line)?;
                    let v2 = try_number_mut(self.stack.last_mut().unwrap(), "Less rhs", &line)?;
                    *(self.stack.last_mut().unwrap()) = Value::Bool(*v2 < v1);
                    "".to_owned()
                }
                OpCode::Add => {
                    if self.stack.last().unwrap().is_string() {
                        let popped = &self.stack.pop().unwrap();
                        let s1: GcWeak<String> = TryInto::<GcWeak<String>>::try_into(popped).unwrap();
                        let s2: GcWeak<String> =
                            TryInto::<GcWeak<String>>::try_into(self.stack.last().unwrap())
                                .map_err(|err| VmError(
                                    format!("{} ({})", err, "String concat"),
                                    *line,
                                ))?;
                        let result = interned_strings.get_or_insert(Rc::new(
                            format!("{}{}", *s2.unwrap_upgrade(), *s1.unwrap_upgrade())));
                        *(self.stack.last_mut().unwrap()) = Value::String(result.into());
                        "".to_owned()
                    } else {
                        binary!(+=)
                    }
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
                    *v = Value::Bool(v.is_falsey());
                    "".to_owned()
                }
            });
            result.push(TracedCommand::new(
                command,
                self.stack
                    .iter()
                    .map(|v| Into::<TracedValue>::into(v))
                    .collect(),
            ));

            previous_line = *line;
            ip += 1;
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use std::io::{Cursor, sink};

    use crate::assert_eq_vec;
    use crate::rslox::common::utils::SliceExt;
    use crate::rslox::compiled::chunk::OpCode;
    use crate::rslox::compiled::tests::unsafe_parse;

    use super::*;

    fn final_res(lines: Vec<&str>) -> TracedValue {
        let stack = VirtualMachine::new(unsafe_parse(lines)).disassemble(&mut sink()).unwrap();
        // Last is return, which as an empty, because second from last is pop, which will also end
        // with an empty stack.
        let third_from_last = &stack.get(stack.len() - 3).unwrap();
        third_from_last.stack_state.clone().unwrap_single().clone()
    }

    fn printed_string(lines: Vec<&str>) -> String {
        let mut buff = Cursor::new(Vec::new());
        let parsed = unsafe_parse(lines);
        // // Comment this in for debugging the compiled program.
        // use std::iter::Enumerate;
        // use std::slice::Iter;
        // use crate::rslox::common::utils::debug_mk_string;
        // eprintln!(
        //     "parsed:\n{}",
        //     debug_mk_string(&parsed.code.iter().enumerate().collect::<Vec<_>>()),
        // );
        VirtualMachine::new(parsed).disassemble(&mut buff).unwrap();
        buff.get_ref().into_iter().map(|i| *i as char).collect()
    }

    fn single_error(lines: Vec<&str>) -> VmError {
        VirtualMachine::new(unsafe_parse(lines)).disassemble(&mut sink()).unwrap_err()
    }

    #[test]
    fn basic_bytecode() {
        let mut chunks = Chunk::new();
        let constant = chunks.add_constant(1.2);
        chunks.write(OpCode::Constant(constant), 123);

        chunks.write(OpCode::Negate, 124);
        chunks.write(OpCode::Return, 124);

        assert_eq!(
            VirtualMachine::new(chunks).disassemble(&mut sink()).unwrap(),
            vec![
                TracedCommand::new(" 123 OP_CONSTANT      0 '1.2'", vec![TracedValue::Number(1.2)]),
                TracedCommand::new(" 124 OP_NEGATE       ", vec![TracedValue::Number(-1.2)]),
                TracedCommand::new("   | OP_RETURN       ", vec![TracedValue::Number(-1.2)]),
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
            VirtualMachine::new(chunks).disassemble(&mut sink()).unwrap(),
            vec![
                TracedCommand::new(" 123 OP_CONSTANT      0 '1'", vec![TracedValue::Number(1.0)]),
                TracedCommand::new("   | OP_CONSTANT      1 '2'", vec![TracedValue::Number(1.0), TracedValue::Number(2.0)]),
                TracedCommand::new("   | OP_ADD          ", vec![TracedValue::Number(3.0)]),
                TracedCommand::new("   | OP_CONSTANT      2 '6'", vec![TracedValue::Number(3.0), TracedValue::Number(6.0)]),
                TracedCommand::new("   | OP_DIVIDE       ", vec![TracedValue::Number(0.5)]),
                TracedCommand::new("   | OP_NEGATE       ", vec![TracedValue::Number(-0.5)]),
                TracedCommand::new("   | OP_RETURN       ", vec![TracedValue::Number(-0.5)]),
            ]
        )
    }

    #[test]
    fn trivial_precedence_final() {
        assert_eq!(
            final_res(vec![
                "-1+2.5;"
            ]),
            TracedValue::Number(1.5),
        )
    }

    #[test]
    fn precedence_final() {
        assert_eq!(
            final_res(vec![
                "-1*-3+2/-4;"
            ]),
            TracedValue::Number(2.5),
        )
    }

    #[test]
    fn precedence_parens() {
        assert_eq!(
            final_res(vec![
                "-1*-(3+2)/-4;"
            ]),
            TracedValue::Number(-1.25),
        )
    }

    #[test]
    fn basic_run_time_error() {
        assert_eq!(
            single_error(vec![
                "-false;",
            ]).1,
            1,
        )
    }

    #[test]
    fn single_bang() {
        assert_eq!(
            final_res(vec![
                "!false;",
            ]),
            TracedValue::Bool(true),
        )
    }

    #[test]
    fn multiple_bang() {
        assert_eq!(
            final_res(vec![
                "!!!!true;",
            ]),
            TracedValue::Bool(true),
        )
    }

    #[test]
    fn not_equal() {
        assert_eq!(
            final_res(vec![
                "3 != 4;",
            ]),
            TracedValue::Bool(true),
        )
    }

    #[test]
    fn greater_equals() {
        assert_eq!(
            final_res(vec![
                "3 >= 4;",
            ]),
            TracedValue::Bool(false),
        )
    }

    #[test]
    fn less() {
        assert_eq!(
            final_res(vec![
                "-5 < -4;",
            ]),
            TracedValue::Bool(true),
        )
    }

    #[test]
    fn complex_equality() {
        assert_eq!(
            final_res(vec![
                "!(5 - 4 > 3 * 2 == !nil);",
            ]),
            TracedValue::Bool(true),
        )
    }

    #[test]
    fn string_equality() {
        assert_eq!(
            final_res(vec![
                r#""string" == "string";"#,
            ]),
            TracedValue::Bool(true),
        )
    }

    #[test]
    fn string_concat() {
        assert_eq!(
            printed_string(vec![
                r#"print "abc" + "def";"#,
            ]),
            "abcdef",
        )
    }

    #[test]
    fn stack_is_empty_after_statement() {
        let stack: Vec<TracedCommand> = VirtualMachine::new(unsafe_parse(vec!["1 + 2;"]))
            .disassemble(&mut sink()).unwrap();
        assert_eq!(&stack.last().unwrap().stack_state.len(), &0);
    }

    #[test]
    fn basic_variable_access() {
        assert_eq!(
            printed_string(vec![
                "var x = 4;",
                "print x;",
            ]),
            "4",
        )
    }

    #[test]
    fn global_variable_redeclaration() {
        assert_eq!(
            printed_string(vec![
                "var x = 4;",
                "print x;",
                "var x = 2;",
                "print x;",
            ]),
            "42",
        )
    }

    #[test]
    fn global_variable_assignment() {
        assert_eq!(
            printed_string(vec![
                "var x = 4;",
                "print x;",
                "x = 2;",
                "print x;",
            ]),
            "42",
        )
    }

    #[test]
    fn local_variable_assignment() {
        assert_eq!(
            printed_string(vec![
                "{",
                "  var x = 4;",
                "  print x;",
                "  x = 2;",
                "  print x;",
                "}",
            ]),
            "42",
        )
    }

    #[test]
    fn chaining_assignment() {
        assert_eq!(
            printed_string(vec![
                "var x = 1;",
                "{",
                "  var y = 2;",
                "  var z = 3;",
                "  y = x = z = 4;",
                "  print x;",
                "  print y;",
                "  print z;",
                "}",
            ]),
            "444",
        )
    }

    #[test]
    fn local_variables() {
        assert_eq!(
            printed_string(vec![
                "var x = 2;",
                "{",
                "  var x = 4;",
                "  print x;",
                "}",
                "print x;",
            ]),
            "42",
        )
    }

    #[test]
    fn if_true_no_else() {
        assert_eq!(
            printed_string(vec![
                "var x = 2;",
                "if (x) {",
                "  print 42;",
                "}",
            ]),
            "42",
        )
    }

    #[test]
    fn if_false_no_else() {
        assert_eq!(
            printed_string(vec![
                "var x = 2;",
                "if (!x)",
                "  print 42;",
                "",
            ]),
            "",
        )
    }

    #[test]
    fn if_true_else() {
        assert_eq!(
            printed_string(vec![
                "var x = 2;",
                "if (x) {",
                "  print 42;",
                "} else",
                "  print 2;",
            ]),
            "42",
        )
    }

    #[test]
    fn if_false_else() {
        assert_eq!(
            printed_string(vec![
                "var x = 2;",
                "if (!x)",
                "  print 42;",
                "else { print 54; }",
            ]),
            "54",
        )
    }

    #[test]
    fn while_loop() {
        assert_eq!(
            printed_string(vec![
                "var x = 0;",
                "while (x < 3) {",
                "  print x;",
                "  x = x + 1;",
                "}",
            ]),
            "012",
        )
    }

    #[test]
    fn for_loop() {
        assert_eq!(
            printed_string(vec![
                "for (var x = 0; x < 3; x = x + 1) {",
                "  print x;",
                "}",
            ]),
            "012",
        )
    }

    #[test]
    fn for_loop_no_init() {
        assert_eq!(
            printed_string(vec![
                "var x = 0;",
                "for (; x < 3; x = x + 1) {",
                "  print x;",
                "}",
            ]),
            "012",
        )
    }

    #[test]
    fn for_loop_no_post() {
        assert_eq!(
            printed_string(vec![
                "for (var x = 0; x < 3;) {",
                "  print x;",
                "  x = x + 1;",
                "}",
            ]),
            "012",
        )
    }

    #[test]
    fn for_loop_no_init_no_post() {
        assert_eq!(
            printed_string(vec![
                "var x = 0;",
                "for (;x < 3;) {",
                "  print x;",
                "  x = x + 1;",
                "}",
            ]),
            "012",
        )
    }
}