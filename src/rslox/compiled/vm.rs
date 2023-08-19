use std::collections::HashMap;
use std::convert::TryInto;
use std::io::Write;
use std::ops::Deref;
use std::rc::Rc;
use std::stringify;

use crate::rslox::compiled::chunk::{Chunk, InternedString};
use crate::rslox::compiled::code::Line;
use crate::rslox::compiled::op_code::OpCode;
use crate::rslox::compiled::value::Value;

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

#[derive(Debug, Default)]
struct VirtualMachine {
    program: Chunk,
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
    Function { name: String, arity: usize, chunk: Chunk },
}

impl From<&Value> for TracedValue {
    fn from(v: &Value) -> Self {
        match v {
            Value::Number(n) => TracedValue::Number(*n),
            Value::Bool(b) => TracedValue::Bool(*b),
            Value::Nil => TracedValue::Nil,
            Value::String(s) => TracedValue::String(s.unwrap_upgrade().deref().to_owned()),
            Value::Function(f) => TracedValue::Function {
                name: f.name.to_owned(),
                arity: f.arity,
                chunk: f.chunk.clone(),
            }
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

impl VirtualMachine {
    pub fn new(program: Chunk) -> Self {
        VirtualMachine { program, ..Default::default() }
    }

    #[cfg(test)]
    fn disassemble(self) -> String {
        let mut result = Vec::new();
        let mut previous_line: Line = 0;
        let mut is_first = true;
        for (i, (op, line)) in self.program.get_code().iter().enumerate() {
            let prefix = format!(
                "{:0>2}: {:>2}",
                i,
                if !is_first && line == &previous_line {
                    " |".to_owned()
                } else {
                    line.to_string()
                },
            );

            let command: String = format!("{} {}{}", prefix, op.to_upper_snake(), match op {
                OpCode::Number(num) => format!("{}", num),
                OpCode::Function(f) => format!("{}", f.stringify()),
                OpCode::UnpatchedJump => panic!("Jump should have been patched at line: '{}'", line),
                OpCode::JumpIfFalse(index) => format!("{}", index),
                OpCode::Jump(index) => format!("{}", index),
                OpCode::GetGlobal(name) => format!("'{}'", name.unwrap_upgrade()),
                OpCode::DefineGlobal(name) => format!("'{}'", name.unwrap_upgrade()),
                OpCode::SetGlobal(name) => format!("'{}'", name.unwrap_upgrade()),
                OpCode::DefineLocal(index) => format!("{}", index),
                OpCode::GetLocal(index) => format!("{}", index),
                OpCode::SetLocal(index) => format!("{}", index),
                OpCode::Bool(bool) => format!("{}", bool),
                OpCode::String(s) => format!("'{}'", s.unwrap_upgrade()),
                OpCode::Return | OpCode::Pop | OpCode::Print | OpCode::Nil | OpCode::Equals |
                OpCode::Greater | OpCode::Less | OpCode::Add | OpCode::Subtract | OpCode::Multiply |
                OpCode::Divide | OpCode::Negate | OpCode::Not => "".to_owned(),
            });
            result.push(command);
            previous_line = *line;
            is_first = false;
        }
        result.join("\n")
    }

    // Returns the final stack value
    pub fn run(mut self, writer: &mut impl Write) -> Result<Vec<Value>, VmError> {
        let (code, mut interned_strings) = self.program.to_tuple();
        let instructions = code.instructions();
        let mut ip: usize = 0;
        while ip < instructions.len() {
            let (op, line) = instructions.get(ip).unwrap();
            macro_rules! binary {
                ($l:tt) => {{
                    let v1 = try_number(&self.stack.pop().unwrap(), stringify!($l), &line)?;
                    let v2 = try_number_mut(self.stack.last_mut().unwrap(), stringify!($l), &line)?;
                    *v2 $l v1;
                }}
            }
            match op {
                OpCode::Return => (),
                OpCode::Pop => { self.stack.pop().unwrap(); }
                OpCode::Print => {
                    let expr = self.stack.pop().unwrap();
                    write!(writer, "{}", expr.stringify()).expect("Not written");
                }
                OpCode::Number(num) => self.stack.push(Value::Number(*num)),
                OpCode::Function(f) => self.stack.push(Value::Function(f.clone())),
                OpCode::UnpatchedJump =>
                    panic!("Jump should have been patched at line: '{}'", line),
                OpCode::JumpIfFalse(index) => {
                    assert!(*index > ip, "Jump target '{}' was smaller than ip '{}'", index, ip);
                    let should_skip = self.stack.pop().unwrap().is_falsey();
                    if should_skip {
                        ip = *index - 1; // ip will increase by one after we exit this pattern match.
                    }
                }
                OpCode::Jump(index) =>
                    ip = *index - 1, // ip will increase by one after we exit this pattern match.
                OpCode::GetGlobal(name) => {
                    let rc = name.unwrap_upgrade();
                    let value = self.globals.get(rc.deref())
                        .ok_or(VmError(format!("Unrecognized identifier '{}'", rc), *line))?;
                    self.stack.push(value.clone());
                }
                OpCode::DefineGlobal(name) => {
                    let value = self.stack.pop().unwrap();
                    self.globals.insert(name.unwrap_upgrade().deref().to_owned(), value);
                }
                OpCode::SetGlobal(name) => {
                    // We not pop on assignment, to allow for chaining.
                    let value = self.stack.last().unwrap();
                    self.globals.insert(name.unwrap_upgrade().deref().to_owned(), value.clone());
                }
                OpCode::DefineLocal(index) =>
                    (*self.stack.get_mut(*index).unwrap()) = self.stack.last().unwrap().clone(),
                OpCode::GetLocal(index) => self.stack.push(self.stack.get(*index).unwrap().clone()),
                OpCode::SetLocal(index) => {
                    // We not pop on assignment, to allow for chaining.
                    let value = self.stack.last().unwrap();
                    *self.stack.get_mut(*index).unwrap() = value.clone();
                }
                OpCode::Bool(bool) => self.stack.push(Value::Bool(*bool)),
                OpCode::Nil => self.stack.push(Value::Nil),
                OpCode::String(s) => self.stack.push(Value::String(s.clone())),
                OpCode::Equals => {
                    let v1 = self.stack.pop().unwrap();
                    let v2 = self.stack.last_mut().unwrap();
                    *v2 = Value::Bool(&v1 == v2);
                }
                OpCode::Greater => {
                    let v1 = try_number(&self.stack.pop().unwrap(), "Greater lhs", &line)?;
                    let v2 = try_number_mut(self.stack.last_mut().unwrap(), "Greater rhs", &line)?;
                    *(self.stack.last_mut().unwrap()) = Value::Bool(*v2 > v1);
                }
                OpCode::Less => {
                    let v1 = try_number(&self.stack.pop().unwrap(), "Less lhs", &line)?;
                    let v2 = try_number_mut(self.stack.last_mut().unwrap(), "Less rhs", &line)?;
                    *(self.stack.last_mut().unwrap()) = Value::Bool(*v2 < v1);
                }
                OpCode::Add =>
                    if self.stack.last().unwrap().is_string() {
                        let popped = &self.stack.pop().unwrap();
                        let s1: InternedString = TryInto::<InternedString>::try_into(popped).unwrap();
                        let s2: InternedString =
                            TryInto::<InternedString>::try_into(self.stack.last().unwrap())
                                .map_err(|err| VmError(
                                    format!("{} ({})", err, "String concat"),
                                    *line,
                                ))?;
                        let result = interned_strings.get_or_insert(Rc::new(
                            format!("{}{}", *s2.unwrap_upgrade(), *s1.unwrap_upgrade())));
                        *(self.stack.last_mut().unwrap()) = Value::String(result.into());
                    } else {
                        binary!(+=)
                    },
                OpCode::Subtract => binary!(-=),
                OpCode::Multiply => binary!(*=),
                OpCode::Divide => binary!(/=),
                OpCode::Negate =>
                    *try_number_mut(self.stack.last_mut().unwrap(), "Negate", &line)? *= -1.0,
                OpCode::Not =>
                    *self.stack.last_mut().unwrap() =
                        Value::Bool(self.stack.last_mut().unwrap().is_falsey()),
            };
            ip += 1;
        }
        Ok(self.stack)
    }
}

#[cfg(test)]
mod tests {
    use std::io::{Cursor, sink};

    use crate::rslox::common::utils::SliceExt;
    use crate::rslox::compiled::op_code::OpCode;
    use crate::rslox::compiled::tests::unsafe_compile;

    use super::*;

    fn final_res(lines: Vec<&str>) -> TracedValue {
        // Remove the final POP to ensure the stack isn't empty
        let mut compiled = unsafe_compile(lines);
        let mut code = compiled.get_code();
        assert!(match code.get(code.len() - 2).unwrap().0 {
            OpCode::Pop => true,
            _ => false
        });
        compiled.remove(code.len() - 2);
        let stack = VirtualMachine::new(compiled).run(&mut sink()).unwrap();
        // Last is return, which as an empty, because second from last is pop, which will also end
        // with an empty stack.
        stack.unwrap_single().into()
    }

    fn printed_string(lines: Vec<&str>) -> String {
        let mut buff = Cursor::new(Vec::new());
        let vm = VirtualMachine::new(unsafe_compile(lines));
        // // Comment this in for debugging the compiled program.
        // use std::iter::Enumerate;
        // use std::slice::Iter;
        // use crate::rslox::common::utils::debug_mk_string;
        // eprintln!("disassembled:\n{}", vm.disassemble());
        vm.run(&mut buff).unwrap();
        buff.get_ref().into_iter().map(|i| *i as char).collect()
    }

    fn single_error(lines: Vec<&str>) -> VmError {
        VirtualMachine::new(unsafe_compile(lines)).run(&mut sink()).unwrap_err()
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
        let stack = VirtualMachine::new(unsafe_compile(vec!["1 + 2;"])).run(&mut sink()).unwrap();
        assert_eq!(stack.len(), 0);
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

    #[test]
    fn printing_a_function_value() {
        assert_eq!(
            printed_string(vec![
                "fun areWeHavingItYet() {",
                "  print \"Yes we are!\";",
                "}",
                "print areWeHavingItYet;",
            ]),
            "<fn areWeHavingItYet>",
        )
    }
}