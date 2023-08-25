use std::cell::RefCell;
use std::collections::HashMap;
use std::convert::TryInto;
use std::io::Write;
use std::ops::Deref;
use std::rc::Rc;
use std::stringify;

use crate::rslox::compiled::chunk::{Chunk, InternedString};
use crate::rslox::compiled::code::Line;
use crate::rslox::compiled::gc::GcWeak;
use crate::rslox::compiled::op_code::OpCode;
use crate::rslox::compiled::value::{Function, Value};

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

#[derive(Debug, Clone)]
struct VirtualMachine {
    script: Function,
}

type InstructionPointer = usize;

#[derive(Debug)]
struct CallFrame {
    function: GcWeak<Function>,
    globals: Rc<RefCell<HashMap<String, Value>>>,
    stack: Rc<RefCell<Vec<Value>>>,
    stack_index: usize,
}

impl CallFrame {
    // Returns the final stack value
    pub fn run(self, writer: &mut impl Write) -> Result<(), VmError> {
        let chunk = &self.function.unwrap_upgrade().chunk;
        // TODO find a better way than copying
        let mut interned_strings = chunk.get_interned_strings().clone();
        let code = chunk.get_code();
        let instructions = code.instructions();
        let mut ip: InstructionPointer = 0;
        let stack = self.stack;
        let globals = self.globals;
        while ip < instructions.len() {
            let (op, line) = instructions.get(ip).unwrap();
            macro_rules! binary {
                ($l:tt) => {{
                    let v1 = try_number(&stack.borrow_mut().pop().unwrap(), stringify!($l), &line)?;
                    *(try_number_mut(
                        stack.borrow_mut().last_mut().unwrap(), stringify!($l), &line))? $l v1;
                }}
            }
            match op {
                OpCode::Return => (),
                OpCode::Pop => { stack.borrow_mut().pop().unwrap(); }
                OpCode::Print => {
                    let expr = stack.borrow_mut().pop().unwrap();
                    write!(writer, "{}", expr.stringify()).expect("Not written");
                }
                OpCode::Number(num) => stack.borrow_mut().push(Value::Number(*num)),
                OpCode::Function(i) =>
                    stack.borrow_mut().push(Value::Function(chunk.get_function(*i))),
                OpCode::UnpatchedJump =>
                    panic!("Jump should have been patched at line: '{}'", line),
                OpCode::JumpIfFalse(index) => {
                    assert!(*index > ip, "Jump target '{}' was smaller than ip '{}'", index, ip);
                    let should_skip = stack.borrow_mut().pop().unwrap().is_falsey();
                    if should_skip {
                        ip = *index - 1; // ip will increase by one after we exit this pattern match.
                    }
                }
                OpCode::Jump(index) =>
                    ip = *index - 1, // ip will increase by one after we exit this pattern match.
                OpCode::GetGlobal(name) => {
                    let rc = name.unwrap_upgrade();
                    let value = globals.borrow().get(rc.deref()).cloned()
                        .ok_or(VmError(format!("Unrecognized identifier '{}'", rc), *line))?;
                    stack.borrow_mut().push(value.clone());
                }
                OpCode::DefineGlobal(name) => {
                    let value = stack.borrow_mut().pop().unwrap();
                    globals.borrow_mut().insert(name.unwrap_upgrade().deref().to_owned(), value);
                }
                OpCode::SetGlobal(name) => {
                    // We not pop on assignment, to allow for chaining.
                    let value = stack.borrow().last().cloned().unwrap();
                    globals.borrow_mut().insert(name.unwrap_upgrade().deref().to_owned(), value.clone());
                }
                OpCode::DefineLocal(index) =>
                    (*stack.borrow_mut().get_mut(*index).unwrap()) =
                        stack.borrow().last().unwrap().clone(),
                OpCode::GetLocal(index) => {
                    let value = stack.borrow().get(*index + self.stack_index).unwrap().clone();
                    stack.borrow_mut().push(value)
                }
                OpCode::SetLocal(index) => {
                    // We not pop on assignment, to allow for chaining.
                    let value = stack.borrow().last().cloned().unwrap();
                    *stack.borrow_mut().get_mut(*index + self.stack_index).unwrap() = value.clone();
                }
                OpCode::Bool(bool) => stack.borrow_mut().push(Value::Bool(*bool)),
                OpCode::Nil => stack.borrow_mut().push(Value::Nil),
                OpCode::String(s) => stack.borrow_mut().push(Value::String(s.clone())),
                OpCode::Equals => {
                    let v1 = stack.borrow_mut().pop().unwrap();
                    let old_v2 = stack.borrow().last().cloned().unwrap();
                    *stack.borrow_mut().last_mut().unwrap() = Value::Bool(v1 == old_v2);
                }
                OpCode::Greater => {
                    let v1 = try_number(&stack.borrow_mut().pop().unwrap(), "Greater lhs", &line)?;
                    let v2 =
                        try_number(&stack.borrow().last().cloned().unwrap(), "Greater rhs", &line)?;
                    *(stack.borrow_mut().last_mut().unwrap()) = Value::Bool(v2 > v1);
                }
                OpCode::Less => {
                    let v1 = try_number(&stack.borrow_mut().pop().unwrap(), "Less lhs", &line)?;
                    let v2 =
                        try_number(&stack.borrow().last().cloned().unwrap(), "Less rhs", &line)?;
                    *(stack.borrow_mut().last_mut().unwrap()) = Value::Bool(v2 < v1);
                }
                OpCode::Call => {
                    let last = stack.borrow().last().cloned().unwrap();
                    match last {
                        Value::Function(f) => {
                            let frame = CallFrame {
                                function: f,
                                stack_index: stack.borrow().len(),
                                stack: stack.clone(),
                                globals: globals.clone(),
                            };
                            frame.run(writer)?;
                        }
                        v => {
                            return Err(VmError(
                                format!("Expected function, but got '{}'", v.stringify()),
                                *line));
                        }
                    }
                }
                OpCode::Add =>
                    if stack.borrow().last().unwrap().is_string() {
                        let popped = &stack.borrow_mut().pop().unwrap();
                        let s1: InternedString = TryInto::<InternedString>::try_into(popped).unwrap();
                        let s2: InternedString =
                            TryInto::<InternedString>::try_into(stack.borrow().last().unwrap())
                                .map_err(|err| VmError(
                                    format!("{} ({})", err, "String concat"),
                                    *line,
                                ))?;
                        let result = interned_strings.get_or_insert(Rc::new(
                            format!("{}{}", *s2.unwrap_upgrade(), *s1.unwrap_upgrade())));
                        *(stack.borrow_mut().last_mut().unwrap()) = Value::String(result.into());
                    } else {
                        binary!(+=)
                    },
                OpCode::Subtract => binary!(-=),
                OpCode::Multiply => binary!(*=),
                OpCode::Divide => binary!(/=),
                OpCode::Negate =>
                    *try_number_mut(stack.borrow_mut().last_mut().unwrap(), "Negate", &line)? *=
                        -1.0,
                OpCode::Not => {
                    let result = stack.borrow().last().unwrap().is_falsey();
                    *stack.borrow_mut().last_mut().unwrap() = Value::Bool(result)
                }
            };
            ip += 1;
        }
        Ok(())
    }
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
            Value::Function(f_) => {
                let f = f_.unwrap_upgrade();
                TracedValue::Function {
                    name: f.name.to_owned(),
                    arity: f.arity,
                    chunk: f.chunk.clone(),
                }
            }
        }
    }
}

impl TracedValue {
    pub fn _string<S: Into<String>>(str: S) -> Self {
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
        let script_name: Rc<String> = Rc::from("<script>".to_owned());
        let script = Function {
            name: GcWeak::from(&script_name),
            arity: 0,
            chunk: program,
        };
        VirtualMachine { script }
    }

    pub fn run(self, writer: &mut impl Write) -> Result<Vec<Value>, VmError> {
        let rc_script = Rc::from(self.script);
        let stack: Rc<RefCell<Vec<Value>>> = Default::default();
        let globals: Rc<RefCell<HashMap<String, Value>>> = Default::default();
        let top_frame = CallFrame {
            function: GcWeak::from(&rc_script),
            globals: globals.clone(),
            stack: stack.clone(),
            stack_index: 0,
        };
        top_frame.run(writer)?;
        Ok(stack.take())
    }

    #[cfg(test)]
    fn _disassemble(self) -> String {
        let mut result = Vec::new();
        result.append(&mut VirtualMachine::_disassemble_chunk(&self.script.chunk));
        result.join("\n")
    }

    #[cfg(test)]
    fn _disassemble_chunk(chunk: &Chunk) -> Vec<String> {
        let mut previous_line: Line = 0;
        let mut is_first = true;
        let mut result = Vec::new();
        for (i, (op, line)) in chunk.get_code().iter().enumerate() {
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
                OpCode::UnpatchedJump => panic!("Jump should have been patched at line: '{}'", line),
                OpCode::JumpIfFalse(index) => format!("{}", index),
                OpCode::Jump(index) => format!("{}", index),
                OpCode::Function(i) => format!("{}", i),
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
                OpCode::Divide | OpCode::Negate | OpCode::Not | OpCode::Call => "".to_owned(),
            });
            result.push(command);
            previous_line = *line;
            is_first = false;
        }
        for i in 0..chunk.function_count() {
            let function = chunk.get_function(i);
            result.push(
                "fun ".to_owned() + function.unwrap_upgrade().name.unwrap_upgrade().deref() + ":");
            result.append(
                &mut VirtualMachine::_disassemble_chunk(&function.unwrap_upgrade().chunk));
            result.push(function.unwrap_upgrade().name.to_owned() + " <end>");
        }
        result
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
        let code = compiled.get_code();
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
        // eprintln!("disassembled:\n{}", vm.clone()._disassemble());
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
    fn get_local_order() {
        assert_eq!(
            printed_string(vec![
                "{",
                "  var x = 1;",
                "  var y = 2;",
                "  var z = 3;",
                "  print x;",
                "  print y;",
                "  print z;",
                "}",
            ]),
            "123",
        )
    }

    #[test]
    fn get_global_order() {
        assert_eq!(
            printed_string(vec![
                "var x = 1;",
                "var y = 2;",
                "var z = 3;",
                "print x;",
                "print y;",
                "print z;",
            ]),
            "123",
        )
    }

    #[test]
    fn local_variable_order_operation() {
        assert_eq!(
            printed_string(vec![
                "{",
                "  var x = 1;",
                "  var y = 2;",
                "  print x - y;",
                "}",
            ]),
            "-1",
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

    #[test]
    fn calling_a_function() {
        assert_eq!(
            printed_string(vec![
                "fun areWeHavingItYet() {",
                "  print \"Yes we are!\";",
                "}",
                "areWeHavingItYet();",
            ]),
            "Yes we are!",
        )
    }

    #[test]
    fn calling_a_function_with_local_computation() {
        assert_eq!(
            printed_string(vec![
                "fun areWeHavingItYet() {",
                "  var x = 1;",
                "  var y = 2;",
                "  print x + y;",
                "}",
                "areWeHavingItYet();",
            ]),
            "3",
        )
    }

    #[test]
    fn nested_functions() {
        assert_eq!(
            printed_string(vec![
                "fun areWeHavingItYet() {",
                "  fun one() {",
                "    var x = 1;",
                "    var y = 2;",
                "    print x + y;",
                "  }",
                "  fun two() {",
                "    var x = 10;",
                "    var y = 20;",
                "    print x * y;",
                "  }",
                "  one();",
                "  two();",
                "}",
                "areWeHavingItYet();",
            ]),
            "3200",
        )
    }
}