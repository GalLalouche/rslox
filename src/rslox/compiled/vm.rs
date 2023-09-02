use std::borrow::ToOwned;
use std::collections::{HashMap, HashSet, VecDeque};
use std::convert::TryInto;
use std::io::Write;
use std::ops::Deref;
use std::rc::Rc;

use nonempty::NonEmpty;

use crate::rslox::common::utils::{RcRc, rcrc, Truncateable};
use crate::rslox::compiled::chunk::{Chunk, InternedString, InternedStrings};
use crate::rslox::compiled::code::Line;
use crate::rslox::compiled::gc::{GcWeak, GcWeakMut};
use crate::rslox::compiled::op_code::{OpCode, StackLocation};
use crate::rslox::compiled::value::{Function, Upvalue, Value};

type FunctionName = String;

#[derive(Debug, Clone, PartialEq, Eq)]
struct VmError {
    msg: String,
    stack_trace: Box<VecDeque<(FunctionName, Line)>>,
}

impl VmError {
    pub fn new(msg: String, function_name: FunctionName, line: Line) -> Self {
        let mut stack_trace: VecDeque<(FunctionName, Line)> = Default::default();
        stack_trace.push_back((function_name, line));
        VmError { msg, stack_trace: Box::new(stack_trace) }
    }
    pub fn prepend(&mut self, function_name: FunctionName, line: Line) {
        self.stack_trace.push_back((function_name, line));
    }
}

#[derive(Debug, Clone)]
struct VirtualMachine {
    frames: NonEmpty<CallFrame>,
}

impl VirtualMachine {
    pub fn run(chunk: Chunk, writer: &mut impl Write) -> Result<Vec<Value>, VmError> {
        let name = Rc::new("<script>".to_owned());
        let script = Rc::new(Function { name: GcWeak::from(&name), arity: 0, chunk });
        let stack: RcRc<Vec<Value>> = Default::default();
        let globals: RcRc<HashMap<String, Value>> = Default::default();
        let upvalues = GcWeakMut::null();
        let top_frame = CallFrame::new(
            0 as InstructionPointer,
            (&script).into(),
            0 as StackLocation,
            upvalues, // upvalues can be empty since we
            stack.clone(),
            globals,
        );
        let mut vm = VirtualMachine { frames: NonEmpty::new(top_frame) };
        while vm.unfinished() {
            match vm.go(writer) {
                Err(ref mut err) => {
                    for f in vm.frames.iter().rev().skip(1) {
                        err.prepend(f.name(), f.current_line())
                    }
                    return Err(err.clone());
                }
                _ => (),
            }
        }
        Ok(stack.take())
    }

    fn go(&mut self, writer: &mut impl Write) -> Result<(), VmError> {
        if self.frames.len() > MAX_FRAMES {
            let active_frame = self.frames.last();
            let line = active_frame.current_line();
            return Err(VmError::new(
                "Stack overflow! Wheeeee!".to_owned(),
                active_frame.function.unwrap_upgrade().name.to_owned(),
                line,
            ));
        }
        self.frames.last_mut().run(writer).map(|maybe_cf| match maybe_cf {
            None => {
                if let Some(stack_index) = self.frames.pop().map(|f| f.stack_index) {
                    self.frames.last_mut().stack.borrow_mut().truncate(stack_index);
                }
            }
            Some(cf) => self.frames.push(cf),
        })
    }

    fn unfinished(&self) -> bool { self.frames.last().unfinished() }

    fn _debug_stack(&self) -> () {
        self.frames.first()._debug_stack();
    }
}

type InstructionPointer = usize;

#[derive(Debug, Clone)]
struct CallFrameInternedStrings {
    original: GcWeak<InternedStrings>,
    working: InternedStrings,
}

impl CallFrameInternedStrings {
    pub fn new(original: GcWeak<InternedStrings>) -> Self {
        CallFrameInternedStrings { original, working: HashSet::new() }
    }

    pub fn get_or_insert(&mut self, str: Rc<String>) -> GcWeak<String> {
        GcWeak::from(self.original.unwrap_upgrade().get(str.deref()).unwrap_or_else(|| {
            self.working.get_or_insert(str)
        }))
    }
}

#[derive(Debug, Clone)]
struct CallFrame {
    ip: InstructionPointer,
    interned_strings: CallFrameInternedStrings,
    function: GcWeak<Function>,
    stack: RcRc<Vec<Value>>,
    upvalues: GcWeakMut<Vec<GcWeakMut<Value>>>,
    globals: RcRc<HashMap<String, Value>>,
    stack_index: usize,
}

static MAX_FRAMES: usize = 10000;

impl CallFrame {
    pub fn name(&self) -> String { self.function.unwrap_upgrade().name.to_owned() }
    pub fn new(
        ip: InstructionPointer,
        function: GcWeak<Function>,
        stack_index: StackLocation,
        upvalues: GcWeakMut<Vec<GcWeakMut<Value>>>,
        stack: RcRc<Vec<Value>>,
        globals: RcRc<HashMap<String, Value>>,
    ) -> Self {
        let interned_strings = CallFrameInternedStrings::new(
            function.clone().unwrap_upgrade().chunk.get_interned_strings());
        CallFrame {
            ip,
            interned_strings,
            function,
            stack,
            upvalues,
            globals,
            stack_index,
        }
    }
    pub fn current_line(&self) -> Line {
        self.function.unwrap_upgrade().chunk.get_code().get(self.ip).unwrap().1
    }
    pub fn unfinished(&self) -> bool {
        self.ip < self.function.unwrap_upgrade().chunk.get_code().len()
    }
    pub fn run(&mut self, writer: &mut impl Write) -> Result<Option<CallFrame>, VmError> {
        let chunk = &self.function.unwrap_upgrade().chunk;
        while self.ip < chunk.get_code().len() {
            if let Some(cf) = self.next(writer)? {
                return Ok(Some(cf));
            }
        }
        Ok(None)
    }

    fn next(&mut self, writer: &mut impl Write) -> Result<Option<CallFrame>, VmError> {
        let chunk = &self.function.unwrap_upgrade().chunk;
        let code = chunk.get_code();
        let instructions = code.instructions();
        let stack = self.stack.clone();
        let globals = self.globals.clone();
        let (op, line) = instructions.get(self.ip).unwrap();
        macro_rules! binary {
                ($l:tt) => {{
                    let v1 =
                        self.try_number(&stack.borrow_mut().pop().unwrap(), stringify!($l), *line)?;
                    self.update_top_number(stringify!($l), *line, |n| n $l v1)
                }}
            }
        match op {
            OpCode::Return => {
                let len = self.stack.borrow().len();
                // Patch return value
                self.stack.borrow_mut().swap(self.stack_index - 1, len - 1);
                self.ip = instructions.len() + 1;
                return Ok(None);
            }
            OpCode::Pop => { stack.borrow_mut().pop().unwrap(); }
            OpCode::PopN(n) => {
                let len = stack.borrow().len();
                assert!(len >= *n);
                stack.borrow_mut().popn(*n);
            }
            OpCode::Print => {
                let expr = stack.borrow_mut().pop().unwrap();
                write!(writer, "{}", expr.stringify()).expect("Not written");
            }
            OpCode::Number(num) => stack.borrow_mut().push(Value::Number(*num)),
            OpCode::Function(i, upvalues) => {
                let mut upvalues_ptrs = Vec::new();
                for Upvalue { index, is_local } in upvalues {
                    let fixed_index = self.stack_index + *index;
                    if *is_local {
                        let existing = std::mem::replace(
                            &mut self.stack.borrow_mut()[fixed_index], Value::Nil);
                        let rc = rcrc(existing);
                        self.stack.borrow_mut()[fixed_index] = Value::OpenUpvalue(rc.clone());
                        upvalues_ptrs.push(GcWeakMut::from(&rc));
                    } else {
                        todo!()
                    }
                }
                stack.borrow_mut().push(
                    Value::Closure(chunk.get_function(*i), rcrc(upvalues_ptrs)));
            }
            OpCode::CloseUpvalue => { /* TODO */ }
            OpCode::UnpatchedJump =>
                panic!("Jump should have been patched at line: '{}'", line),
            OpCode::JumpIfFalse(index) => {
                assert!(*index > self.ip, "Jump target '{}' was smaller than ip '{}'", index, self.ip);
                let should_skip = stack.borrow_mut().pop().unwrap().is_falsey();
                if should_skip {
                    self.ip = *index - 1; // ip will increase by one after we exit this pattern match.
                }
            }
            OpCode::Jump(index) =>
                self.ip = *index - 1, // ip will increase by one after we exit this pattern match.
            OpCode::GetGlobal(name) => {
                let rc = name.unwrap_upgrade();
                let value = globals.borrow().get(rc.deref()).cloned().ok_or_else(
                    || self.err(format!("Unrecognized identifier '{}'", rc), *line))?;
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
            OpCode::GetUpvalue(index) =>
                stack.borrow_mut().push(
                    Value::upvalue_ptr(self.upvalues.unwrap_upgrade().borrow()[*index].clone())),

            OpCode::SetUpvalue(index) => {
                // We don't pop on assignment, to allow for chaining.
                let value = stack.borrow().last().cloned().unwrap();
                self.upvalues.unwrap_upgrade().borrow_mut()[*index].unwrap_upgrade().replace(value);
            }
            OpCode::DefineLocal(index) =>
                (*stack.borrow_mut().get_mut(*index).unwrap()) =
                    stack.borrow().last().unwrap().clone(),
            OpCode::GetLocal(index) => {
                let value = stack.borrow().get(*index + self.stack_index).unwrap().clone();
                stack.borrow_mut().push(value)
            }
            OpCode::SetLocal(index) => {
                // We don't pop on assignment, to allow for chaining.
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
                let v1 = self.try_number(&stack.borrow_mut().pop().unwrap(), "Greater lhs", *line)?;
                let v2 = self.try_number(
                    &stack.borrow().last().cloned().unwrap(), "Greater rhs", *line)?;
                *(stack.borrow_mut().last_mut().unwrap()) = Value::Bool(v2 > v1);
            }
            OpCode::Less => {
                let v1 = self.try_number(&stack.borrow_mut().pop().unwrap(), "Less lhs", *line)?;
                let v2 = self.try_number(
                    &stack.borrow().last().cloned().unwrap(), "Less rhs", *line)?;
                *(stack.borrow_mut().last_mut().unwrap()) = Value::Bool(v2 < v1);
            }
            OpCode::Call(arg_count) => {
                let func_index = stack.borrow().len() - arg_count - 1;
                let value = stack.borrow().get(func_index).cloned().unwrap();
                let (function, upvalues): (GcWeak<Function>, GcWeakMut<Vec<GcWeakMut<Value>>>) =
                    (&value).try_into().map_err(|err: String| self.err(err, *line))?;
                let arity = function.unwrap_upgrade().arity;
                if arity != *arg_count {
                    return Err(self.err(
                        format!("Expected {} arguments but got {}", arity, arg_count),
                        *line));
                }
                self.ip += 1;
                return Ok(Some(CallFrame::new(
                    0 as InstructionPointer,
                    function,
                    stack.borrow().len() - arity as StackLocation,
                    upvalues,
                    stack.clone(),
                    globals.clone(),
                )));
            }
            OpCode::Add =>
                if stack.borrow().last().unwrap().is_string() {
                    let popped = &stack.borrow_mut().pop().unwrap();
                    let s1: InternedString = TryInto::<InternedString>::try_into(popped).unwrap();
                    let s2: InternedString =
                        TryInto::<InternedString>::try_into(stack.borrow().last().unwrap())
                            .map_err(|err|
                                self.err(format!("{} ({})", err, "String concat"), *line))?;
                    let result = self.interned_strings.get_or_insert(Rc::new(
                        format!("{}{}", *s2.unwrap_upgrade(), *s1.unwrap_upgrade())));
                    *(stack.borrow_mut().last_mut().unwrap()) = Value::String(result);
                } else {
                    binary!(+)?
                },
            OpCode::Subtract => binary!(-)?,
            OpCode::Multiply => binary!(*)?,
            OpCode::Divide => binary!(/)?,
            OpCode::Negate => self.update_top_number("Negate", *line, |v| v * -1.0)?,
            OpCode::Not => {
                let result = stack.borrow().last().unwrap().is_falsey();
                *stack.borrow_mut().last_mut().unwrap() = Value::Bool(result)
            }
        };
        self.ip += 1;
        Ok(None)
    }

    fn err(&self, msg: String, line: Line) -> VmError {
        VmError::new(msg, self.function.unwrap_upgrade().name.to_owned(), line)
    }

    fn try_number(&self, value: &Value, msg: &str, line: Line) -> Result<f64, VmError> {
        value.try_into().map_err(|err: String| self.err(format!("{} ({})", err, msg), line))
    }

    // Updates the to value of the stack to be the new number.
    fn update_top_number(
        &mut self,
        msg: &str,
        line: Line,
        f: impl FnOnce(f64) -> f64,
    ) -> Result<(), VmError> {
        let n = self.stack.borrow().last().unwrap().try_into()
            .map_err(|err: String| self.err(format!("{} ({})", err, msg), line))?;
        *self.stack.borrow_mut().last_mut().unwrap() = Value::Number(f(n));
        Ok(())
    }

    fn _debug_stack(&self) -> () {
        let stack = &self.stack;
        eprintln!("stack for {}:", self.function.unwrap_upgrade().name.unwrap_upgrade());
        for (i, value) in stack.borrow().iter().enumerate() {
            eprintln!("{:0>2}: {}", i, value.stringify())
        }
    }
}

// Copies all interned data locally.
#[cfg(test)]
mod tests {
    use std::io::{Cursor, sink};

    use crate::assert_eq_vec;
    use crate::rslox::common::utils::SliceExt;
    use crate::rslox::compiled::op_code::OpCode;
    use crate::rslox::compiled::tests::unsafe_compile;

    use super::*;

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
                Value::Closure(..) => panic!("Closures don't have a traced value"),
                Value::UpvaluePtr(..) => panic!("Upvalues don't have a traced value"),
                Value::OpenUpvalue(..) => panic!("Upvalues don't have a traced value"),
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


    fn final_res(lines: Vec<&str>) -> TracedValue {
        let mut compiled = unsafe_compile(lines);
        // // Comment this in for debugging the compiled program.
        // eprintln!("disassembled:\n{}", crate::rslox::compiled::compiler::disassemble(&compiled).join("\n"));
        let code = compiled.get_code();
        // Remove the final POP to ensure the stack isn't empty
        assert_eq!(code.last().unwrap().0, OpCode::Pop);
        compiled.pop();
        let stack = VirtualMachine::run(compiled, &mut sink()).unwrap();
        stack.unwrap_single().into()
    }

    fn printed_string(lines: Vec<&str>) -> String {
        let mut buff = Cursor::new(Vec::new());
        let chunk = unsafe_compile(lines);
        // // Comment this in for debugging the compiled program.
        // eprintln!("disassembled:\n{}", crate::rslox::compiled::compiler::disassemble(&chunk).join("\n"));
        VirtualMachine::run(chunk, &mut buff).unwrap();
        buff.get_ref().into_iter().map(|i| *i as char).collect()
    }

    fn assert_printed(code: &str, expected: &str) {
        assert_eq!(printed_string(vec![code]), expected)
    }

    fn single_error(code: &str) -> VmError {
        VirtualMachine::run(unsafe_compile(vec![code.trim()]), &mut sink()).unwrap_err()
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
            single_error("-false;").stack_trace.unwrap_single().1,
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
        assert_printed(r#"print "abc" + "def";"#, "abcdef")
    }

    #[test]
    fn stack_is_empty_after_statement() {
        let stack = VirtualMachine::run(unsafe_compile(vec!["1 + 2;"]), &mut sink()).unwrap();
        assert_eq!(stack.len(), 0);
    }

    #[test]
    fn basic_variable_access() {
        assert_printed(r#"
var x = 4;
print x;
"#,
                       "4",
        )
    }

    #[test]
    fn global_variable_redeclaration() {
        assert_printed(r#"
var x = 4;
print x;
var x = 2;
print x;
"#,
                       "42",
        )
    }

    #[test]
    fn global_variable_assignment() {
        assert_printed(r#"
var x = 4;
print x;
x = 2;
print x;
        "#,
                       "42",
        )
    }

    #[test]
    fn local_variable_assignment() {
        assert_printed(r#"
{
  var x = 4;
  print x;
  x = 2;
  print x;
}
        "#,
                       "42",
        )
    }

    #[test]
    fn chaining_assignment() {
        assert_printed(r#"
var x = 1;
{
  var y = 2;
  var z = 3;
  y = x = z = 4;
  print x;
  print y;
  print z;
}
        "#,
                       "444",
        )
    }

    #[test]
    fn local_variables() {
        assert_printed(r#"
var x = 2;
{
  var x = 4;
  print x;
}
print x;
        "#,
                       "42",
        )
    }

    #[test]
    fn get_local_order() {
        assert_printed(r#"
{
  var x = 1;
  var y = 2;
  var z = 3;
  print x;
  print y;
  print z;
}
        "#,
                       "123",
        )
    }

    #[test]
    fn get_global_order() {
        assert_printed(r#"
var x = 1;
var y = 2;
var z = 3;
print x;
print y;
print z;
        "#,
                       "123",
        )
    }

    #[test]
    fn local_variable_order_operation() {
        assert_printed(r#"
{
  var x = 1;
  var y = 2;
  print x - y;
}
        "#,
                       "-1",
        )
    }

    #[test]
    fn if_true_no_else() {
        assert_printed(r#"
var x = 2;
if (x) {
  print 42;
}
        "#,
                       "42",
        )
    }

    #[test]
    fn if_false_no_else() {
        assert_printed(r#"
var x = 2;
if (!x)
  print 42;

        "#,
                       "",
        )
    }

    #[test]
    fn if_true_else() {
        assert_printed(r#"
var x = 2;
if (x) {
  print 42;
} else
  print 2;
        "#,
                       "42",
        )
    }

    #[test]
    fn multi_line_if() {
        assert_printed(r#"
var x = 2;
if (x) {
  y = 42;
  z = x + y;
  print z * 3;
}
z = 15;
print z * x;
        "#,
                       "13230",
        )
    }

    #[test]
    fn multi_line_if_false() {
        assert_printed(r#"
var x = 2;
if (x < 0) {
  y = 42;
  z = x + y;
  print z * 3;
}
z = 15;
print z * x;
        "#,
                       "30",
        )
    }

    #[test]
    fn if_false_else() {
        assert_printed(r#"
var x = 2;
if (!x)
  print 42;
else { print 54; }
        "#,
                       "54",
        )
    }

    #[test]
    fn while_loop() {
        assert_printed(r#"
var x = 0;
while (x < 3) {
  print x;
  x = x + 1;
}
        "#,
                       "012",
        )
    }

    #[test]
    fn for_loop() {
        assert_printed(r#"
for (var x = 0; x < 3; x = x + 1) {
  print x;
}
        "#,
                       "012",
        )
    }

    #[test]
    fn for_loop_no_init() {
        assert_printed(r#"
var x = 0;
for (; x < 3; x = x + 1) {
  print x;
}
        "#,
                       "012",
        )
    }

    #[test]
    fn for_loop_no_post() {
        assert_printed(r#"
for (var x = 0; x < 3;) {
  print x;
  x = x + 1;
}
        "#,
                       "012",
        )
    }

    #[test]
    fn for_loop_no_init_no_post() {
        assert_printed(r#"
var x = 0;
for (;x < 3;) {
  print x;
  x = x + 1;
}
        "#,
                       "012",
        )
    }

    #[test]
    fn printing_a_function_value() {
        assert_printed(r#"
fun areWeHavingItYet() {
  print "Yes we are!";
}
print areWeHavingItYet;
        "#,
                       "<fn areWeHavingItYet>",
        )
    }

    #[test]
    fn calling_a_function() {
        assert_printed(r#"
fun areWeHavingItYet() {
  print "Yes we are!";
}
areWeHavingItYet();
        "#,
                       "Yes we are!",
        )
    }

    #[test]
    fn calling_a_function_with_local_computation() {
        assert_printed(r#"
fun areWeHavingItYet() {
  var x = 1;
  var y = 2;
  print x + y;
}
areWeHavingItYet();
        "#,
                       "3",
        )
    }

    #[test]
    fn nested_functions() {
        assert_printed(r#"
fun areWeHavingItYet() {
  fun one() {
    var x = 1;
    var y = 2;
    print x + y;
  }
  fun two() {
    var x = 10;
    var y = 20;
    print x * y;
  }
  one();
  two();
}
areWeHavingItYet();
        "#,
                       "3200",
        )
    }

    #[test]
    fn calling_a_function_with_arguments() {
        assert_printed(r#"
fun areWeHavingItYet(x, y) {
  var z = "3";
  print x + y + z;
}
var x = "1";
var z = "2";
areWeHavingItYet(x, z);
        "#,
                       "123",
        )
    }

    #[test]
    fn user_error_on_not_enough_arguments() {
        assert_eq!(
            single_error(r#"
fun areWeHavingItYet(x, y) {
  var z = "3";
  print x + y + z;
}
areWeHavingItYet();
"#).stack_trace.unwrap_single().1,
            5,
        )
    }

    #[test]
    fn user_error_on_stack_overflow() {
        assert_eq!(
            single_error(r#"
fun foo() {
  foo();
}
foo();
"#).msg,
            "Stack overflow! Wheeeee!".to_owned(),
        )
    }

    #[test]
    fn prints_stack_trace_on_error() {
        let err = single_error(
            r#"
fun a() { b(); }
fun b() { c(); }
fun c() {
  c("too", "many");
}
a();
"#);
        assert_eq!(err.msg, "Expected 0 arguments but got 2");
        let vec: Vec<(FunctionName, Line)> = Vec::from(err.stack_trace.deref().clone());
        assert_eq_vec!(
            vec,
            vec![
                ("c".to_owned(), 4 as usize),
                ("b".to_owned(), 2 as usize),
                ("a".to_owned(), 1 as usize),
                ("<script>".to_owned(), 6 as usize),
            ],
        )
    }

    #[test]
    fn manual_factorial() {
        assert_printed(r#"
fun a(x) {
  return x * b(x - 1);
}
fun b(x) {
  return x * c(x - 1);
}
fun c(x) {
  return 1;
}
print a(2);
        "#,
                       "2",
        )
    }

    #[test]
    fn functions_calling_functions_calling_functions_hard() {
        assert_printed(r#"
fun a(x) {
  b(x + x, x * x);
  b(x - x, x / x);
}
fun b(x, y) {
  c(x * y, x + y, x - y);
  c(x, y, x / y);
}
fun c(x, y, z) {
  print x;
  print y;
  print z;
}
a(1);
        "#,
                       "23121201-1010",
        )
    }

    #[test]
    fn implicit_function_return() {
        assert_printed(r#"
fun a(x) {
  print x * x;
}
print a(16);
        "#,
                       "256nil",
        )
    }

    #[test]
    fn implicit_function_return2() {
        assert_printed(r#"
fun a(x) {
  print x * x;
}
res = a(16);
print res;
        "#,
                       "256nil",
        )
    }

    #[test]
    fn basic_explicit_return() {
        assert_printed(r#"
fun plus() {
  return 42;
}
print plus();
        "#,
                       "42",
        )
    }

    #[test]
    fn basic_explicit_return_with_args() {
        assert_printed(r#"
fun plus(x, y) {
  return x + y;
}
print plus(10, 20);
        "#,
                       "30",
        )
    }

    #[test]
    fn factorial_0() {
        assert_printed(r#"
fun factorial(x) {
  if (x == 0) {return 1;}
  else {return x * factorial(x - 1);}
}
print factorial(0);
        "#,
                       "1",
        )
    }

    #[test]
    fn factorial_1() {
        assert_printed(r#"
fun factorial(x) {
  if (x == 0) {return 1;}
  else {return x * factorial(x - 1);}
}
print factorial(1);
        "#,
                       "1",
        )
    }

    #[test]
    fn factorial_5() {
        assert_printed(r#"
fun factorial(x) {
  if (x == 0) {return 1;}
  else {return x * factorial(x - 1);}
}
print factorial(5);
        "#,
                       "120",
        )
    }

    #[test]
    fn factorial_5_early_exit() {
        assert_printed(r#"
fun factorial(x) {
  if (x == 0) {
    return 1;
  }
  return x * factorial(x - 1);
}
print factorial(5);
        "#,
                       "120",
        )
    }

    #[test]
    fn fib() {
        assert_printed(r#"
fun fib(x) {
  if (x < 2) {return x;}
  return fib(x - 1) + fib(x - 2);
}
print fib(10);
        "#,
                       "55",
        )
    }

    #[test]
    fn functions_returning_functions_no_closure() {
        assert_printed(r#"
fun f() {
  print "f1";
  fun g() {
    print "g";
  }
  print "f2";
  return g;
}
f()();
        "#,
                       "f1f2g",
        )
    }

    #[test]
    fn basic_function_closure() {
        assert_printed(r#"
{
  var x = 42;
  fun foo() {
    print x;
  }
  foo();
}
        "#,
                       "42",
        )
    }

    #[test]
    fn basic_function_set_closure() {
        assert_printed(r#"
{
  var x = 42;
  fun foo() {
    x = 1;
  }
  foo();
  print x;
}
        "#,
                       "1",
        )
    }

    #[test]
    fn basic_function_set_from_get_closure() {
        assert_printed(r#"
{
  var x = 42;
  fun foo() {
    x = x + 1;
  }
  foo();
  print x;
}
        "#,
                       "43",
        )
    }

    #[test]
    fn nested_function_closure() {
        assert_printed(r#"
fun foo(x) {
  fun bar() {
    print x;
  }
  bar();
}
foo(42);
        "#,
                       "42",
        )
    }
}
