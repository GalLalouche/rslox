use std::borrow::ToOwned;
use std::collections::{HashMap, VecDeque};
use std::convert::{TryFrom, TryInto};
use std::io::Write;
use std::ops::Deref;
use std::rc::{Rc, Weak};

use linked_list::{Cursor, LinkedList};
use nonempty::NonEmpty;

use crate::format_interned;
use crate::rslox::common::utils::{RcRc, rcrc, Truncateable};
use crate::rslox::compiled::chunk::{Chunk, Upvalue};
use crate::rslox::compiled::code::Line;
use crate::rslox::compiled::memory::{Heap, InternedString, Managed, Pointer};
use crate::rslox::compiled::op_code::{OpCode, StackLocation};
use crate::rslox::compiled::value::{Function, Instance, Mark, PointedUpvalue, Upvalues, Value};

use super::compiler::InternedStrings;

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

#[derive(Debug)]
struct VirtualMachine {
    frames: NonEmpty<CallFrame>,
}

impl VirtualMachine {
    pub fn run(
        chunk: Chunk, interned_strings: InternedStrings, writer: &mut impl Write,
    ) -> Result<Vec<Value>, VmError> {
        VirtualMachine::run_apply(chunk, interned_strings, writer, |vm| vm.frames.head.stack.take())
    }

    pub fn run_apply<A, F: FnOnce(VirtualMachine) -> A>(
        chunk: Chunk, interned_strings: InternedStrings, writer: &mut impl Write, f: F,
    ) -> Result<A, VmError> {
        let name = Managed::new("<script>".to_owned());
        let script = Rc::new(Function { name: name.ptr(), arity: 0, chunk });
        let stack: RcRc<Vec<Value>> = Default::default();
        let globals: RcRc<HashMap<InternedString, Value>> = Default::default();
        let upvalues = Upvalues::new(Vec::new());
        let open_upvalues = rcrc(LinkedList::new());
        let closed_upvalues = rcrc(Heap::default());
        let rc_interned_strings = rcrc(interned_strings);
        let objects = rcrc(Heap::default());
        let top_frame = CallFrame::new(
            0 as InstructionPointer,
            Rc::downgrade(&script),
            0 as StackLocation,
            upvalues,
            stack.clone(),
            globals,
            rc_interned_strings,
            open_upvalues,
            closed_upvalues,
            objects,
        );
        let mut vm = VirtualMachine { frames: NonEmpty::new(top_frame) };
        while vm.unfinished() {
            // I'm calling it at pretty arbitrary times, since I just want to make sure it works,
            // and I'm too lazy to implement a proper mechanism for checking the current code use.
            vm.collect_garbage();
            match vm.go(writer) {
                Err(ref mut err) => {
                    for f in vm.frames.iter().rev().skip(1) {
                        err.prepend(f.function.upgrade().unwrap().name.to_owned(), f.current_line())
                    }
                    return Err(err.clone());
                }
                _ => (),
            }
        }
        Ok(f(vm))
    }

    fn go(&mut self, writer: &mut impl Write) -> Result<(), VmError> {
        self.collect_garbage();
        if self.frames.len() > MAX_FRAMES {
            let active_frame = self.frames.last();
            let line = active_frame.current_line();
            return Err(VmError::new(
                "Stack overflow! Wheeeee!".to_owned(),
                active_frame.function.upgrade().unwrap().name.to_owned(),
                line,
            ));
        };
        let result = self.frames.last_mut().run(writer).map(|maybe_cf| match maybe_cf {
            None => {
                if let Some(stack_index) = self.frames.pop().map(|f| f.stack_index) {
                    self.frames.last_mut().stack.borrow_mut().truncate(stack_index);
                }
            }
            Some(cf) => self.frames.push(cf),
        })?;
        self.collect_garbage();
        Ok(result)
    }

    fn unfinished(&self) -> bool { self.frames.last().unfinished() }

    fn _debug_stack(&self) -> () {
        self.frames.first()._debug_stack();
    }

    fn collect_garbage(&mut self) {
        self.mark();
        self.sweep();
    }

    fn mark(&mut self) {
        let top_frame = &self.frames.head;
        for local in top_frame.stack.borrow().iter() {
            local.mark();
        }
        top_frame.function.upgrade().unwrap().chunk.mark();
        top_frame.globals.borrow().mark();
    }

    fn sweep(&mut self) {
        let top_frame = &mut self.frames.head;
        top_frame.interned_strings.borrow_mut().sweep();
        top_frame.closed_upvalues.borrow_mut().sweep();
        top_frame.objects.borrow_mut().sweep();
    }
}

type InstructionPointer = usize;

#[derive(Debug)]
struct CallFrame {
    ip: InstructionPointer,
    interned_strings: RcRc<InternedStrings>,
    function: Weak<Function>,
    stack: RcRc<Vec<Value>>,
    closure_upvalues: Upvalues,
    globals: RcRc<HashMap<InternedString, Value>>,
    open_upvalues: RcRc<LinkedList<Managed<PointedUpvalue>>>,
    closed_upvalues: RcRc<Heap<PointedUpvalue>>,
    objects: RcRc<Heap<Instance>>,
    stack_index: usize,
}

static MAX_FRAMES: usize = 100;

impl CallFrame {
    pub fn new(
        ip: InstructionPointer,
        function: Weak<Function>,
        stack_index: StackLocation,
        upvalues: Upvalues,
        stack: RcRc<Vec<Value>>,
        globals: RcRc<HashMap<InternedString, Value>>,
        interned_strings: RcRc<InternedStrings>,
        open_upvalues: RcRc<LinkedList<Managed<PointedUpvalue>>>,
        closed_upvalues: RcRc<Heap<PointedUpvalue>>,
        objects: RcRc<Heap<Instance>>,
    ) -> Self {
        CallFrame {
            ip,
            interned_strings,
            function,
            stack,
            closure_upvalues: upvalues,
            globals,
            stack_index,
            open_upvalues,
            closed_upvalues,
            objects,
        }
    }
    pub fn current_line(&self) -> Line {
        self.function.upgrade().unwrap().chunk.get_code().get(self.ip).unwrap().1
    }
    pub fn unfinished(&self) -> bool {
        self.ip < self.chunk_length()
    }
    fn chunk_length(&self) -> usize {
        self.function.upgrade().unwrap().chunk.get_code().len()
    }
    pub fn run(&mut self, writer: &mut impl Write) -> Result<Option<CallFrame>, VmError> {
        while self.ip < self.chunk_length() {
            if let Some(cf) = self.next(writer)? {
                return Ok(Some(cf));
            }
        }
        self.close_upvalues(self.stack_index);
        Ok(None)
    }

    fn next(&mut self, writer: &mut impl Write) -> Result<Option<CallFrame>, VmError> {
        let chunk = &&self.function.upgrade().unwrap().chunk;
        let code = chunk.get_code();
        let instructions = code.instructions();
        let stack = self.stack.clone();
        let globals = self.globals.clone();
        let (op, line) = instructions.get(self.ip).unwrap();
        macro_rules! binary {
                ($l:tt) => {{
                    let popped = stack.borrow_mut().pop().unwrap();
                    let v1: f64 = self.try_into_err(&popped, stringify!($l), *line)?;
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
                let upvalue_ptrs: Vec<Pointer<PointedUpvalue>> =
                    upvalues.into_iter().map(|Upvalue { index, is_local }|
                        if *is_local {
                            self.capture_upvalue(self.stack_index + *index)
                        } else {
                            let enclosing_func = &self.stack.borrow_mut()[self.stack_index - 1];
                            let enclosing_upvalues = enclosing_func.try_into_closure().unwrap().1;
                            enclosing_upvalues.get(*index)
                        }
                    ).collect();
                stack.borrow_mut().push(
                    Value::closure(
                        self.function.upgrade().unwrap().chunk.get_function(*i),
                        Upvalues::new(upvalue_ptrs),
                    ));
            }
            OpCode::Class(i) => {
                self.stack.borrow_mut().push(
                    Value::Class(self.function.upgrade().unwrap().chunk.get_class(*i)),
                )
            }
            OpCode::GetProperty(n) => {
                let instance: Pointer<Instance> = self.try_into_err(
                    &self.stack.borrow_mut().pop().unwrap(), "get_property", *line)?;
                let value = instance.apply(|i| i.get(n.clone())).ok_or(
                    self.err(format_interned!("Undefined property '{}'.", n), *line))?;
                stack.borrow_mut().push(value.clone());
            }
            OpCode::SetProperty(n) => {
                let value = self.stack.borrow_mut().pop().unwrap();
                let mut instance: Pointer<Instance> = self.try_into_err(
                    &self.stack.borrow_mut().pop().unwrap(), "set_property", *line)?;
                instance.mutate(|i| i.set(n.clone(), value.clone()));
                stack.borrow_mut().push(value);
            }
            OpCode::CloseUpvalue => {
                self.close_upvalues(self.stack_index);
                self.stack.borrow_mut().pop().unwrap();
            }
            OpCode::UnpatchedJump => panic!("Jump should have been patched at line: '{}'", line),
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
                let value = globals.borrow().get(name).cloned().ok_or_else(
                    || self.err(format_interned!("Unrecognized identifier '{}'", name), *line))?;
                stack.borrow_mut().push(value.clone());
            }
            OpCode::DefineGlobal(name) => {
                let value = stack.borrow_mut().pop().unwrap();
                globals.borrow_mut().insert(name.clone(), value);
            }
            OpCode::SetGlobal(name) => {
                // We not pop on assignment, to allow for chaining.
                let value = stack.borrow().last().cloned().unwrap();
                globals.borrow_mut().insert(name.clone(), value.clone());
            }
            OpCode::GetUpvalue(index) =>
                stack.borrow_mut().push(Value::UpvaluePtr(self.closure_upvalues.get(*index).clone())),

            OpCode::SetUpvalue(index) => {
                // We don't pop on assignment, to allow for chaining.
                let value = stack.borrow().last().cloned().unwrap();
                self.closure_upvalues.set(*index, value);
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
                let value: Value = stack.borrow().last().cloned().unwrap();
                stack.borrow_mut().get_mut(
                    *index + self.stack_index).unwrap().set(value.clone());
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
                let v1: f64 = self.try_into_err(&stack.borrow_mut().pop().unwrap(), "Greater lhs", *line)?;
                let v2: f64 = self.try_into_err(
                    &stack.borrow().last().cloned().unwrap(), "Greater rhs", *line)?;
                *(stack.borrow_mut().last_mut().unwrap()) = Value::Bool(v2 > v1);
            }
            OpCode::Less => {
                let v1: f64 = self.try_into_err(&stack.borrow_mut().pop().unwrap(), "Less lhs", *line)?;
                let v2: f64 = self.try_into_err(
                    &stack.borrow().last().cloned().unwrap(), "Less rhs", *line)?;
                *(stack.borrow_mut().last_mut().unwrap()) = Value::Bool(v2 < v1);
            }
            OpCode::Call(arg_count) => {
                let func_index = stack.borrow().len() - arg_count - 1;
                let value = stack.borrow().get(func_index).cloned().unwrap();
                if let Ok((function, upvalues)) = value.try_into_closure() {
                    let arity = &function.upgrade().unwrap().arity;
                    if arity != arg_count {
                        return Err(self.err(
                            format!("Expected {} arguments but got {}", arity, arg_count),
                            *line));
                    }
                    self.ip += 1;
                    return Ok(Some(CallFrame::new(
                        0 as InstructionPointer,
                        function,
                        stack.borrow().len() - *arity as StackLocation,
                        upvalues,
                        stack.clone(),
                        globals.clone(),
                        self.interned_strings.clone(),
                        self.open_upvalues.clone(),
                        self.closed_upvalues.clone(),
                        self.objects.clone(),
                    )));
                } else if let Ok(class) = value.try_into_class() {
                    assert_eq!(*arg_count, 0);
                    assert_eq!(func_index, stack.borrow().len() - 1);
                    let instance_ptr = self.objects.borrow_mut().push(Instance::new(class));
                    *stack.borrow_mut().last_mut().unwrap() = Value::Instance(instance_ptr);
                } else {
                    return Err(self.err(
                        format!("Expected closure or class, got {}", value.stringify()), *line));
                }
            }
            OpCode::Add =>
                if stack.borrow().last().unwrap().is_string() {
                    let popped = &stack.borrow_mut().pop().unwrap();
                    let s1: InternedString = popped.try_into().unwrap();
                    let s2: InternedString = self.try_into_err(
                        stack.borrow().last().unwrap(), "String concat", *line)?;
                    let result = self.interned_strings.borrow_mut().intern_string(
                        format_interned!("{}{}", s2, s1));
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
        // Comment this in to make errs panics, e.g., in case tests are failing when they shouldn't.
        // panic!("{} @ {}", msg, line);
        VmError::new(msg, self.function.upgrade().unwrap().name.to_owned(), line)
    }

    fn try_into_err<'a, A: TryFrom<&'a Value, Error=String>>(
        &self, value: &'a Value, location: &str, line: Line,
    ) -> Result<A, VmError> {
        value.try_into().map_err(|s| self.err(format!("{} ({})", s, location), line))
    }

    // Updates the to value of the stack to be the new number.
    fn update_top_number(
        &mut self,
        location: &str,
        line: Line,
        f: impl FnOnce(f64) -> f64,
    ) -> Result<(), VmError> {
        let n = self.try_into_err(self.stack.borrow().last().unwrap(), location, line)?;
        *self.stack.borrow_mut().last_mut().unwrap() = Value::Number(f(n));
        Ok(())
    }

    fn capture_upvalue(&mut self, index: StackLocation) -> Pointer<PointedUpvalue> {
        let mut ref_mut = self.open_upvalues.borrow_mut();
        let mut cursor = ref_mut.cursor();
        while let Some(head) = cursor.next() {
            let upvalue_index = head.as_ref().open_location();
            if upvalue_index == index {
                return head.deref().ptr();
            }
            if upvalue_index < index {
                break;
            }
        }
        let result = Managed::new(PointedUpvalue::open(index, Rc::downgrade(&self.stack)));
        cursor.prev();
        cursor.insert(result);
        cursor.next().unwrap().ptr()
    }

    fn close_upvalues(&mut self, max_stack_index: StackLocation) {
        let mut ref_mut = self.open_upvalues.borrow_mut();
        let mut cursor: Cursor<Managed<PointedUpvalue>> = ref_mut.cursor();
        while let Some(head) = cursor.peek_next() {
            let upvalue_index = head.as_ref().open_location();
            if upvalue_index < max_stack_index {
                break;
            }
            let mut next = cursor.remove().unwrap();
            next.as_ref_mut().close();
            self.closed_upvalues.borrow_mut().own(next);
        }
    }
    fn _debug_stack(&self) -> () {
        let stack = &self.stack;
        eprintln!("stack for {}:", &self.function.upgrade().unwrap().name.to_owned());
        for (i, value) in stack.borrow().iter().enumerate() {
            eprintln!("{:0>2}: {:?}", i, value.pp_debug())
        }
    }
}


// Copies all interned data locally.
#[cfg(test)]
mod tests {
    use std::convert::identity;
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
                Value::String(s) => TracedValue::String(s.to_owned()),
                Value::Instance(..) => panic!("instances don't have a traced value"),
                Value::Class(..) => panic!("Classes don't have a traced value"),
                Value::Closure(..) => panic!("Closures don't have a traced value"),
                Value::UpvaluePtr(..) => panic!("Upvalues don't have a traced value"),
                Value::TemporaryPlaceholder => panic!("TemporaryPlaceholder found!")
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
        let (mut compiled, interned_strings) = unsafe_compile(lines);
        // // Comment this in for debugging the compiled program.
        // eprintln!("disassembled:\n{}", crate::rslox::compiled::compiler::disassemble(&compiled).join("\n"));
        let code = compiled.get_code();
        // Remove the final POP to ensure the stack isn't empty
        assert_eq!(code.last().unwrap().0, OpCode::Pop);
        compiled.pop();
        let stack = VirtualMachine::run(compiled, interned_strings, &mut sink()).unwrap();
        stack.unwrap_single().into()
    }

    fn run(code: &str) -> (VirtualMachine, String) {
        let mut buff = Cursor::new(Vec::new());
        let (chunk, interned_strings) = unsafe_compile(vec![code]);
        // // Comment this in for debugging the compiled program.
        // eprintln!("disassembled:\n{}", crate::rslox::compiled::compiler::disassemble(&chunk).join("\n"));
        let vm = VirtualMachine::run_apply(chunk, interned_strings, &mut buff, identity).unwrap();
        (vm, buff.get_ref().into_iter().map(|i| *i as char).collect())
    }

    fn printed_string(code: &str) -> String { run(code).1 }

    fn assert_printed(code: &str, expected: &str) {
        assert_eq!(printed_string(code), expected)
    }

    fn single_error(code: &str) -> VmError {
        let (chunk, interned_strings) = unsafe_compile(vec![code.trim()]);
        VirtualMachine::run(chunk, interned_strings, &mut sink()).unwrap_err()
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
        let (chunk, interned_strings) = unsafe_compile(vec!["1 + 2;"]);
        let stack = VirtualMachine::run(chunk, interned_strings, &mut sink()).unwrap();
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
    fn referencing_outer_blocks() {
        assert_printed(r#"
var x = 1;
{
  var y = x + 1;
  var z = y + 1;
  print x;
  print y;
  print z;
  y = x = z = 4;
  print x;
  print y;
  print z;
}
        "#,
                       "123444",
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

    #[test]
    fn access_closed_variable_locally() {
        assert_printed(r#"
fun foo(x) {
  x = x + 1;
  fun bar() {
    x = x * 2;
  }
  fun bazz() {
    x = x + 1;
  }
  x = x + 2;
  bar();
  bazz();
  bazz();
  bar();
  print x;
}
foo(5);
        "#,
                       "36",
        )
    }

    #[test]
    fn basic_closed_upvalues() {
        assert_printed(r#"

{
  var x = 42;
  fun bar() {
    print x;
  }
  f = bar;
}
f();
        "#,
                       "42",
        )
    }

    #[test]
    fn multiple_closures() {
        assert_printed(r#"
{
  fun foo(a, b) {
    fun bar(c, d) {
        fun bazz(e, f) {
            print a + b + c + d + e + f;
        }
        return bazz("e", "f");
    }
    return bar("c", "d");
  }
  f = foo;
}
f("a", "b");
        "#,
                       "abcdef",
        )
    }

    #[test]
    fn non_local_closure() {
        assert_printed(r#"
fun foo(x) {
  fun bar() {
      fun bazz() {
        print x;
      }
      bazz();
  }
  bar();
}
foo(42);
        "#,
                       "42",
        )
    }

    #[test]
    fn upvalues_book_example() {
        assert_printed(
            r#"
fun outer() {
  var x = "outside";
  fun inner() {
    print x;
  }
  inner();
}
outer();
           "#,
            "outside",
        )
    }

    #[test]
    fn closed_upvalues_book_example() {
        assert_printed(
            r#"
fun outer() {
  var x = "outside";
  fun inner() {
    print x;
  }

  return inner;
}


closure = outer();
closure();
           "#,
            "outside",
        )
    }

    #[test]
    fn values_and_variables_book_example() {
        assert_printed(
            r#"
var globalSet;
var globalGet;

fun main() {
  var a = "initial";

  fun set() { a = "updated"; }
  fun get() { print a; }

  globalSet = set;
  globalGet = get;
}

main();
globalSet();
globalGet();
           "#,
            "updated",
        )
    }

    #[test]
    fn sharing_closures() {
        assert_printed(
            r#"
{
    fun foo(x) {
      fun bar() {
        x = x + 1;
        print x;
      }
      f = bar;
      g = bar;
    }
    foo(42);
}
f();
g();
           "#,
            "4344",
        )
    }

    #[test]
    fn basic_class_declaration() {
        assert_printed(
            r#"
class Foo {}
print Foo;
           "#,
            "Foo",
        )
    }

    #[test]
    fn basic_class_instantiation() {
        assert_printed(
            r#"
class Foo {}
print Foo();
           "#,
            "Foo instance",
        )
    }

    #[test]
    fn basic_set_and_get_property() {
        assert_printed(
            r#"
class Foo {}
foo = Foo();
foo.x = 3;
print foo.x;
           "#,
            "3",
        )
    }

    #[test]
    fn get_and_set_book_example() {
        assert_printed(
            r#"
class Pair {}

var pair = Pair();
pair.first = 1;
pair.second = 2;
print pair.first + pair.second; // 3.
           "#,
            "3",
        )
    }

    #[test]
    fn nested_getting_and_setting() {
        assert_printed(
            r#"
class Foo {}

var foo = Foo();
foo.foo = Foo();
foo.foo.x = 42;
var bar = foo.foo;
bar.y = 43;
print foo.foo.x;
print foo.foo.y;
           "#,
            "4243",
        )
    }

    #[test]
    fn setting_closures() {
        assert_printed(
            r#"
class Foo {}

var foo = Foo();
{
    fun bar(x) {
        fun bazz() {
            return x + 1;
        }
        foo.bazz = bazz;
    }
    bar(42);
}
print foo.bazz();
           "#,
            "43",
        )
    }

    #[test]
    fn cyclic_references() {
        let vm = run(
            r#"
class Foo {}

{
    var foo = Foo();
    var bar = Foo();
    foo.x = bar;
    bar.x = foo;
}
           "#,
        ).0;
        assert!(vm.frames.head.objects.take().is_empty())
    }
}
