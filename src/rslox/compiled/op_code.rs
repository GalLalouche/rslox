use nonempty::NonEmpty;

use crate::rslox::compiled::chunk::InternedString;
use crate::rslox::compiled::tests::DeepEq;
use crate::rslox::compiled::value::Upvalue;

pub type CodeLocation = usize;
pub type StackLocation = usize;
pub type ConstantIndex = usize;
pub type LocalCount = usize;
// including parameters
pub type ArgCount = usize;

#[derive(Debug, Clone, PartialEq)]
pub enum OpCode {
    Return,
    Pop,
    // A more efficient variant of the above, used by function returns.
    PopN(usize),
    Print,
    Function(ConstantIndex),
    Upvalues(NonEmpty<Upvalue>),
    DefineGlobal(InternedString),
    DefineLocal(StackLocation),
    Number(f64),
    Bool(bool),
    // since std::String is already heap managed, we don't need a separate pointer here.
    // Hurray for real languages!
    // While "Weak", this is never expected to actually point to null as Strings are only
    // "uninterested" when garbage collected.
    String(InternedString),
    GetGlobal(InternedString),
    SetGlobal(InternedString),
    GetUpvalue(StackLocation),
    SetUpvalue(StackLocation),
    GetLocal(StackLocation),
    SetLocal(StackLocation),
    Nil,
    Call(ArgCount),
    Add,
    Subtract,
    Multiply,
    Divide,
    Negate,
    Not,
    Equals,
    Less,
    Greater,
    UnpatchedJump,
    Jump(CodeLocation),
    JumpIfFalse(CodeLocation),
}

impl Eq for &OpCode {}

impl DeepEq for OpCode {
    fn deep_eq(&self, other: &Self) -> bool {
        match (&self, &other) {
            (OpCode::DefineGlobal(s1), OpCode::DefineGlobal(s2)) =>
                s1.unwrap_upgrade() == s2.unwrap_upgrade(),
            (OpCode::GetGlobal(s1), OpCode::GetGlobal(s2)) =>
                s1.unwrap_upgrade() == s2.unwrap_upgrade(),
            (OpCode::String(s1), OpCode::String(s2)) =>
                s1.unwrap_upgrade() == s2.unwrap_upgrade(),
            _ => self == other
        }
    }
}

impl OpCode {
    pub fn to_upper_snake(&self) -> String {
        format!("{:15}", match self {
            OpCode::Return => "RETURN",
            OpCode::Pop => "POP",
            OpCode::PopN(_) => "POP_N",
            OpCode::Print => "PRINT",
            OpCode::Function(_) => "FUNCTION",
            OpCode::Upvalues(_) => "UPVALUE",
            OpCode::DefineGlobal(_) => "DEFINE_GLOBAL",
            OpCode::DefineLocal(_) => "DEFINE_LOCAL",
            OpCode::Number(_) => "NUMBER",
            OpCode::Bool(_) => "BOOL",
            OpCode::String(_) => "STRING",
            OpCode::GetGlobal(_) => "GET_GLOBAL",
            OpCode::SetGlobal(_) => "SET_GLOBAL",
            OpCode::GetUpvalue(_) => "GET_UPVALUE",
            OpCode::SetUpvalue(_) => "SET_UPVALUE",
            OpCode::GetLocal(_) => "GET_LOCAL",
            OpCode::SetLocal(_) => "SET_LOCAL",
            OpCode::Nil => "NIL",
            OpCode::Add => "ADD",
            OpCode::Call(_) => "CALL",
            OpCode::Subtract => "SUBTRACT",
            OpCode::Multiply => "MULTIPLY",
            OpCode::Divide => "DIVIDE",
            OpCode::Negate => "NEGATE",
            OpCode::Not => "NOT",
            OpCode::Equals => "EQUALS",
            OpCode::Less => "LESS",
            OpCode::Greater => "GREATER",
            OpCode::UnpatchedJump => "UNPATCHED_JUMP",
            OpCode::Jump(_) => "JUMP",
            OpCode::JumpIfFalse(_) => "JUMP_IF_FALSE",
        })
    }
}

