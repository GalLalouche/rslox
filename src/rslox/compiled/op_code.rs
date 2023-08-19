use crate::rslox::compiled::chunk::InternedString;
use crate::rslox::compiled::tests::DeepEq;
use crate::rslox::compiled::value::Function;

pub type CodeLocation = usize;
pub type StackLocation = usize;

#[derive(Debug, Clone, PartialEq)]
pub enum OpCode {
    Return,
    Pop,
    Print,
    DefineGlobal(InternedString),
    DefineLocal(StackLocation),
    Number(f64),
    Bool(bool),
    Function(Function),
    // since std::String is already heap managed, we don't need a separate pointer here.
    // Hurray for real languages!
    // While "Weak", this is never expected to actually point to null as Strings are only
    // "uninterested" when garbage collected.
    String(InternedString),
    GetGlobal(InternedString),
    SetGlobal(InternedString),
    GetLocal(StackLocation),
    SetLocal(StackLocation),
    Nil,
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
            OpCode::Print => "PRINT",
            OpCode::DefineGlobal(_) => "DEFINE_GLOBAL",
            OpCode::DefineLocal(_) => "DEFINE_LOCAL",
            OpCode::Number(_) => "DEFINE_LOCAL",
            OpCode::Bool(_) => "BOOL",
            OpCode::String(_) => "STRING",
            OpCode::Function(_) => "FUNCTION",
            OpCode::GetGlobal(_) => "GET_GLOBAL",
            OpCode::SetGlobal(_) => "SET_GLOBAL",
            OpCode::GetLocal(_) => "GET_LOCAL",
            OpCode::SetLocal(_) => "SET_LOCAL",
            OpCode::Nil => "NIL",
            OpCode::Add => "ADD",
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

