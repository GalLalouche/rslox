use convert_case::{Case, Casing};
use crate::rslox::compiled::gc::GcWeak;
use crate::rslox::compiled::tests::DeepEq;

pub type Ptr = usize;
pub type CodeLocation = usize;
pub type StackLocation = usize;

#[derive(Debug, Clone, PartialEq)]
pub enum OpCode {
    Return,
    Pop,
    Print,
    DefineGlobal(GcWeak<String>),
    DefineLocal(StackLocation),
    Constant(Ptr),
    Bool(bool),
    // since std::String is already heap managed, we don't need a separate pointer here.
    // Hurray for real languages!
    // While "Weak", this is never expected to actually point to null as Strings are only
    // "uninterested" when garbage collected.
    String(GcWeak<String>),
    GetGlobal(GcWeak<String>),
    SetGlobal(GcWeak<String>),
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
        format!("OP_{:13}",
                format!("{:?}", self)
                    .to_case(Case::UpperSnake)
                    .chars()
                    .into_iter()
                    .take_while(|e| e.is_alphanumeric())
                    .collect::<String>())
    }
}

