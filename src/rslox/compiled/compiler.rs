use std::mem;

use either::Either::{Left, Right};
use nonempty::NonEmpty;
use num_traits::FromPrimitive;

use crate::rslox::common::error::{convert_errors, LoxResult, ParserError, ToNonEmpty};
use crate::rslox::common::lexer::{Token, TokenType};
use crate::rslox::compiled::chunk::{Chunk, Line};
use crate::rslox::compiled::op_code::{CodeLocation, OpCode};
use crate::rslox::compiled::program::Program;

type CompilerError = ParserError;
pub fn compile(lexems: Vec<Token>) -> LoxResult<Program> {
    convert_errors(Compiler::new(lexems).compile())
}

type Depth = i64;

const UNINITIALIZED: Depth = -1;

#[derive(Debug, Default)]
struct Compiler {
    program: Program,
    tokens: Vec<Token>,
    current: usize,
    locals: Vec<(String, Depth)>,
    depth: Depth,
}

#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd, FromPrimitive)]
enum Precedence {
    TopLevel,
    Assignment,
    Or,
    And,
    Equality /* == != */,
    Comparison /* < > <= >= */,
    Term /* + - */,
    Factor /* * / */,
    Unary /* ! - */,
    Call /* . () */,
    Primary,
}

impl Precedence {
    fn next(&self) -> Option<Self> {
        FromPrimitive::from_u8(*self as u8 + 1)
    }
}

impl From<&TokenType> for Precedence {
    fn from(tt: &TokenType) -> Self {
        match tt {
            TokenType::Minus => Precedence::Term,
            TokenType::Plus => Precedence::Term,
            TokenType::Slash => Precedence::Factor,
            TokenType::Star => Precedence::Factor,
            TokenType::EqualEqual => Precedence::Equality,
            TokenType::BangEqual => Precedence::Equality,
            TokenType::Less => Precedence::Comparison,
            TokenType::LessEqual => Precedence::Comparison,
            TokenType::Greater => Precedence::Comparison,
            TokenType::GreaterEqual => Precedence::Comparison,
            _ => Precedence::TopLevel,
        }
    }
}

type CanAssign = bool;
type JumpOffset = usize;

impl Compiler {
    pub fn new(lexems: Vec<Token>) -> Self {
        Compiler { tokens: lexems, ..Default::default() }
    }

    pub fn compile(mut self) -> Result<Program, NonEmpty<CompilerError>> {
        let mut last_line: Line = 0;
        let mut errors = Vec::new();
        while !self.is_at_end() {
            if let Some(line) = self.declaration(&mut errors) {
                last_line = line;
            }
        }
        match NonEmpty::from_vec(errors) {
            None => {
                self.active_chunk().write(OpCode::Return, last_line);
                Ok(self.program)
            }
            Some(errs) => Err(errs),
        }
    }

    fn synchronize(&mut self) {
        while !self.is_at_end() && !self.matches(TokenType::Semicolon).is_some() {
            match self.peek_type() {
                TokenType::Class | TokenType::Fun | TokenType::Var | TokenType::For | TokenType::If
                | TokenType::While | TokenType::Print | TokenType::Return => return,
                _ => {
                    self.advance();
                }
            }
        }
    }

    fn declaration(&mut self, errors: &mut Vec<CompilerError>) -> Option<Line> {
        macro_rules! push_single {
            ($e:ident) => {{
                errors.push($e);
                self.synchronize();
                None
            }};
        }
        if let Some(line) = self.matches(TokenType::Var) {
            match self.declare_variable(true: CanAssign) {
                Ok(_) => Some(line),
                Err(e) => push_single!(e),
            }
        } else {
            match self.statement() {
                Ok(l) => Some(l),
                Err(errs) => {
                    for err in errs {
                        errors.push(err);
                    }
                    self.synchronize();
                    None
                }
            }
        }
    }

    fn statement(&mut self) -> Result<Line, NonEmpty<CompilerError>> {
        let line = if let Some(line) = self.matches(TokenType::Print) {
            self.compile_expression().to_nonempty()?;
            self.active_chunk().write(OpCode::Print, line);
            line
        } else if let Some(line) = self.matches(TokenType::If) {
            return self.if_stmt(line); // Skips semicolon
        } else if let Some(line) = self.matches(TokenType::While) {
            return self.while_stmt(line); // Skips semicolon
        } else if let Some(line) = self.matches(TokenType::For) {
            return self.for_stmt(line); // Skips semicolon
        } else if let Some(line) = self.matches(TokenType::OpenBrace) {
            self.begin_scope();
            let mut errors = Vec::new();
            while !self.is_at_end() && self.peek_type() != &TokenType::CloseBrace {
                self.declaration(&mut errors);
            }
            self.consume(TokenType::CloseBrace, None).to_nonempty()?;
            // Skip the semicolon
            return match NonEmpty::from_vec(errors) {
                None => {
                    self.end_scope(line);
                    Ok(line)
                }
                Some(errs) => Err(errs),
            };
        } else {
            self.expression_statement().to_nonempty()?
        };
        self.consume(TokenType::Semicolon, None).to_nonempty()?;
        Ok(line)
    }

    fn end_scope(&mut self, line: Line) {
        assert!(self.depth > 0);
        while self.locals.last().map(|e| e.1).contains(&self.depth) {
            self.active_chunk().write(OpCode::Pop, line);
            self.locals.pop().unwrap();
        }
        self.depth -= 1;
    }

    fn begin_scope(&mut self) {
        self.depth += 1;
    }

    fn if_stmt(&mut self, line: Line) -> Result<Line, NonEmpty<CompilerError>> {
        self.consume(TokenType::OpenParen, None).to_nonempty()?;
        self.compile_expression().to_nonempty()?;
        self.consume(TokenType::CloseParen, None).to_nonempty()?;
        self.jumping_body(line, 1: JumpOffset, OpCode::JumpIfFalse)?;
        if let Some(line) = self.matches(TokenType::Else) {
            self.jumping_body(line, 0: JumpOffset, OpCode::Jump)?;
        }
        Ok(line)
    }

    fn while_stmt(&mut self, line: Line) -> Result<Line, NonEmpty<CompilerError>> {
        self.consume(TokenType::OpenParen, None).to_nonempty()?;
        let body_start = self.active_chunk().next_location();
        self.compile_expression().to_nonempty()?;
        self.consume(TokenType::CloseParen, None).to_nonempty()?;
        self.jumping_body(line, 1: JumpOffset, OpCode::JumpIfFalse)?;
        self.active_chunk().write(OpCode::Jump(body_start), line);
        Ok(line)
    }

    fn for_stmt(&mut self, line: Line) -> Result<Line, NonEmpty<CompilerError>> {
        self.consume(TokenType::OpenParen, None).to_nonempty()?;
        // Initializer
        self.begin_scope();
        if self.matches(TokenType::Semicolon).is_some() {
            Ok(())
        } else if self.matches(TokenType::Var).is_some() {
            self.declare_variable(true: CanAssign).to_nonempty()
        } else {
            self.expression_statement().to_nonempty().map(|_| ())
        }?;
        // Condition
        let body_start = self.active_chunk().next_location();
        let condition_jump: Option<CodeLocation> =
            if self.matches(TokenType::Semicolon).is_some() {
                None
            } else {
                self.compile_expression().to_nonempty()?;
                self.consume(TokenType::Semicolon, None).to_nonempty()?;
                Some(self.active_chunk().write(OpCode::UnpatchedJump, line))
            };
        // Increment
        let increment: Option<CodeLocation> =
            if self.matches(TokenType::CloseParen).is_some() {
                Ok::<Option<CodeLocation>, NonEmpty<CompilerError>>(None)
            } else {
                let jump_over_increment = self.active_chunk().write(OpCode::UnpatchedJump, line);
                let result = self.active_chunk().next_location();
                self.compile_expression().to_nonempty()?;
                self.active_chunk().write(OpCode::Pop, line);
                self.active_chunk().write(OpCode::Jump(body_start), line);
                self.patch_jump(jump_over_increment, 0: JumpOffset, OpCode::Jump);
                self.consume(TokenType::CloseParen, None).to_nonempty()?;
                Ok(Some(result))
            }?;
        self.statement()?;
        if let Some(cond) = condition_jump {
            self.patch_jump(cond, 1: JumpOffset, OpCode::JumpIfFalse);
        }
        if let Some(incr) = increment {
            self.active_chunk().write(OpCode::Jump(incr), line);
        } else {
            self.active_chunk().write(OpCode::Jump(body_start), line);
        }
        self.end_scope(line);
        Ok(line)
    }

    fn patch_jump<F: FnOnce(CodeLocation) -> OpCode>(
        &mut self, source: CodeLocation, offset: JumpOffset, ctor: F,
    ) {
        assert!(match self.active_chunk().get(source).unwrap().0 {
            OpCode::UnpatchedJump => true,
            _ => false,
        });
        (*self.active_chunk().get_mut(source).unwrap()).0 = ctor(self.active_chunk().next_location() + offset);
    }

    // If new elements are added after this function has finished running, the jump should be after
    // those.
    fn jumping_body<F: FnOnce(CodeLocation) -> OpCode>(
        &mut self, line: Line, offset: JumpOffset, ctor: F,
    ) -> Result<(), NonEmpty<CompilerError>> {
        let jump_pos = self.active_chunk().write(OpCode::UnpatchedJump, line);
        self.statement()?;
        self.patch_jump(jump_pos, offset, ctor);
        Ok(())
    }

    fn declare_variable(&mut self, can_assign: bool) -> Result<(), CompilerError> {
        let Token { r#type, line } = self.advance();
        let name = match r#type {
            TokenType::Identifier(name) => Ok(name),
            e => Err(CompilerError {
                message: format!("Expected Identifier for variable, got '{:?}'", e),
                token: Token { r#type: e, line },
            })
        }?;
        if self.depth > 0 {
            self.locals.push((name.clone(), UNINITIALIZED));
        }
        if can_assign && self.matches(TokenType::Equal).is_some() {
            self.compile_expression()
        } else {
            self.active_chunk().write(OpCode::Nil, line);
            Ok(line)
        }?;
        if self.depth == 0 {
            let global = self.program.define_global(name);
            self.active_chunk().write(OpCode::DefineGlobal(global), line);
            Ok(())
        } else {
            // Skipping the first element because that is the current (uninitialized) local.
            for (local_name, depth) in self.locals.iter().rev().skip(1) {
                if depth < &self.depth {
                    break;
                }
                if &name == local_name {
                    return Err(CompilerError {
                        message: format!("Redefined variable '{}' in same scope", name),
                        token: Token { r#type: TokenType::identifier(name), line },
                    });
                }
            }
            assert_eq!(self.locals.last().unwrap().0, name);
            self.locals.last_mut().unwrap().1 = self.depth;
            Ok(())
        }.and_then(|result| {
            self.consume(TokenType::Semicolon, None)?;
            Ok(result)
        })
    }

    fn expression_statement(&mut self) -> Result<Line, CompilerError> {
        let line = self.compile_expression()?;
        self.active_chunk().write(OpCode::Pop, line);
        Ok(line)
    }

    fn compile_expression(&mut self) -> Result<Line, CompilerError> {
        self.compile_precedence(Precedence::Assignment)
    }

    fn compile_precedence(&mut self, precedence: Precedence) -> Result<Line, CompilerError> {
        let can_assign = precedence <= Precedence::Assignment;
        let Token { line, r#type } = self.advance();
        match r#type {
            TokenType::Minus => {
                self.compile_precedence(Precedence::Unary)?;
                self.active_chunk().write(OpCode::Negate, line);
            }
            TokenType::Bang => {
                self.compile_precedence(Precedence::Unary)?;
                self.active_chunk().write(OpCode::Not, line);
            }
            TokenType::NumberLiteral(num) => {
                self.active_chunk().write(OpCode::Number(num), line);
            }
            TokenType::Identifier(name) => {
                let is_assignment = can_assign && self.matches(TokenType::Equal).is_some();
                match self.resolve_local(&name, &line)? {
                    Some(index) => {
                        if is_assignment {
                            self.compile_expression()?;
                            self.active_chunk().write(OpCode::SetLocal(index), line);
                        } else {
                            self.active_chunk().write(OpCode::GetLocal(index), line);
                        }
                    }
                    None => {
                        let global = self.program.define_global(name);
                        if is_assignment {
                            self.compile_expression()?;
                            self.active_chunk().write(OpCode::SetGlobal(global), line);
                        } else {
                            self.active_chunk().write(OpCode::GetGlobal(global), line);
                        }
                    }
                }
            }
            TokenType::StringLiteral(str) => self.program.intern_string(str, line),
            TokenType::True | TokenType::False | TokenType::Nil => {
                let op = match &r#type {
                    TokenType::True => OpCode::Bool(true),
                    TokenType::False => OpCode::Bool(false),
                    TokenType::Nil => OpCode::Nil,
                    _ => panic!(),
                };
                self.active_chunk().write(op, line);
            }
            TokenType::OpenParen => {
                self.compile_expression()?;
                self.consume(TokenType::CloseParen, None)?;
            }
            e => return Err(
                CompilerError::new(format!("Unexpected '{:?}'", e), Token { r#type: e, line })),
        }
        let mut last_line = line;
        while !self.is_at_end() && precedence <= Precedence::from(self.peek_type()) {
            let Token { line, r#type } = self.advance();
            let next_precedence = Precedence::from(&r#type).next().unwrap();
            let op = match r#type {
                TokenType::Minus => Left(OpCode::Subtract),
                TokenType::Plus => Left(OpCode::Add),
                TokenType::Slash => Left(OpCode::Divide),
                TokenType::Star => Left(OpCode::Multiply),
                TokenType::EqualEqual => Left(OpCode::Equals),
                TokenType::Less => Left(OpCode::Less),
                TokenType::Greater => Left(OpCode::Greater),
                TokenType::BangEqual => Right(OpCode::Equals),
                TokenType::LessEqual => Right(OpCode::Greater),
                TokenType::GreaterEqual => Right(OpCode::Less),
                _ => panic!()
            };
            self.compile_precedence(next_precedence)?;
            match op {
                Left(op) => { self.active_chunk().write(op, line); }
                Right(op) => {
                    self.active_chunk().write(op, line);
                    self.active_chunk().write(OpCode::Not, line);
                }
            }
            last_line = line;
            if !self.is_at_end() && can_assign && self.peek_type() == &TokenType::Equal {
                return Err(CompilerError::new(
                    "Invalid assignment target.",
                    self.tokens[self.current].clone(),
                ));
            }
        }
        Ok(last_line)
    }

    fn active_chunk(&mut self) -> &mut Chunk {
        &mut self.program.chunk
    }

    fn resolve_local(&self, name: &str, line: &Line) -> Result<Option<usize>, CompilerError> {
        for (i, (local_name, depth)) in self.locals.iter().rev().enumerate() {
            if depth == &UNINITIALIZED {
                return Err(CompilerError::new(
                    format!("Expression uses uninitialized local variable '{}'", name),
                    Token::new(*line, TokenType::identifier(name)),
                ));
            }
            if name == local_name {
                return Ok(Some(i));
            }
        }
        return Ok(None);
    }

    fn consume(&mut self, expected: TokenType, msg: Option<String>) -> Result<(), CompilerError> {
        let expected_msg = msg.unwrap_or(expected.to_string());
        if self.is_at_end() {
            return Err(CompilerError::new(
                format!("Expected {}, but encountered end of file", expected_msg),
                self.tokens.last().expect("empty tokens").to_owned(),
            ));
        }

        let token = self.advance();
        if token.r#type != expected {
            Err(CompilerError::new(
                format!(
                    "Expected {}, but encountered {} at line {}",
                    expected_msg,
                    token.r#type,
                    token.line,
                ),
                token.to_owned(),
            ))
        } else {
            assert_ne!(expected, TokenType::Eof);
            Ok(())
        }
    }

    fn matches(&mut self, tt: TokenType) -> Option<Line> {
        if self.is_at_end() {
            None
        } else if self.peek_type() == &tt {
            let result = self.tokens[self.current].line;
            self.advance();
            Some(result)
        } else {
            None
        }
    }

    fn advance(&mut self) -> Token {
        let result =
            mem::replace(self.tokens.get_mut(self.current).unwrap(), Token::new(0, TokenType::Eof));
        self.current += 1;
        result
    }

    fn is_at_end(&self) -> bool {
        self.current == self.tokens.len()
    }

    fn peek_type(&self) -> &TokenType {
        &self.tokens[self.current].r#type
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::ops::Deref;
    use std::rc::Rc;

    use crate::{assert_deep_eq, assert_msg_contains};
    use crate::rslox::common::tests::unsafe_tokenize;
    use crate::rslox::common::utils::SliceExt;
    use crate::rslox::compiled::tests::unsafe_compile;

    use super::*;

    #[test]
    fn constant() {
        let mut expected: Chunk = Default::default();
        expected.write(OpCode::Number(123.0), 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_compile(vec!["123;"]).chunk,
            expected,
        )
    }

    #[test]
    fn grouped_constant() {
        let mut expected: Chunk = Default::default();
        expected.write(OpCode::Number(123.0), 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            compile(unsafe_tokenize(vec!["(123);"])).unwrap().chunk,
            expected,
        )
    }

    #[test]
    fn unary_minus() {
        let mut expected: Chunk = Default::default();
        expected.write(OpCode::Number(123.0), 1);
        expected.write(OpCode::Negate, 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_compile(vec!["-123;"]).chunk,
            expected,
        )
    }

    #[test]
    fn basic_precedence() {
        let mut expected: Chunk = Default::default();
        expected.write(OpCode::Number(1.0), 1);
        expected.write(OpCode::Negate, 1);
        expected.write(OpCode::Number(2.0), 1);
        expected.write(OpCode::Add, 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_compile(vec!["-1+2;"]).chunk,
            expected,
        )
    }

    #[test]
    fn mixed_unary_and_binary() {
        let mut expected: Chunk = Default::default();
        expected.write(OpCode::Number(1.0), 1);
        expected.write(OpCode::Negate, 1);
        expected.write(OpCode::Number(2.0), 1);
        expected.write(OpCode::Subtract, 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_compile(vec!["-1-2;"]).chunk,
            expected,
        )
    }

    #[test]
    fn string_interning() {
        let interned_strings = unsafe_compile(vec![r#""str" == "str";"#]).interned_strings;
        let mut expected = HashSet::new();
        expected.insert(Rc::new("str".to_owned()));
        assert_eq!(
            interned_strings,
            expected,
        )
    }

    #[test]
    fn multiple_error_report() {
        let vec: Vec<_> = compile(
            unsafe_tokenize(
                vec![
                    "1 +;",
                    "3 * 3;",
                    r#"print -;"#,
                ])
        ).unwrap_err().into();
        assert_eq!(
            vec.iter().map(|e| e.deref().get_info().line).collect::<Vec<_>>(),
            vec![1, 3],
        )
    }

    #[test]
    fn define_nil_var() {
        let compiled = unsafe_compile(vec!["var foo;"]);
        let mut expected: Program = Default::default();
        let w = expected.define_global("foo".to_owned());
        expected.chunk.write(OpCode::Nil, 1);
        expected.chunk.write(OpCode::DefineGlobal(w), 1);
        expected.chunk.write(OpCode::Return, 1);
        assert_deep_eq!(
            compiled,
            expected,
        )
    }

    #[test]
    fn invalid_assignment_target() {
        let msg =
            compile(unsafe_tokenize(vec!["a*b = c+d;"])).unwrap_err().unwrap_single().get_message();
        assert_msg_contains!(msg, "Invalid assignment target")
    }

    #[test]
    fn uninitialized_variable() {
        assert_msg_contains!(
            compile(unsafe_tokenize(vec![
                "var a = 42;",
                "{",
                "  var a = a;",
                "}",
            ])).unwrap_err().unwrap_single().get_message(),
            "uninitialized local variable"
        )
    }

    #[test]
    fn local_variable_redeclaration() {
        assert_msg_contains!(
            compile(unsafe_tokenize(vec![
                "{",
                "  var a = 42;",
                "  var a = 54;",
                "}",
            ])).unwrap_err().unwrap_single().get_message(),
            "Redefined variable 'a' in same scope"
        )
    }

    #[test]
    fn var_inside_if() {
        assert_msg_contains!(
            compile(unsafe_tokenize(vec![
                "if (true)",
                "  var x = 2;",
            ])).unwrap_err().unwrap_single().get_message(),
            "Unexpected 'Var'"
        )
    }
    // TODO No condition tests will just result in an infinite loop until return inside functions is implemented.
}