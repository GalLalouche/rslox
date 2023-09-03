use std::mem;

use either::Either::{Left, Right};
use nonempty::NonEmpty;
use num_traits::FromPrimitive;

use crate::rslox::common::error::{convert_errors, LoxResult, ParserError};
use crate::rslox::common::lexer::{Token, TokenType};
use crate::rslox::compiled::chunk::{Chunk, InternedString, Upvalue};
use crate::rslox::compiled::code::Line;
use crate::rslox::compiled::op_code::{ArgCount, CodeLocation, OpCode, StackLocation};
use crate::rslox::compiled::value::Function;

type CompilerError = ParserError;

impl From<CompilerError> for NonEmpty<CompilerError> {
    fn from(value: CompilerError) -> Self { NonEmpty::new(value) }
}

pub fn compile(tokens: Vec<Token>) -> LoxResult<Chunk> {
    convert_errors(Compiler::new(tokens).compile())
}

type Depth = i64;


type TokenPointer = usize;

#[derive(Debug)]
struct Compiler {
    tokens: Vec<Token>,
    frames: NonEmpty<FunctionContext>,
    depth: Depth,
    current: TokenPointer,
}

impl Compiler {
    pub fn new(tokens: Vec<Token>) -> Self {
        let top_frame = Default::default();
        Compiler {
            tokens,
            frames: NonEmpty::new(top_frame),
            depth: 0,
            current: 0,
        }
    }

    pub fn compile(mut self) -> Result<Chunk, NonEmpty<CompilerError>> {
        let mut errors = Vec::new();
        while !self.is_at_end() {
            self.declaration(&mut errors);
        }
        match NonEmpty::from_vec(errors) {
            None => {
                assert_eq!(self.frames.len(), 1);
                Ok(self.frames.head.chunk)
            }
            Some(errs) => Err(errs),
        }
    }

    fn begin_scope(&mut self) { self.depth += 1; }

    fn end_scope(&mut self, line: Line) {
        assert!(self.depth > 0);
        let mut pop_n_counter = 0;
        while self.active_locals().last().iter().any(|l| l.depth == self.depth) {
            if self.active_locals_mut().pop().unwrap().is_captured {
                self.write_pop(pop_n_counter, line);
                pop_n_counter = 0;
                self.write(OpCode::CloseUpvalue, line);
            } else {
                pop_n_counter += 1;
            }
        }
        self.write_pop(pop_n_counter, line);
        self.depth -= 1;
    }

    fn write_pop(&mut self, amount: usize, line: Line) {
        if amount == 1 {
            self.write(OpCode::Pop, line);
        } else if amount > 1 {
            self.write(OpCode::PopN(amount), line);
        }
    }

    // Consumes all the tokens until the next "synchronization" point, so we can report as many
    // errors as possible.
    fn synchronize(&mut self) {
        while !self.is_at_end() && !self.matches(TokenType::Semicolon).is_some() {
            let should_continue = match self.peek_type() {
                TokenType::Class | TokenType::Fun | TokenType::Var | TokenType::For | TokenType::If
                | TokenType::While | TokenType::Print | TokenType::Return => false,
                _ => true,
            };
            if should_continue { self.advance(); } else { return; }
        }
    }

    fn declaration(&mut self, errors: &mut Vec<CompilerError>) -> Option<Line> {
        if let Some(_) = self.matches(TokenType::Fun) {
            match self.declare_function() {
                Ok(l) => Some(l),
                Err(errs) => {
                    for err in errs {
                        errors.push(err);
                    }
                    self.synchronize();
                    None
                }
            }
        } else if let Some(line) = self.matches(TokenType::Var) {
            match self.declare_variable(true as CanAssign) {
                Ok(_) => Some(line),
                Err(e) => {
                    errors.push(e);
                    self.synchronize();
                    None
                }
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
            self.compile_expression()?;
            self.write(OpCode::Print, line);
            line
        } else if let Some(line) = self.matches(TokenType::Return) {
            return self.return_stmt(line).map_err(|e| e.into());
        } else if let Some(line) = self.matches(TokenType::If) {
            return self.if_stmt(line); // Skips semicolon
        } else if let Some(line) = self.matches(TokenType::While) {
            return self.while_stmt(line); // Skips semicolon
        } else if let Some(line) = self.matches(TokenType::For) {
            return self.for_stmt(line); // Skips semicolon
        } else if let Some(_) = self.matches(TokenType::OpenBrace) {
            return self.block();
        } else {
            self.expression_statement()?
        };
        self.consume(TokenType::Semicolon, None)?;
        Ok(line)
    }

    fn return_stmt(&mut self, line: Line) -> Result<Line, CompilerError> {
        if let Some(line) = self.matches(TokenType::Semicolon) {
            self.write(OpCode::Nil, line);
        } else {
            self.compile_expression()?;
        }
        self.consume(TokenType::Semicolon, None)?;
        self.write(OpCode::Return, line);
        Ok(line)
    }

    fn block(&mut self) -> Result<Line, NonEmpty<CompilerError>> {
        self.begin_scope();
        let ending_line = self.multi_statements()?;
        self.end_scope(ending_line);
        Ok(ending_line)
    }

    fn multi_statements(&mut self) -> Result<Line, NonEmpty<CompilerError>> {
        let mut errors = Vec::new();
        while !self.is_at_end() && self.peek_type() != &TokenType::CloseBrace {
            self.declaration(&mut errors);
        }
        let ending_line = self.consume(TokenType::CloseBrace, None)?;
        match NonEmpty::from_vec(errors) {
            None => Ok(ending_line),
            Some(errs) => Err(errs),
        }
    }

    fn if_stmt(&mut self, line: Line) -> Result<Line, NonEmpty<CompilerError>> {
        self.consume(TokenType::OpenParen, None)?;
        self.compile_expression()?;
        self.consume(TokenType::CloseParen, None)?;
        let jump_pos = self.jumping_body(line, 0 as JumpOffset, OpCode::JumpIfFalse)?;
        if let Some(line) = self.matches(TokenType::Else) {
            self.jumping_body(line, 0 as JumpOffset, OpCode::Jump)?;
            // Since we added a Jump, we need to fix the JumpIfFalse target.
            let current_jump = self.active_chunk().get_code().get(jump_pos).unwrap().0.clone();
            (*self.active_chunk_mut().get_mut(jump_pos).unwrap()).0 = match current_jump {
                OpCode::JumpIfFalse(to) => OpCode::JumpIfFalse(to + 1),
                e => panic!("Expected JumpIfFalse, was {:?}", e),
            };
        }
        Ok(line)
    }

    fn while_stmt(&mut self, line: Line) -> Result<Line, NonEmpty<CompilerError>> {
        self.consume(TokenType::OpenParen, None)?;
        let body_start = self.active_chunk().get_code().next_location();
        self.compile_expression()?;
        self.consume(TokenType::CloseParen, None)?;
        self.jumping_body(line, 1 as JumpOffset, OpCode::JumpIfFalse)?;
        self.write(OpCode::Jump(body_start), line);
        Ok(line)
    }

    fn for_stmt(&mut self, line: Line) -> Result<Line, NonEmpty<CompilerError>> {
        self.consume(TokenType::OpenParen, None)?;
        // Initializer
        self.begin_scope();
        if self.matches(TokenType::Semicolon).is_some() {
            Ok(())
        } else if self.matches(TokenType::Var).is_some() {
            self.declare_variable(true as CanAssign)
        } else {
            self.expression_statement().map(|_| ())
        }?;
        // Condition
        let body_start = self.active_chunk().get_code().next_location();
        let condition_jump: Option<CodeLocation> =
            if self.matches(TokenType::Semicolon).is_some() {
                None
            } else {
                self.compile_expression()?;
                self.consume(TokenType::Semicolon, None)?;
                Some(self.write(OpCode::UnpatchedJump, line))
            };
        // Increment
        let increment: Option<CodeLocation> =
            if self.matches(TokenType::CloseParen).is_some() {
                Ok::<Option<CodeLocation>, NonEmpty<CompilerError>>(None)
            } else {
                let jump_over_increment = self.write(OpCode::UnpatchedJump, line);
                let result = self.active_chunk().get_code().next_location();
                self.compile_expression()?;
                self.write(OpCode::Pop, line);
                self.write(OpCode::Jump(body_start), line);
                self.active_frame_mut().patch_jump(
                    jump_over_increment, 0 as JumpOffset, OpCode::Jump);
                self.consume(TokenType::CloseParen, None)?;
                Ok(Some(result))
            }?;
        self.statement()?;
        if let Some(cond) = condition_jump {
            self.active_frame_mut().patch_jump(cond, 1 as JumpOffset, OpCode::JumpIfFalse);
        }
        self.write(OpCode::Jump(increment.unwrap_or(body_start)), line);
        self.end_scope(line);
        Ok(line)
    }

    // If new elements are added after this function has finished running, the jump should be after
    // those.
    fn jumping_body<F: FnOnce(CodeLocation) -> OpCode>(
        &mut self, line: Line, offset: JumpOffset, ctor: F,
    ) -> Result<CodeLocation, NonEmpty<CompilerError>> {
        let jump_pos = self.write(OpCode::UnpatchedJump, line);
        self.statement()?;
        self.active_frame_mut().patch_jump(jump_pos, offset, ctor);
        Ok(jump_pos)
    }

    fn declare_function(&mut self) -> Result<Line, NonEmpty<CompilerError>> {
        let (name, line) = self.parse_variable()?;
        self.mark_initialized();
        let mut arity = 0;
        self.depth += 1;
        self.frames.push(FunctionContext::default());
        self.consume(TokenType::OpenParen, None)?;
        if self.peek_type() != &TokenType::CloseParen {
            loop {
                arity += 1;
                let (var_name, line) = self.parse_variable()?;
                self.define_variable(var_name, line)?;
                if self.matches(TokenType::Comma).is_none() {
                    break;
                }
            }
        }
        self.consume(TokenType::CloseParen, None)?;
        self.consume(TokenType::OpenBrace, None)?;
        // Functions don't explicitly clean up after themselves; instead, each return statement
        // knows how many elements to drop from the call stack.
        let end_line = self.multi_statements()?;
        let (chunk, upvalues) = self.frames.pop().unwrap().finish(end_line);
        self.depth -= 1;
        let function = Function { name: name.clone(), arity, chunk };
        self.active_chunk_mut().add_function(function, line, upvalues.into_iter().collect());
        self.define_variable(name, line)?;
        Ok(end_line)
    }

    fn declare_variable(&mut self, can_assign: bool) -> Result<(), CompilerError> {
        let (name, line) = self.parse_variable()?;
        if can_assign && self.matches(TokenType::Equal).is_some() {
            self.compile_expression()
        } else {
            self.write(OpCode::Nil, line);
            Ok(line)
        }?;
        self.define_variable(name, line).and_then(|result| {
            self.consume(TokenType::Semicolon, None)?;
            Ok(result)
        })
    }

    fn parse_variable(&mut self) -> Result<(InternedString, Line), CompilerError> {
        let Token { r#type, line } = self.advance();
        let name = match r#type {
            TokenType::Identifier(name) => Ok(name),
            e => Err(CompilerError {
                message: format!("Expected Identifier for variable, got '{:?}'", e),
                token: Token { r#type: e, line },
            })
        }?;
        let interned = self.intern_string(name);
        if self.depth > 0 {
            self.active_locals_mut().push(Local::new(interned.clone()))
        }
        Ok((interned, line))
    }

    fn define_variable(&mut self, name: InternedString, line: Line) -> Result<(), CompilerError> {
        if self.depth == 0 {
            self.write(OpCode::DefineGlobal(name), line);
            Ok(())
        } else {
            // Skipping the first element because that is the current (uninitialized) local.
            for Local { name: local_name, depth, .. } in self.active_locals().iter().rev().skip(1) {
                if depth < &self.depth {
                    break;
                }
                if &name == local_name {
                    return Err(CompilerError {
                        message: format!(
                            "Redefined variable '{}' in same scope",
                            name.unwrap_upgrade()),
                        token: Token {
                            r#type: TokenType::identifier(name.to_owned()),
                            line,
                        },
                    });
                }
            }
            assert_eq!(self.active_locals().last().unwrap().name, name);
            self.mark_initialized();
            Ok(())
        }
    }

    fn mark_initialized(&mut self) {
        // No need to initialize globals.
        if self.depth != 0 {
            self.active_locals_mut().last_mut().unwrap().depth = self.depth;
        }
    }

    fn expression_statement(&mut self) -> Result<Line, CompilerError> {
        let line = self.compile_expression()?;
        self.write(OpCode::Pop, line);
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
                self.write(OpCode::Negate, line);
            }
            TokenType::Bang => {
                self.compile_precedence(Precedence::Unary)?;
                self.write(OpCode::Not, line);
            }
            TokenType::NumberLiteral(num) => {
                self.write(OpCode::Number(num), line);
            }
            TokenType::Identifier(id) => {
                let is_assignment = can_assign && self.matches(TokenType::Equal).is_some();
                let name = self.intern_string(id);
                let (setter, getter) =
                    if let Some(index) = self.active_frame().resolve_local(&name, line)? {
                        (OpCode::SetLocal(index), OpCode::GetLocal(index))
                    } else if let Some(index) = self.resolve_upvalue(&name) {
                        (OpCode::SetUpvalue(index), OpCode::GetUpvalue(index))
                    } else {
                        (OpCode::SetGlobal(name.clone()), OpCode::GetGlobal(name))
                    };
                if is_assignment {
                    self.compile_expression()?;
                    self.write(setter, line);
                } else {
                    self.write(getter, line);
                }
            }
            TokenType::StringLiteral(str) => {
                let interned = self.intern_string(str);
                self.write(OpCode::String(interned), line);
            }
            TokenType::True | TokenType::False | TokenType::Nil => {
                let op = match &r#type {
                    TokenType::True => OpCode::Bool(true),
                    TokenType::False => OpCode::Bool(false),
                    TokenType::Nil => OpCode::Nil,
                    _ => panic!(),
                };
                self.write(op, line);
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
                TokenType::OpenParen => self.argument_list().map(|c| Left(OpCode::Call(c)))?,
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
                _ => panic!(),
            };
            match op {
                Left(OpCode::Call(c)) => {
                    self.consume(TokenType::CloseParen, None)?;
                    self.write(OpCode::Call(c), line);
                }
                _ => {
                    self.compile_precedence(next_precedence)?;
                    match op {
                        Left(op) => { self.write(op, line); }
                        Right(op) => {
                            self.write(op, line);
                            self.write(OpCode::Not, line);
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
            }
        }
        Ok(last_line)
    }

    fn argument_list(&mut self) -> Result<ArgCount, CompilerError> {
        let mut arity = 0;
        if self.peek_type() != &TokenType::CloseParen {
            loop {
                self.compile_expression()?;
                arity += 1;
                if self.matches(TokenType::Comma).is_none() {
                    break;
                }
            }
        }
        Ok(arity)
    }

    fn active_frame_mut(&mut self) -> &mut FunctionContext { self.frames.last_mut() }
    fn active_frame(&self) -> &FunctionContext { self.frames.last() }

    fn active_chunk(&self) -> &Chunk { &self.active_frame().chunk }
    fn active_chunk_mut(&mut self) -> &mut Chunk { &mut self.active_frame_mut().chunk }

    fn active_locals(&self) -> &Vec<Local> { &self.active_frame().locals }
    fn active_locals_mut(&mut self) -> &mut Vec<Local> {
        &mut self.active_frame_mut().locals
    }

    fn resolve_upvalue(&mut self, name: &InternedString) -> Option<StackLocation> {
        self.resolve_upvalue_aux(name, self.frames.len() - 1)
    }

    fn resolve_upvalue_aux(
        &mut self, name: &InternedString, frame_index: usize) -> Option<StackLocation> {
        if frame_index == 0 {
            return None;
        }
        if let Some(enclosing) = self.frames.get_mut(frame_index - 1) {
            if let Some(local_index) = enclosing.resolve_local_for_upvalue(name) {
                return Some(
                    self.frames[frame_index].insert_upvalue(
                        Upvalue { index: local_index, is_local: true }));
            } else if let Some(local_index) = self.resolve_upvalue_aux(name, frame_index - 1) {
                return Some(
                    self.frames[frame_index].insert_upvalue(
                        Upvalue { index: local_index, is_local: false }));
            }
        }
        return None;
    }

    fn consume(&mut self, expected: TokenType, msg: Option<String>) -> Result<Line, CompilerError> {
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
                    expected_msg, token.r#type, token.line,
                ),
                token.to_owned(),
            ))
        } else {
            assert_ne!(expected, TokenType::Eof);
            Ok(token.line)
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
        let result = mem::replace(
            self.tokens.get_mut(self.current).unwrap(),
            Token::new(0, TokenType::Eof),
        );
        self.current += 1;
        result
    }

    fn is_at_end(&self) -> bool {
        self.current == self.tokens.len()
    }

    fn peek_type(&self) -> &TokenType { &self.tokens[self.current].r#type }

    fn write(&mut self, code: OpCode, line: Line) -> CodeLocation {
        self.active_frame_mut().chunk.write(code, line)
    }

    fn intern_string(&mut self, str: String) -> InternedString {
        self.active_frame_mut().chunk.intern_string(str)
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Local {
    name: InternedString,
    depth: Depth,
    is_captured: bool,
}

impl Local {
    const UNINITIALIZED: Depth = -1;

    pub fn new(name: InternedString) -> Self {
        Local { name, depth: Local::UNINITIALIZED, is_captured: false }
    }

    pub fn is_uninitialized(&self) -> bool { self.depth == Local::UNINITIALIZED }
}

#[derive(Debug, Default)]
struct FunctionContext {
    locals: Vec<Local>,
    chunk: Chunk,
    upvalues: Vec<Upvalue>,
}

impl FunctionContext {
    pub fn finish(mut self, line: Line) -> (Chunk, Vec<Upvalue>) {
        if self.chunk.get_code().last().iter().any(|e| match &e.0 {
            OpCode::Return => false,
            _ => true,
        }) {
            self.chunk.write(OpCode::Nil, line);
            self.chunk.write(OpCode::Return, line);
        }
        (self.chunk, self.upvalues)
    }

    pub fn resolve_local(
        &self, name: &InternedString, line: Line) -> Result<Option<StackLocation>, CompilerError> {
        for (index, local) in self.locals.iter().enumerate() {
            if local.is_uninitialized() {
                return Err(CompilerError::new(
                    format!(
                        "Expression uses uninitialized local variable '{}'", name.unwrap_upgrade()),
                    Token::new(line, TokenType::identifier(name.to_owned())),
                ));
            }
            if name.compare_values(&local.name) {
                return Ok(Some(index));
            }
        }
        return Ok(None);
    }

    pub fn resolve_local_for_upvalue(&mut self, name: &InternedString) -> Option<StackLocation> {
        for (index, local) in self.locals.iter().enumerate() {
            assert!(!local.is_uninitialized());
            if name.compare_values(&local.name) {
                assert_ne!(name, &local.name);
                self.locals[index].is_captured = true;
                return Some(index);
            }
        }
        None
    }

    pub fn insert_upvalue(&mut self, upvalue: Upvalue) -> StackLocation {
        self.upvalues.iter().position(|e| *e == upvalue).unwrap_or_else(|| {
            self.upvalues.push(upvalue);
            self.upvalues.len() - 1
        })
    }

    pub fn patch_jump<F: FnOnce(CodeLocation) -> OpCode>(
        &mut self, source: CodeLocation, offset: JumpOffset, ctor: F,
    ) {
        assert!(match self.chunk.get_code().get(source).unwrap().0 {
            OpCode::UnpatchedJump => true,
            _ => false,
        });
        let next_location = self.chunk.get_code().next_location();
        let result = if offset.is_negative() {
            next_location - (offset.wrapping_abs() as usize)
        } else {
            next_location + offset as usize
        };
        (*self.chunk.get_mut(source).unwrap()).0 = ctor(result);
    }
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
            TokenType::OpenParen => Precedence::Call,
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
type JumpOffset = i8;

#[cfg(test)]
pub fn disassemble(chunk: &Chunk) -> Vec<String> {
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
            OpCode::PopN(num) => format!("{}", num),
            OpCode::UnpatchedJump =>
                panic!("Jump should have been patched at line: '{}'", line),
            OpCode::JumpIfFalse(index) => format!("{}", index),
            OpCode::Jump(index) => format!("{}", index),
            OpCode::Function(i, upvalues) => format!(
                "{} [{}]",
                i,
                upvalues.iter()
                    .map(|e| format!("({},{})", e.index, if e.is_local { "t" } else { "f" }))
                    .collect::<Vec<_>>()
                    .join(","),
            ),
            OpCode::DefineGlobal(name) => format!("'{}'", name.unwrap_upgrade()),
            OpCode::GetGlobal(name) => format!("'{}'", name.unwrap_upgrade()),
            OpCode::SetGlobal(name) => format!("'{}'", name.unwrap_upgrade()),
            OpCode::GetUpvalue(index) => format!("'{}'", index),
            OpCode::SetUpvalue(index) => format!("'{}'", index),
            OpCode::DefineLocal(index) => format!("{}", index),
            OpCode::GetLocal(index) => format!("{}", index),
            OpCode::SetLocal(index) => format!("{}", index),
            OpCode::Bool(bool) => format!("{}", bool),
            OpCode::String(s) => format!("'{}'", s.unwrap_upgrade()),
            OpCode::Call(arg_count) => format!("'{}'", arg_count),
            OpCode::Greater | OpCode::Less | OpCode::Add | OpCode::Subtract | OpCode::Multiply |
            OpCode::Pop | OpCode::Print | OpCode::Nil | OpCode::Equals | OpCode::Divide |
            OpCode::Negate | OpCode::Not | OpCode::CloseUpvalue | OpCode::Return =>
                "".to_owned(),
        });
        result.push(command);
        previous_line = *line;
        is_first = false;
    }
    for i in 0..chunk.function_count() {
        let function = chunk.get_function(i);
        let name = function.unwrap_upgrade().name.unwrap_upgrade();
        result.push(format!("<fun {}>", name));
        result.append(&mut disassemble(&function.unwrap_upgrade().chunk));
        result.push(format!("<end {}>", name));
    }
    result
}

#[cfg(test)]
mod tests {
    use std::ops::Deref;

    use lazy_static::lazy_static;
    use regex::Regex;

    use crate::assert_msg_contains;
    use crate::rslox::common::tests::unsafe_tokenize;
    use crate::rslox::common::utils::SliceExt;
    use crate::rslox::compiled::tests::unsafe_compile;

    use super::*;

    lazy_static! {
        static ref TRIMMER: Regex = Regex::new(r" +\n").unwrap();
    }
    fn assert_bytecode(code: &str, expected: &str) -> () {
        use pretty_assertions_sorted::assert_eq;
        let string = disassemble(&unsafe_compile(vec![code.trim()])).join("\n");
        assert_eq!(
            expected.trim().lines().collect::<Vec<_>>(),
            TRIMMER.replace_all(string.trim(), "\n").lines().collect::<Vec<_>>()
        )
    }

    #[test]
    fn constant() {
        assert_bytecode(
            "123;",
            r#"
00:  1 NUMBER         123
01:  | POP
"#,
        )
    }

    #[test]
    fn grouped_constant() {
        assert_bytecode(
            "123;",
            r#"
00:  1 NUMBER         123
01:  | POP
"#,
        )
    }

    #[test]
    fn unary_minus() {
        assert_bytecode(
            "-123;",
            r#"
00:  1 NUMBER         123
01:  | NEGATE
02:  | POP
"#,
        )
    }

    #[test]
    fn basic_precedence() {
        assert_bytecode(
            "-1+2;",
            r#"
00:  1 NUMBER         1
01:  | NEGATE
02:  | NUMBER         2
03:  | ADD
04:  | POP"#,
        )
    }

    #[test]
    fn mixed_unary_and_binary() {
        assert_bytecode(
            "-1-2;",
            r#"
00:  1 NUMBER         1
01:  | NEGATE
02:  | NUMBER         2
03:  | SUBTRACT
04:  | POP            "#,
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
        assert_bytecode(
            "var foo;",
            r#"
00:  1 NIL
01:  | DEFINE_GLOBAL  'foo'"#,
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
    fn depth_is_reduced() {
        assert_bytecode(
            r#"
{
}
var x = 42;
print x;"#,
            r#"
00:  3 NUMBER         42
01:  | DEFINE_GLOBAL  'x'
02:  4 GET_GLOBAL     'x'
03:  | PRINT"#,
        )
    }

    #[test]
    fn local_variable_order() {
        assert_bytecode(r#"
{
  var x = 1;
  var y = 2;
  print x - y;
}"#,
                        r#"
00:  2 NUMBER         1
01:  3 NUMBER         2
02:  4 GET_LOCAL      0
03:  | GET_LOCAL      1
04:  | SUBTRACT
05:  | PRINT
06:  5 POP_N          2"#,
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

    #[test]
    fn patched_if() {
        assert_bytecode(
            r#"
if (false) {
  print "wtf";
}
            "#,
            r#"
00:  1 BOOL           false
01:  | JUMP_IF_FALSE  4
02:  2 STRING         'wtf'
03:  | PRINT
"#,
        )
    }

    #[test]
    fn patched_if_else() {
        assert_bytecode(
            r#"
if (false) {
  print "wtf";
} else {
  print "ok";
}
            "#,
            r#"
00:  1 BOOL           false
01:  | JUMP_IF_FALSE  5
02:  2 STRING         'wtf'
03:  | PRINT
04:  3 JUMP           7
05:  4 STRING         'ok'
06:  | PRINT
                "#,
        )
    }

    #[test]
    fn define_and_print_function() {
        assert_bytecode(
            r#"
fun areWeHavingItYet() {
  print "Yes we are!";
}
print areWeHavingItYet;
            "#,
            r#"
00:  1 FUNCTION       0 []
01:  | DEFINE_GLOBAL  'areWeHavingItYet'
02:  4 GET_GLOBAL     'areWeHavingItYet'
03:  | PRINT
<fun areWeHavingItYet>
00:  2 STRING         'Yes we are!'
01:  | PRINT
02:  3 NIL
03:  | RETURN
<end areWeHavingItYet>
              "#,
        )
    }

    #[test]
    fn define_function_with_local_variables() {
        assert_bytecode(
            r#"
fun areWeHavingItYet() {
  var x = 1;
  var y = 2;
  print x + y;
}
            "#,
            r#"
00:  1 FUNCTION       0 []
01:  | DEFINE_GLOBAL  'areWeHavingItYet'
<fun areWeHavingItYet>
00:  2 NUMBER         1
01:  3 NUMBER         2
02:  4 GET_LOCAL      0
03:  | GET_LOCAL      1
04:  | ADD
05:  | PRINT
06:  5 NIL
07:  | RETURN
<end areWeHavingItYet>
            "#,
        );
    }

    #[test]
    fn call_function() {
        assert_bytecode(
            r#"
fun areWeHavingItYet() {
  print "Yes we are!";
}
areWeHavingItYet();
            "#,
            r#"
00:  1 FUNCTION       0 []
01:  | DEFINE_GLOBAL  'areWeHavingItYet'
02:  4 GET_GLOBAL     'areWeHavingItYet'
03:  | CALL           '0'
04:  | POP
<fun areWeHavingItYet>
00:  2 STRING         'Yes we are!'
01:  | PRINT
02:  3 NIL
03:  | RETURN
<end areWeHavingItYet>
            "#,
        )
    }

    #[test]
    fn define_function_with_args() {
        assert_bytecode(
            r#"
fun areWeHavingItYet(x, y) {
  var z = 1;
  print x + y + z;
}
            "#,
            r#"
00:  1 FUNCTION       0 []
01:  | DEFINE_GLOBAL  'areWeHavingItYet'
<fun areWeHavingItYet>
00:  2 NUMBER         1
01:  3 GET_LOCAL      0
02:  | GET_LOCAL      1
03:  | ADD
04:  | GET_LOCAL      2
05:  | ADD
06:  | PRINT
07:  4 NIL
08:  | RETURN
<end areWeHavingItYet>
           "#,
        )
    }

    #[test]
    fn call_function_with_args() {
        assert_bytecode(
            r#"
fun areWeHavingItYet(x, y) {
  var z = 1;
  print x + y + z;
}
var x = 52;
var z = 12;
areWeHavingItYet(x, z);
            "#,
            r#"
00:  1 FUNCTION       0 []
01:  | DEFINE_GLOBAL  'areWeHavingItYet'
02:  5 NUMBER         52
03:  | DEFINE_GLOBAL  'x'
04:  6 NUMBER         12
05:  | DEFINE_GLOBAL  'z'
06:  7 GET_GLOBAL     'areWeHavingItYet'
07:  | GET_GLOBAL     'x'
08:  | GET_GLOBAL     'z'
09:  | CALL           '2'
10:  | POP
<fun areWeHavingItYet>
00:  2 NUMBER         1
01:  3 GET_LOCAL      0
02:  | GET_LOCAL      1
03:  | ADD
04:  | GET_LOCAL      2
05:  | ADD
06:  | PRINT
07:  4 NIL
08:  | RETURN
<end areWeHavingItYet>
"#,
        )
    }

    #[test]
    fn implicit_function_return() {
        assert_bytecode(
            r#"
fun foo() {
  print "hi";
}
            "#,
            r#"
00:  1 FUNCTION       0 []
01:  | DEFINE_GLOBAL  'foo'
<fun foo>
00:  2 STRING         'hi'
01:  | PRINT
02:  3 NIL
03:  | RETURN
<end foo>
            "#,
        )
    }

    #[test]
    fn basic_function_return() {
        assert_bytecode(
            r#"
fun plus(x, y) {
  return x + y;
}
print plus(10, 20);
            "#,
            r#"
00:  1 FUNCTION       0 []
01:  | DEFINE_GLOBAL  'plus'
02:  4 GET_GLOBAL     'plus'
03:  | NUMBER         10
04:  | NUMBER         20
05:  | CALL           '2'
06:  | PRINT
<fun plus>
00:  2 GET_LOCAL      0
01:  | GET_LOCAL      1
02:  | ADD
03:  | RETURN
<end plus>
            "#,
        )
    }

    #[test]
    fn return_inside_if() {
        assert_bytecode(
            r#"
fun foo(x) {
  if (x > 0) {
    return 1;
  }
  return 2;
}
            "#,
            r#"
00:  1 FUNCTION       0 []
01:  | DEFINE_GLOBAL  'foo'
<fun foo>
00:  2 GET_LOCAL      0
01:  | NUMBER         0
02:  | GREATER
03:  | JUMP_IF_FALSE  6
04:  3 NUMBER         1
05:  | RETURN
06:  5 NUMBER         2
07:  | RETURN
<end foo>
            "#,
        )
    }

    #[test]
    fn basic_closure_local() {
        assert_bytecode(
            r#"
fun foo(x) {
  fun bar() {
    return x;
  }
  return bar;
}
            "#,
            r#"
00:  1 FUNCTION       0 []
01:  | DEFINE_GLOBAL  'foo'
<fun foo>
00:  2 FUNCTION       0 [(0,t)]
01:  5 GET_LOCAL      1
02:  | RETURN
<fun bar>
00:  3 GET_UPVALUE    '0'
01:  | RETURN
<end bar>
<end foo>
            "#,
        )
    }

    #[test]
    fn basic_closure_deeper() {
        assert_bytecode(
            r#"
fun foo(x) {
  fun bar() {
    fun bazz() {
      return x;
    }
    return bazz;
  }
  return bar;
}
            "#,
            r#"
00:  1 FUNCTION       0 []
01:  | DEFINE_GLOBAL  'foo'
<fun foo>
00:  2 FUNCTION       0 [(0,t)]
01:  8 GET_LOCAL      1
02:  | RETURN
<fun bar>
00:  3 FUNCTION       0 [(0,f)]
01:  6 GET_LOCAL      0
02:  | RETURN
<fun bazz>
00:  4 GET_UPVALUE    '0'
01:  | RETURN
<end bazz>
<end bar>
<end foo>
            "#,
        )
    }

    #[test]
    fn close_upvalue_and_popn() {
        assert_bytecode(
            r#"
{
    var a = 1;
    var b = 2;
    var c = 3;
    var d = 4;
    fun foo() {
        print b + c;
    }
}
           "#,
            r#"
00:  2 NUMBER         1
01:  3 NUMBER         2
02:  4 NUMBER         3
03:  5 NUMBER         4
04:  6 FUNCTION       0 [(1,t),(2,t)]
05:  9 POP_N          2
06:  | CLOSE_UPVALUE
07:  | CLOSE_UPVALUE
08:  | POP
<fun foo>
00:  7 GET_UPVALUE    '0'
01:  | GET_UPVALUE    '1'
02:  | ADD
03:  | PRINT
04:  8 NIL
05:  | RETURN
<end foo>"#,
        )
    }

    #[test]
    fn referencing_the_same_upvalue_multiple_times() {
        assert_bytecode(
            r#"
{
    var x = 1;
    fun foo() {
        print x + x;
    }
}
           "#,
            r#"
00:  2 NUMBER         1
01:  3 FUNCTION       0 [(0,t)]
02:  6 POP
03:  | CLOSE_UPVALUE
<fun foo>
00:  4 GET_UPVALUE    '0'
01:  | GET_UPVALUE    '0'
02:  | ADD
03:  | PRINT
04:  5 NIL
05:  | RETURN
<end foo>"#,
        )
    }

    #[test]
    fn close_nested_upvalue() {
        assert_bytecode(
            r#"
fun foo(x) {
    fun bar(y) {
        fun bazz() {
            print x + y;
        }
        return bazz;
    }
    return bar;
}
            "#,
            r#"
00:  1 FUNCTION       0 []
01:  | DEFINE_GLOBAL  'foo'
<fun foo>
00:  2 FUNCTION       0 [(0,t)]
01:  8 GET_LOCAL      1
02:  | RETURN
<fun bar>
00:  3 FUNCTION       0 [(0,f),(0,t)]
01:  6 GET_LOCAL      1
02:  | RETURN
<fun bazz>
00:  4 GET_UPVALUE    '0'
01:  | GET_UPVALUE    '1'
02:  | ADD
03:  | PRINT
04:  5 NIL
05:  | RETURN
<end bazz>
<end bar>
<end foo>
            "#,
        )
    }
}
