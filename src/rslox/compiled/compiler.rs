use std::cell::{Ref, RefCell};
use std::mem;
use std::ops::Deref;
use std::rc::Rc;

use either::Either::{Left, Right};
use nonempty::NonEmpty;
use num_traits::FromPrimitive;
use option_ext::OptionExt;

use crate::rslox::common::error::{convert_errors, LoxResult, ParserError, ToNonEmpty};
use crate::rslox::common::lexer::{Token, TokenType};
use crate::rslox::compiled::chunk::{Chunk, InternedString};
use crate::rslox::compiled::code::{Code, Line};
use crate::rslox::compiled::op_code::{CodeLocation, OpCode};
use crate::rslox::compiled::value::Function;

type CompilerError = ParserError;

pub fn compile(lexems: Vec<Token>) -> LoxResult<Chunk> {
    convert_errors(Compiler::new(lexems).compile())
}

type Depth = i64;

const UNINITIALIZED: Depth = -1;

#[derive(Debug, Default)]
struct Compiler {
    tokens: Vec<Token>,
}


impl Compiler {
    pub fn new(lexems: Vec<Token>) -> Self {
        Compiler { tokens: lexems, ..Default::default() }
    }

    pub fn compile(self) -> Result<Chunk, NonEmpty<CompilerError>> {
        let mut last_chunk = Chunk::default();
        let mut current = 0;
        let tokens_rc = Rc::new(RefCell::new(self.tokens));
        while current != tokens_rc.borrow().len() {
            let frame = FunctionFrame::new(tokens_rc.clone(), current);
            let (chunk, new_current) = frame.compile()?;
            current = new_current;
            last_chunk = chunk;
        }
        Ok(last_chunk)
    }
}

type TokenPointer = usize;

#[derive(Debug, Default)]
struct FunctionFrame {
    locals: Vec<(InternedString, Depth)>,
    depth: Depth,
    chunk: Chunk,

    tokens: Rc<RefCell<Vec<Token>>>,
    current: TokenPointer,
}

impl FunctionFrame {
    pub fn new(tokens: Rc<RefCell<Vec<Token>>>, current: TokenPointer) -> Self {
        FunctionFrame { tokens, current, ..Default::default() }
    }
    pub fn compile(mut self) -> Result<(Chunk, TokenPointer), NonEmpty<CompilerError>> {
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
                Ok((self.chunk, self.current))
            }
            Some(errs) => Err(errs),
        }
    }

    fn finish(self) -> (Chunk, TokenPointer) { (self.chunk, self.current) }

    fn begin_scope(&mut self) {
        self.depth += 1;
    }

    fn end_scope(&mut self, line: Line) {
        assert!(self.depth > 0);
        while self.locals.last().map(|e| e.1).contains(&self.depth) {
            self.chunk.write(OpCode::Pop, line);
            self.locals.pop().unwrap();
        }
        self.depth -= 1;
    }

    fn synchronize(&mut self) {
        while !self.is_at_end() && !self.matches(TokenType::Semicolon).is_some() {
            let should_continue = match self.peek_type().deref() {
                TokenType::Class | TokenType::Fun | TokenType::Var | TokenType::For | TokenType::If
                | TokenType::While | TokenType::Print | TokenType::Return => false,
                _ => true,
            };
            if should_continue { self.advance(); } else { return; }
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
        if let Some(line) = self.matches(TokenType::Fun) {
            match self.declare_function() {
                Ok(_) => Some(line),
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
            return self.block(line);
        } else {
            self.expression_statement().to_nonempty()?
        };
        self.consume(TokenType::Semicolon, None).to_nonempty()?;
        Ok(line)
    }

    fn block(&mut self, line: Line) -> Result<Line, NonEmpty<CompilerError>> {
        self.begin_scope();
        let mut errors = Vec::new();
        while !self.is_at_end() && self.peek_type().deref() != &TokenType::CloseBrace {
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
    }

    fn if_stmt(&mut self, line: Line) -> Result<Line, NonEmpty<CompilerError>> {
        self.consume(TokenType::OpenParen, None).to_nonempty()?;
        self.compile_expression().to_nonempty()?;
        self.consume(TokenType::CloseParen, None).to_nonempty()?;
        self.jumping_body(line, 1 as JumpOffset, OpCode::JumpIfFalse)?;
        if let Some(line) = self.matches(TokenType::Else) {
            self.jumping_body(line, 0 as JumpOffset, OpCode::Jump)?;
        }
        Ok(line)
    }

    fn while_stmt(&mut self, line: Line) -> Result<Line, NonEmpty<CompilerError>> {
        self.consume(TokenType::OpenParen, None).to_nonempty()?;
        let body_start = self.active_chunk().get_code().next_location();
        self.compile_expression().to_nonempty()?;
        self.consume(TokenType::CloseParen, None).to_nonempty()?;
        self.jumping_body(line, 1 as JumpOffset, OpCode::JumpIfFalse)?;
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
            self.declare_variable(true as CanAssign).to_nonempty()
        } else {
            self.expression_statement().to_nonempty().map(|_| ())
        }?;
        // Condition
        let body_start = self.active_chunk().get_code().next_location();
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
                let result = self.active_chunk().get_code().next_location();
                self.compile_expression().to_nonempty()?;
                self.active_chunk().write(OpCode::Pop, line);
                self.active_chunk().write(OpCode::Jump(body_start), line);
                self.patch_jump(jump_over_increment, 0 as JumpOffset, OpCode::Jump);
                self.consume(TokenType::CloseParen, None).to_nonempty()?;
                Ok(Some(result))
            }?;
        self.statement()?;
        if let Some(cond) = condition_jump {
            self.patch_jump(cond, 1 as JumpOffset, OpCode::JumpIfFalse);
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
        assert!(match self.active_chunk().get_code().get(source).unwrap().0 {
            OpCode::UnpatchedJump => true,
            _ => false,
        });
        (*self.active_chunk().get_mut(source).unwrap()).0 =
            ctor(self.active_chunk().get_code().next_location() + offset);
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

    fn declare_function(&mut self) -> Result<(), NonEmpty<CompilerError>> {
        let (name, line) = self.parse_variable().to_nonempty()?;
        self.consume(TokenType::OpenParen, None).to_nonempty()?;
        self.consume(TokenType::CloseParen, None).to_nonempty()?;
        self.consume(TokenType::OpenBrace, None).to_nonempty()?;
        let mut frame = FunctionFrame::new(self.tokens.clone(), self.current);
        frame.block(line)?;
        let (chunk, new_current) = frame.finish();
        let function = Function { name: name.clone(), chunk, arity: 0 };
        self.current = new_current;
        self.chunk.add_function(function, line);
        self.define_variable(name.clone(), line).to_nonempty()
    }

    fn declare_variable(&mut self, can_assign: bool) -> Result<(), CompilerError> {
        let (name, line) = self.parse_variable()?;
        if self.depth > 0 {
            self.locals.push((name.clone(), UNINITIALIZED));
        }
        if can_assign && self.matches(TokenType::Equal).is_some() {
            self.compile_expression()
        } else {
            self.active_chunk().write(OpCode::Nil, line);
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
        Ok((self.chunk.intern_string(name), line))
    }

    fn define_variable(&mut self, name: InternedString, line: Line) -> Result<(), CompilerError> {
        if self.depth == 0 {
            self.active_chunk().write(OpCode::DefineGlobal(name), line);
            Ok(())
        } else {
            // Skipping the first element because that is the current (uninitialized) local.
            for (local_name, depth) in self.locals.iter().rev().skip(1) {
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
            assert_eq!(self.locals.last().unwrap().0, name);
            self.locals.last_mut().unwrap().1 = self.depth;
            Ok(())
        }
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
                let interned_name = self.chunk.intern_string(name);
                match self.resolve_local(&interned_name, &line)? {
                    Some(index) => {
                        if is_assignment {
                            self.compile_expression()?;
                            self.active_chunk().write(OpCode::SetLocal(index), line);
                        } else {
                            self.active_chunk().write(OpCode::GetLocal(index), line);
                        }
                    }
                    None => {
                        if is_assignment {
                            self.compile_expression()?;
                            self.active_chunk().write(OpCode::SetGlobal(interned_name), line);
                        } else {
                            self.active_chunk().write(OpCode::GetGlobal(interned_name), line);
                        }
                    }
                }
            }
            TokenType::StringLiteral(str) => {
                let interned = self.chunk.intern_string(str);
                self.active_chunk().write(OpCode::String(interned), line);
            }
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
        while !self.is_at_end() && precedence <= Precedence::from(self.peek_type().deref()) {
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
            if !self.is_at_end() && can_assign && self.peek_type().deref() == &TokenType::Equal {
                return Err(CompilerError::new(
                    "Invalid assignment target.",
                    self.tokens.borrow()[self.current].clone(),
                ));
            }
        }
        Ok(last_line)
    }

    fn active_chunk(&mut self) -> &mut Chunk {
        &mut self.chunk
    }

    fn resolve_local(&self, name: &InternedString, line: &Line) -> Result<Option<usize>, CompilerError> {
        for (i, (local_name, depth)) in self.locals.iter().rev().enumerate() {
            if depth == &UNINITIALIZED {
                return Err(CompilerError::new(
                    format!(
                        "Expression uses uninitialized local variable '{}'", name.unwrap_upgrade()),
                    Token::new(*line, TokenType::identifier(name.to_owned())),
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
                self.tokens.borrow().last().expect("empty tokens").to_owned(),
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
        } else if self.peek_type().deref() == &tt {
            let result = self.tokens.borrow()[self.current].line;
            self.advance();
            Some(result)
        } else {
            None
        }
    }

    fn advance(&mut self) -> Token {
        let result = mem::replace(
            self.tokens.borrow_mut().get_mut(self.current).unwrap(),
            Token::new(0, TokenType::Eof),
        );
        self.current += 1;
        result
    }

    fn is_at_end(&self) -> bool {
        self.current == self.tokens.borrow().len()
    }

    fn peek_type(&self) -> Ref<TokenType> {
        Ref::map(self.tokens.borrow(), |tokens| &tokens[self.current].r#type)
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
        let mut expected: Code = Default::default();
        expected.write(OpCode::Number(123.0), 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_compile(vec!["123;"]).get_code(),
            &expected,
        )
    }

    #[test]
    fn grouped_constant() {
        let mut expected: Code = Default::default();
        expected.write(OpCode::Number(123.0), 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            compile(unsafe_tokenize(vec!["(123);"])).unwrap().get_code(),
            &expected,
        )
    }

    #[test]
    fn unary_minus() {
        let mut expected: Code = Default::default();
        expected.write(OpCode::Number(123.0), 1);
        expected.write(OpCode::Negate, 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_compile(vec!["-123;"]).get_code(),
            &expected,
        )
    }

    #[test]
    fn basic_precedence() {
        let mut expected: Code = Default::default();
        expected.write(OpCode::Number(1.0), 1);
        expected.write(OpCode::Negate, 1);
        expected.write(OpCode::Number(2.0), 1);
        expected.write(OpCode::Add, 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_compile(vec!["-1+2;"]).get_code(),
            &expected,
        )
    }

    #[test]
    fn mixed_unary_and_binary() {
        let mut expected: Code = Default::default();
        expected.write(OpCode::Number(1.0), 1);
        expected.write(OpCode::Negate, 1);
        expected.write(OpCode::Number(2.0), 1);
        expected.write(OpCode::Subtract, 1);
        expected.write(OpCode::Pop, 1);
        expected.write(OpCode::Return, 1);
        assert_eq!(
            unsafe_compile(vec!["-1-2;"]).get_code(),
            &expected,
        )
    }

    #[test]
    fn string_interning() {
        let mut expected = HashSet::new();
        expected.insert(Rc::new("str".to_owned()));
        assert_eq!(
            unsafe_compile(vec![r#""str" == "str";"#]).get_interned_strings(),
            &expected,
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
        let mut expected: Chunk = Default::default();
        let w = expected.intern_string("foo".to_owned());
        expected.write(OpCode::Nil, 1);
        expected.write(OpCode::DefineGlobal(w), 1);
        expected.write(OpCode::Return, 1);
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

    #[test]
    fn define_and_print_function() {
        let compiled = unsafe_compile(vec![
            "fun areWeHavingItYet() {",
            "  print \"Yes we are!\";",
            "}",
            "print areWeHavingItYet;",
        ]);
        let mut expected: Chunk = Default::default();
        let w = expected.intern_string("areWeHavingItYet".to_owned());
        expected.write(OpCode::Function(0), 1);
        expected.write(OpCode::DefineGlobal(w.clone()), 1);
        expected.write(OpCode::GetGlobal(w.clone()), 4);
        expected.write(OpCode::Print, 4);
        expected.write(OpCode::Return, 4);
        let mut function_chunk: Chunk = Default::default();
        function_chunk.write(OpCode::Print, 2);
        function_chunk.intern_string("Yes we are!".to_owned());
        expected.add_function(Function {
            name: w,
            arity: 0,
            chunk: function_chunk,
        }, 1);
        assert_deep_eq!(expected, compiled);
    }
}