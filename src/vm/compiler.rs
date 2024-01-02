use crate::instructions::Instruction;
use crate::parser::{SExpression, Atom};
use std::io::Write;
use std::{fmt, io::Cursor};
use std::error::Error;

use super::vp::{VirtualProgram, Instr, OpCode};

#[derive(Debug)]
pub struct CompilationError {
    err: String
}

impl CompilationError {
    fn from(msg: &str) -> CompilationError {
        CompilationError{err: msg.to_string()}
    }
}

impl fmt::Display for CompilationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.err)
    }
}

impl Error for CompilationError {
    fn description(&self) -> &str {
        &self.err
    }
}

impl From<fmt::Error> for CompilationError {
    fn from(value: fmt::Error) -> CompilationError {
        CompilationError{err: value.to_string()}
    }
}

struct BytecodeBuilder {
    cursor: Cursor<Vec<u8>>
}

impl BytecodeBuilder {
    fn new() -> BytecodeBuilder {
        BytecodeBuilder{cursor: Cursor::new(vec![])}
    }

    fn load_atom(&mut self, atom: &Atom, reg: u8) {
        match atom {
            Atom::Boolean(_) => todo!(),
            Atom::Integer(i) => {
                let opcode = OpCode::new(Instr::LoadInt, reg);
                let _ = self.cursor.write(&opcode.get_data());
                let _ = self.cursor.write(&i.to_le_bytes());
            }
            Atom::Float(f) => {
                let opcode = OpCode::new(Instr::LoadFloat, reg);
                let _ = self.cursor.write(&opcode.get_data());
                let _ = self.cursor.write(&f.to_le_bytes());
            },
            Atom::String(_) => todo!(),
        }
    }

    fn store_opcode(&mut self, instr: Instr, dest_reg: u8, r1: u8, r2: u8) {
        let opcode = [instr as u8, dest_reg, r1, r2];
        let _ = self.cursor.write(&opcode);
    }
}

pub struct Compiler {
    bytecode: BytecodeBuilder,
    last_used_reg: u8,
}

impl Compiler {
    const MAX_REG: u8 = 255;

    pub fn new() -> Compiler {
        Compiler{bytecode: BytecodeBuilder::new(), last_used_reg: 0}
    }

    fn allocate_reg(&mut self) -> Result<u8, CompilationError> {
        if self.last_used_reg < Compiler::MAX_REG {
            let reg = self.last_used_reg;
            self.last_used_reg += 1;
            Ok(reg)
        }
        else {
            Err(CompilationError::from("Maximum number of registers exceeded"))
        }
    }

    fn reset_reg(&mut self, reg: u8) {
        self.last_used_reg = reg;
    }

    pub fn compile(&mut self, root: &SExpression) -> Result<VirtualProgram, CompilationError> {
        let reg = self.compile_expr(root, &[])?;
        let mut new_builder = BytecodeBuilder::new();
        std::mem::swap(&mut self.bytecode, &mut new_builder);
        let prog = VirtualProgram::new(new_builder.cursor.into_inner(), reg);
        Ok(prog)
    }

    fn compile_expr(&mut self, root: &SExpression, args: &[SExpression]) -> Result<u8, CompilationError> {
        match root {
            SExpression::Atom(a) => {
                let reg = self.allocate_reg()?;
                self.bytecode.load_atom(a, reg);
                Ok(reg)
            },
            SExpression::BuiltIn(b) => self.compile_builtin(b, args),
            SExpression::Symbol(_) => todo!(),
            SExpression::List(l) => self.compile_list(l),
            SExpression::Lambda(_) => todo!(),
        }
    }

    fn compile_list(&mut self, list: &[SExpression]) -> Result<u8, CompilationError> {
        if !list.is_empty() {
            let expr = &list[0];
            match expr {
                SExpression::Atom(_) => todo!(),
                SExpression::BuiltIn(b) => self.compile_builtin(b, &list[1..]),
                SExpression::Symbol(_) => todo!(),
                SExpression::List(l) => self.compile_list(l),
                SExpression::Lambda(_) => todo!(),
            }
        }
        else {
            Err(CompilationError::from("Empty list")) //TODO
        }
    }

    fn compile_builtin(&mut self, instr: &Instruction, args: &[SExpression]) -> Result<u8, CompilationError> {
        match instr {
            Instruction::Define => todo!(),
            Instruction::Lambda => todo!(),
            Instruction::If => todo!(),
            Instruction::Not => todo!(),
            Instruction::And => todo!(),
            Instruction::Or => todo!(),
            Instruction::Plus => self.compile_binary_op(args, Instr::Add),
            Instruction::Minus => self.compile_binary_op(args, Instr::Sub),
            Instruction::Multiply => self.compile_binary_op(args, Instr::Mul),
            Instruction::Divide => self.compile_binary_op(args, Instr::Div),
            Instruction::Eq => todo!(),
            Instruction::Lt => todo!(),
            Instruction::Gt => todo!(),
            Instruction::Leq => todo!(),
            Instruction::Geq => todo!(),
        }
    }

    fn compile_binary_op(&mut self, args: &[SExpression], instr: Instr) -> Result<u8, CompilationError> {
        if args.len() >= 2 {
            let result_reg = self.compile_expr(&args[0], &[])?;
            for i in 1..args.len() {
                let rnext = self.compile_expr(&args[i], &[])?;
                self.bytecode.store_opcode(instr, result_reg, result_reg, rnext);
                self.reset_reg(result_reg + 1);
            }
            self.reset_reg(result_reg + 1);
            Ok(result_reg)
        }
        else {
            todo!()
        }
    }
}