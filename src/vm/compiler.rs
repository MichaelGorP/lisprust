use crate::instructions::Instruction;
use crate::parser::{SExpression, Atom};
use std::io::Write;
use std::mem::size_of;
use std::{fmt, io::Cursor};
use std::error::Error;

use super::vp::{VirtualProgram, Instr, OpCode, JumpCondition};

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
            Atom::Boolean(b) => {
                let opcode = OpCode::new(Instr::LoadBool, reg, *b as u8, 0);
                let _ = self.cursor.write(&opcode.get_data());
            },
            Atom::Integer(i) => {
                let opcode = OpCode::new_dest(Instr::LoadInt, reg);
                let _ = self.cursor.write(&opcode.get_data());
                let _ = self.cursor.write(&i.to_le_bytes());
            }
            Atom::Float(f) => {
                let opcode = OpCode::new_dest(Instr::LoadFloat, reg);
                let _ = self.cursor.write(&opcode.get_data());
                let _ = self.cursor.write(&f.to_le_bytes());
            },
            Atom::String(s) => {
                let opcode = OpCode::new_dest(Instr::LoadFloat, reg);
                let _ = self.cursor.write(&opcode.get_data());
                let _ = self.cursor.write(&s.len().to_le_bytes());
                let _ = self.cursor.write(s.as_bytes());
            },
        }
    }

    fn store_opcode(&mut self, instr: Instr, dest_reg: u8, r1: u8, r2: u8) {
        let opcode = [instr as u8, dest_reg, r1, r2];
        let _ = self.cursor.write(&opcode);
    }

    fn store_value(&mut self, val: &[u8]) {
        let _ = self.cursor.write(&val);
    }

    fn store_at(&mut self, pos: u64, val: &[u8]) {
        self.cursor.set_position(pos);
        let _ = self.cursor.write(val);
    }

    fn position(&self) -> u64 {
        self.cursor.position()
    }

    fn set_position(&mut self, pos: u64) {
        self.cursor.set_position(pos);
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
            Instruction::Not => {
                if args.len() != 1 {
                    Err(CompilationError::from("Expected 1 argument"))
                }
                else {
                    let reg = self.compile_expr(&args[0], &[])?;
                    self.bytecode.store_opcode(Instr::Not, reg, reg, 0);
                    Ok(reg)
                }
            },
            Instruction::And => {
                let mut result_reg = 0;
                //empty and evaluates to true
                if args.is_empty() {
                    //write true into target register
                    let result_reg = self.allocate_reg()?;
                    self.bytecode.load_atom(&Atom::Boolean(true), result_reg);
                }
                //positions of jump marks
                let mut jump_marks : Vec<u64> = vec![];
                for (i, expr) in args.iter().enumerate() {
                    result_reg = self.compile_expr(expr, &[])?;
                    if i == args.len() - 1 {
                        //after the last check, write false into target register. If the check succeeded, skip it
                        self.bytecode.store_opcode(Instr::Jump, result_reg, JumpCondition::JumpTrue as u8, 0);
                        self.bytecode.store_value(&(4 as i64).to_le_bytes()); //skip one opcode

                        //now, we have the jump target for all other jumps
                        let jump_target = self.bytecode.position();
                        self.bytecode.load_atom(&Atom::Boolean(false), result_reg);

                        //replace all jump targets
                        let end = self.bytecode.position();
                        for pos in &jump_marks {
                            let distance : i64 = (jump_target - pos - size_of::<i64>() as u64) as i64;
                            self.bytecode.store_at(*pos,&distance.to_le_bytes());
                        }
                        self.bytecode.set_position(end);
                    }
                    else {
                        //if the condition did not evaluate to true, jump to end and skip all other checks
                        self.bytecode.store_opcode(Instr::Jump, result_reg, JumpCondition::JumpFalse as u8, 0);
                        jump_marks.push(self.bytecode.position());
                        self.bytecode.store_value(&[0; size_of::<i64>()]);
                    }
                    self.reset_reg(result_reg);
                }
                self.reset_reg(result_reg + 1);
                Ok(result_reg)
            },
            Instruction::Or => {
                let mut result_reg = 0;
                //empty or evaluates to false
                if args.is_empty() {
                    //write false into target register
                    let result_reg = self.allocate_reg()?;
                    self.bytecode.load_atom(&Atom::Boolean(false), result_reg);
                }
                //positions of jump marks
                let mut jump_marks : Vec<u64> = vec![];
                for (i, expr) in args.iter().enumerate() {
                    result_reg = self.compile_expr(expr, &[])?;
                    if i == args.len() - 1 {
                        //now, we have the jump target for all other jumps
                        let jump_target = self.bytecode.position();

                        //replace all jump targets
                        let end = self.bytecode.position();
                        for pos in &jump_marks {
                            let distance : i64 = (jump_target - pos - size_of::<i64>() as u64) as i64;
                            self.bytecode.store_at(*pos,&distance.to_le_bytes());
                        }
                        self.bytecode.set_position(end);
                    }
                    else {
                        //if the condition did not evaluate to false, jump to end and skip all other checks
                        self.bytecode.store_opcode(Instr::Jump, result_reg, JumpCondition::JumpTrue as u8, 0);
                        jump_marks.push(self.bytecode.position());
                        self.bytecode.store_value(&[0; size_of::<i64>()]);
                    }
                    self.reset_reg(result_reg);
                }
                self.reset_reg(result_reg + 1);
                Ok(result_reg)
            },
            Instruction::Plus => self.compile_binary_op(args, Instr::Add),
            Instruction::Minus => self.compile_binary_op(args, Instr::Sub),
            Instruction::Multiply => self.compile_binary_op(args, Instr::Mul),
            Instruction::Divide => self.compile_binary_op(args, Instr::Div),
            Instruction::Eq => self.compile_comparison_op(args, Instr::Eq),
            Instruction::Lt => self.compile_comparison_op(args, Instr::Lt),
            Instruction::Gt => self.compile_comparison_op(args, Instr::Gt),
            Instruction::Leq => self.compile_comparison_op(args, Instr::Leq),
            Instruction::Geq => self.compile_comparison_op(args, Instr::Geq),
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

    fn compile_comparison_op(&mut self, args: &[SExpression], instr: Instr) -> Result<u8, CompilationError> {
        let result_reg = self.allocate_reg()?;
        self.bytecode.load_atom(&Atom::Boolean(true), result_reg);
        if args.is_empty() {    
            Ok(result_reg)
        }
        else {
            let r1 = self.compile_expr(&args[0], &[])?;
            if args.len() >= 2 {
                for i in 1..args.len() {
                    let rnext = self.compile_expr(&args[i], &[])?;
                    self.bytecode.store_opcode(instr, result_reg, r1, rnext);
                    if i < args.len() - 1 {
                        self.bytecode.store_opcode(Instr::CopyReg, r1, rnext, 0)
                    }
                    self.reset_reg(r1 + 1)
                }
            }
            else {
                //compare it to itself to check the type and produce the result true
                self.bytecode.store_opcode(Instr::Eq, result_reg, r1, r1);
            }
            self.reset_reg(result_reg + 1);
            Ok(result_reg)
        }
    }
}