use crate::parser::{SExpression, Atom};
use crate::vm::vp::{Instr, JumpCondition};
use crate::instructions::Instruction;
use crate::vm::compiler::{Compiler, CompilationError};

pub fn compile_math_op(compiler: &mut Compiler, instr: &Instruction, args: &[SExpression]) -> Result<u8, CompilationError> {
    let mut reg_args = Vec::new();
    for arg in args {
        let reg = compiler.compile_expr(arg, &[], false)?;
        reg_args.push(reg);
    }
    let dest_reg = compiler.scopes.allocate_reg()?;
    match instr {
        Instruction::Plus => {
            if reg_args.is_empty() {
                    compiler.bytecode.load_atom(&Atom::Float(0.0), dest_reg);
            } else {
                compiler.bytecode.store_opcode(Instr::CopyReg, dest_reg, reg_args[0], 0);
                for i in 1..reg_args.len() {
                    compiler.bytecode.store_opcode(Instr::Add, dest_reg, dest_reg, reg_args[i]);
                }
            }
        },
        Instruction::Multiply => {
            if reg_args.is_empty() {
                    compiler.bytecode.load_atom(&Atom::Float(1.0), dest_reg);
            } else {
                compiler.bytecode.store_opcode(Instr::CopyReg, dest_reg, reg_args[0], 0);
                for i in 1..reg_args.len() {
                    compiler.bytecode.store_opcode(Instr::Mul, dest_reg, dest_reg, reg_args[i]);
                }
            }
        },
        Instruction::Minus => {
            if reg_args.is_empty() {
                return Err(CompilationError::from("Expected at least 1 argument for -"));
            } else if reg_args.len() == 1 {
                    let zero = compiler.scopes.allocate_reg()?;
                    compiler.bytecode.load_atom(&Atom::Float(0.0), zero);
                    compiler.bytecode.store_opcode(Instr::Sub, dest_reg, zero, reg_args[0]);
            } else {
                compiler.bytecode.store_opcode(Instr::CopyReg, dest_reg, reg_args[0], 0);
                for i in 1..reg_args.len() {
                    compiler.bytecode.store_opcode(Instr::Sub, dest_reg, dest_reg, reg_args[i]);
                }
            }
        },
        Instruction::Divide => {
                if reg_args.is_empty() {
                return Err(CompilationError::from("Expected at least 1 argument for /"));
            } else if reg_args.len() == 1 {
                    let one = compiler.scopes.allocate_reg()?;
                    compiler.bytecode.load_atom(&Atom::Float(1.0), one);
                    compiler.bytecode.store_opcode(Instr::Div, dest_reg, one, reg_args[0]);
            } else {
                compiler.bytecode.store_opcode(Instr::CopyReg, dest_reg, reg_args[0], 0);
                for i in 1..reg_args.len() {
                    compiler.bytecode.store_opcode(Instr::Div, dest_reg, dest_reg, reg_args[i]);
                }
            }
        },
        _ => return Err(CompilationError::from("Unknown math instruction"))
    }
    compiler.scopes.reset_reg(dest_reg + 1);
    Ok(dest_reg)
}

pub fn compile_comparison(compiler: &mut Compiler, instr: &Instruction, args: &[SExpression]) -> Result<u8, CompilationError> {
    let mut reg_args = Vec::new();
    for arg in args {
        let reg = compiler.compile_expr(arg, &[], false)?;
        reg_args.push(reg);
    }
    let dest_reg = compiler.scopes.allocate_reg()?;

    if reg_args.len() < 2 {
            compiler.bytecode.load_atom(&Atom::Boolean(true), dest_reg);
    } else {
        compiler.bytecode.load_atom(&Atom::Boolean(true), dest_reg);
        
        let mut jump_positions = Vec::new();

        for i in 0..reg_args.len()-1 {
            let r1 = reg_args[i];
            let r2 = reg_args[i+1];
            let tmp = compiler.scopes.allocate_reg()?;
            match instr {
                Instruction::Eq => compiler.bytecode.store_opcode(Instr::Eq, tmp, r1, r2),
                Instruction::Lt => compiler.bytecode.store_opcode(Instr::Lt, tmp, r1, r2),
                Instruction::Gt => compiler.bytecode.store_opcode(Instr::Gt, tmp, r1, r2),
                Instruction::Leq => compiler.bytecode.store_opcode(Instr::Leq, tmp, r1, r2),
                Instruction::Geq => compiler.bytecode.store_opcode(Instr::Geq, tmp, r1, r2),
                _ => unreachable!()
            }
            compiler.bytecode.store_opcode(Instr::CopyReg, dest_reg, tmp, 0);
            compiler.bytecode.store_opcode(Instr::Jump, dest_reg, JumpCondition::JumpFalse as u8, 0);
            jump_positions.push(compiler.bytecode.position());
            compiler.bytecode.store_value(&[0; 8]);
        }
        
        let end_pos = compiler.bytecode.position();
        for pos in jump_positions {
            let offset = end_pos - pos - 8;
            compiler.bytecode.store_and_reset_pos(pos, &offset.to_le_bytes());
        }
    }
    compiler.scopes.reset_reg(dest_reg + 1);
    Ok(dest_reg)
}
