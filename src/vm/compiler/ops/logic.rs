use crate::parser::{SExpression, Atom};
use crate::vm::vp::{Instr, JumpCondition};
use crate::vm::compiler::{Compiler, CompilationError};

pub fn compile_and(compiler: &mut Compiler, args: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
    if args.is_empty() {
        let reg = compiler.scopes.allocate_reg()?;
        compiler.bytecode.load_atom(&Atom::Boolean(true), reg);
        Ok(reg)
    } else {
        let result_reg = compiler.scopes.allocate_reg()?;
        let mut jump_positions = Vec::new();
        
        for (i, arg) in args.iter().enumerate() {
            let is_last = i == args.len() - 1;
            let reg = compiler.compile_expr(arg, &[], is_tail && is_last)?;
            compiler.bytecode.store_opcode(Instr::CopyReg, result_reg, reg, 0);
            
            if !is_last {
                // If false, jump to end
                compiler.bytecode.store_opcode(Instr::Jump, result_reg, JumpCondition::JumpFalse as u8, 0);
                jump_positions.push(compiler.bytecode.position());
                compiler.bytecode.store_value(&[0; 8]);
            }
        }
        
        let end_pos = compiler.bytecode.position();
        for pos in jump_positions {
            let offset = end_pos - pos - 8;
            compiler.bytecode.store_and_reset_pos(pos, &offset.to_le_bytes());
        }
        compiler.scopes.reset_reg(result_reg + 1);
        Ok(result_reg)
    }
}

pub fn compile_or(compiler: &mut Compiler, args: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
    if args.is_empty() {
        let reg = compiler.scopes.allocate_reg()?;
        compiler.bytecode.load_atom(&Atom::Boolean(false), reg);
        Ok(reg)
    } else {
        let result_reg = compiler.scopes.allocate_reg()?;
        let mut jump_positions = Vec::new();
        
        for (i, arg) in args.iter().enumerate() {
            let is_last = i == args.len() - 1;
            let reg = compiler.compile_expr(arg, &[], is_tail && is_last)?;
            compiler.bytecode.store_opcode(Instr::CopyReg, result_reg, reg, 0);
            
            if !is_last {
                // If true, jump to end
                compiler.bytecode.store_opcode(Instr::Jump, result_reg, JumpCondition::JumpTrue as u8, 0);
                jump_positions.push(compiler.bytecode.position());
                compiler.bytecode.store_value(&[0; 8]);
            }
        }
        
        let end_pos = compiler.bytecode.position();
        for pos in jump_positions {
            let offset = end_pos - pos - 8;
            compiler.bytecode.store_and_reset_pos(pos, &offset.to_le_bytes());
        }
        compiler.scopes.reset_reg(result_reg + 1);
        Ok(result_reg)
    }
}

pub fn compile_not(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.len() != 1 {
        return Err(CompilationError::from("Expected 1 argument for not"));
    }
    let reg = compiler.compile_expr(&args[0], &[], false)?;
    let dest_reg = compiler.scopes.allocate_reg()?;
    compiler.bytecode.store_opcode(Instr::Not, dest_reg, reg, 0);
    compiler.scopes.reset_reg(dest_reg + 1);
    Ok(dest_reg)
}
