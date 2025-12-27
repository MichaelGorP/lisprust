use crate::parser::SExpression;
use crate::vm::vp::{Instr, JumpCondition};
use crate::vm::compiler::{Compiler, CompilationError};
use std::mem::size_of;

pub fn compile_if(compiler: &mut Compiler, args: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
    if args.len() < 2 || args.len() > 3 {
        Err(CompilationError::from("Expected 2 or 3 arguments"))
    }
    else {
        let reg = compiler.compile_expr(&args[0], &[], false)?;
        compiler.bytecode.store_opcode(Instr::Jump, reg, JumpCondition::JumpFalse as u8, 0);
        compiler.scopes.reset_reg(reg); //not needed after the check
        let target_pos = compiler.bytecode.position();
        compiler.bytecode.store_value(&[0; size_of::<i64>()]);
        //compile_expr might return an existing register, so no code is generated. But we need some code for now, so copy to a target register
        let target_reg = compiler.scopes.allocate_reg()?;
        let ok_reg = compiler.compile_expr(&args[1], &[], is_tail)?;
        compiler.bytecode.store_opcode(Instr::CopyReg, target_reg, ok_reg, 0);
        compiler.scopes.reset_reg(target_reg + 1); //not needed, copied
        //update jump target
        let mut false_jump_target = compiler.bytecode.position() - target_pos - std::mem::size_of::<i64>() as u64;
        if args.len() == 3 {
            //we have to jump past the else expression
            compiler.bytecode.store_opcode(Instr::Jump, reg, JumpCondition::Jump as u8, 0);
            let target_pos = compiler.bytecode.position();
            compiler.bytecode.store_value(&[0; size_of::<i64>()]);
            false_jump_target += 4 + size_of::<i64>() as u64;
            //compile else expression
            let ok_reg = compiler.compile_expr(&args[2], &[], is_tail)?;
            compiler.bytecode.store_opcode(Instr::CopyReg, target_reg, ok_reg, 0);
            compiler.bytecode.store_and_reset_pos(target_pos, &(compiler.bytecode.position() - target_pos - std::mem::size_of::<i64>() as u64).to_le_bytes());
            compiler.scopes.reset_reg(target_reg + 1)
        }
        compiler.bytecode.store_and_reset_pos(target_pos, &false_jump_target.to_le_bytes());
        Ok(target_reg)
    }
}
