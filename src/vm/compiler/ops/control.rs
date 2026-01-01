use crate::parser::{SExpression, SourceMap};
use crate::vm::vp::{Instr, JumpCondition};
use crate::vm::compiler::{Compiler, CompilationError};
use std::mem::size_of;

pub fn compile_if(compiler: &mut Compiler, args: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
    if args.len() < 2 || args.len() > 3 {
        Err(CompilationError::from("Expected 2 or 3 arguments"))
    }
    else {
        let map = compiler.current_map();
        let map_list = if let SourceMap::List(_, l) = map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

        // Check for (not ...) optimization
        let mut is_negated = false;
        let condition_expr = &args[0];
        
        let actual_expr = if let SExpression::List(l) = condition_expr {
            let is_not = if let Some(first) = l.first() {
                match first {
                    SExpression::BuiltIn(instr) => matches!(instr, crate::instructions::Instruction::Not),
                    _ => false
                }
            } else {
                false
            };

            if is_not && l.len() == 2 {
                is_negated = true;
                &l[1]
            } else {
                condition_expr
            }
        } else {
            condition_expr
        };

        compiler.push_map(&map_list[1]);
        // If negated, we need to map to the inner expression's map if possible, 
        // but map_list[1] corresponds to the whole (not ...) expression.
        // For simplicity, we just compile the actual_expr. 
        
        let reg = if is_negated {
             // We need to dig into the map to find the map for the inner expression
             if let SourceMap::List(_, sub_l) = &map_list[1] {
                 if sub_l.len() >= 2 {
                     compiler.push_map(&sub_l[1]);
                     let r = compiler.compile_expr(actual_expr, &[], false)?;
                     compiler.pop_map();
                     r
                 } else {
                     compiler.compile_expr(actual_expr, &[], false)?
                 }
             } else {
                 compiler.compile_expr(actual_expr, &[], false)?
             }
        } else {
            compiler.compile_expr(actual_expr, &[], false)?
        };
        
        compiler.pop_map();

        let jump_cond = if is_negated { JumpCondition::JumpTrue } else { JumpCondition::JumpFalse };
        compiler.bytecode.store_opcode(Instr::Jump, reg, jump_cond as u8, 0);
        compiler.scopes.reset_reg(reg); //not needed after the check
        let target_pos = compiler.bytecode.position();
        compiler.bytecode.store_value(&[0; size_of::<i64>()]);
        //compile_expr might return an existing register, so no code is generated. But we need some code for now, so copy to a target register
        let target_reg = compiler.scopes.allocate_reg()?;
        
        compiler.push_map(&map_list[2]);
        let ok_reg = compiler.compile_expr(&args[1], &[], is_tail)?;
        compiler.pop_map();

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
            compiler.push_map(&map_list[3]);
            let ok_reg = compiler.compile_expr(&args[2], &[], is_tail)?;
            compiler.pop_map();

            compiler.bytecode.store_opcode(Instr::CopyReg, target_reg, ok_reg, 0);
            compiler.bytecode.store_and_reset_pos(target_pos, &(compiler.bytecode.position() - target_pos - std::mem::size_of::<i64>() as u64).to_le_bytes());
            compiler.scopes.reset_reg(target_reg + 1)
        }
        compiler.bytecode.store_and_reset_pos(target_pos, &false_jump_target.to_le_bytes());
        Ok(target_reg)
    }
}

pub fn compile_cond(compiler: &mut Compiler, args: &[SExpression], is_tail: bool, map_offset: usize) -> Result<u8, CompilationError> {
    if args.is_empty() {
        let reg = compiler.scopes.allocate_reg()?;
        compiler.bytecode.load_atom(&crate::parser::Atom::Boolean(false), reg);
        return Ok(reg);
    }

    // Get the map for the clause
    let map = compiler.current_map();
    let map_list = if let SourceMap::List(_, l) = map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };
    
    if map_offset >= map_list.len() {
         return Err(CompilationError::from("SourceMap index out of bounds"));
    }
    let clause_map = &map_list[map_offset];
    let clause_map_list = if let SourceMap::List(_, l) = clause_map { l } else { return Err(CompilationError::from("SourceMap mismatch in cond clause")); };

    let clause = &args[0];
    if let SExpression::List(l) = clause {
        if l.is_empty() {
            return Err(CompilationError::from("Empty cond clause"));
        }
        
        let is_else = if let SExpression::Symbol(s) = &l[0] {
            s == "else"
        } else {
            false
        };

        compiler.push_map(clause_map);

        if is_else {
            let mut last_reg = 0;
            for (i, expr) in l.iter().skip(1).enumerate() {
                if i + 1 >= clause_map_list.len() { return Err(CompilationError::from("SourceMap mismatch in else clause")); }
                compiler.push_map(&clause_map_list[i+1]);
                last_reg = compiler.compile_expr(expr, &[], is_tail)?;
                compiler.pop_map();
            }
            compiler.pop_map();
            return Ok(last_reg);
        }

        let target_reg = compiler.scopes.allocate_reg()?;

        let condition = &l[0];
        if clause_map_list.is_empty() { return Err(CompilationError::from("SourceMap mismatch in cond condition")); }
        compiler.push_map(&clause_map_list[0]);
        let cond_reg = compiler.compile_expr(condition, &[], false)?;
        compiler.pop_map();
        
        compiler.bytecode.store_opcode(Instr::Jump, cond_reg, JumpCondition::JumpFalse as u8, 0);
        let jump_pos = compiler.bytecode.position();
        compiler.bytecode.store_value(&[0; size_of::<i64>()]);
        
        let mut result_reg = 0;
        if l.len() > 1 {
            for (i, expr) in l.iter().skip(1).enumerate() {
                let is_last = i == l.len() - 2;
                if i + 1 >= clause_map_list.len() { return Err(CompilationError::from("SourceMap mismatch in cond body")); }
                compiler.push_map(&clause_map_list[i+1]);
                result_reg = compiler.compile_expr(expr, &[], is_tail && is_last)?;
                compiler.pop_map();
            }
        } else {
            result_reg = cond_reg;
        }
        
        compiler.bytecode.store_opcode(Instr::CopyReg, target_reg, result_reg, 0);

        compiler.bytecode.store_opcode(Instr::Jump, 0, JumpCondition::Jump as u8, 0);
        let end_jump_pos = compiler.bytecode.position();
        compiler.bytecode.store_value(&[0; size_of::<i64>()]);
        
        let false_jump_target = compiler.bytecode.position() - jump_pos - size_of::<i64>() as u64;
        compiler.bytecode.store_and_reset_pos(jump_pos, &false_jump_target.to_le_bytes());
        
        compiler.pop_map();

        let else_reg = compile_cond(compiler, &args[1..], is_tail, map_offset + 1)?;
        compiler.bytecode.store_opcode(Instr::CopyReg, target_reg, else_reg, 0);
        
        let end_jump_target = compiler.bytecode.position() - end_jump_pos - size_of::<i64>() as u64;
        compiler.bytecode.store_and_reset_pos(end_jump_pos, &end_jump_target.to_le_bytes());
        
        Ok(target_reg)
    } else {
        Err(CompilationError::from("Invalid cond clause"))
    }
}
