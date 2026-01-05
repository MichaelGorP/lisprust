use crate::parser::{SExpression, SourceMap};
use crate::vm::vp::{Instr, JumpCondition};
use crate::vm::compiler::{Compiler, CompilationError};
use crate::instructions::Instruction;

fn compile_intrinsic_lambda(compiler: &mut Compiler, instr: Instruction, arg_count: usize, name: &str) -> Result<u8, CompilationError> {
    let mut args_syms = Vec::new();
    let mut args_exprs = Vec::new();
    
    for i in 0..arg_count {
        let sym_name = format!("arg{}", i);
        let sym = SExpression::Symbol(sym_name);
        args_syms.push(sym.clone());
        args_exprs.push(sym);
    }

    let instr_expr = SExpression::BuiltIn(instr);
    let mut body_vec = vec![instr_expr];
    body_vec.extend(args_exprs);
    let body = SExpression::List(body_vec);
    
    let lambda_args_list = SExpression::List(args_syms);
    let lambda_def = vec![lambda_args_list, body];
    
    let func_value_reg = compiler.scopes.allocate_reg()?;
    compiler.compile_lambda_into(&lambda_def, func_value_reg, &[], Some(name), None)
}

pub fn compile_map(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.len() != 2 {
        return Err(CompilationError::from("map expects 2 arguments"));
    }
    
    let map = compiler.current_map();
    let map_list = if let SourceMap::List(_, l) = map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

    compiler.push_map(&map_list[1]);
    let func_reg = compiler.compile_expr(&args[0], &[], false)?;
    compiler.pop_map();

    compiler.push_map(&map_list[2]);
    let list_reg = compiler.compile_expr(&args[1], &[], false)?;
    compiler.pop_map();

    let result_reg = compiler.scopes.allocate_reg()?;
    let temp_reg = compiler.scopes.allocate_reg()?;

    compiler.bytecode.store_opcode(Instr::LoadNil, result_reg, 0, 0);

    let start_pos = compiler.bytecode.cursor.position();

    compiler.bytecode.store_opcode(Instr::Map, func_reg, list_reg, result_reg);
    compiler.bytecode.store_value(&[temp_reg]);
    
    // Loop body: Cons res, temp, res
    compiler.bytecode.store_opcode(Instr::Cons, result_reg, temp_reg, result_reg);
    
    // Jump back to Map
    let end_pos = compiler.bytecode.cursor.position();
    let jump_dist = (start_pos as i64) - (end_pos as i64) - 12;
    compiler.bytecode.store_opcode(Instr::Jump, 0, JumpCondition::Jump as u8, 0);
    compiler.bytecode.store_value(&jump_dist.to_le_bytes());

    Ok(result_reg)
}

pub fn compile_for_each(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.len() != 2 {
        return Err(CompilationError::from("for-each expects 2 arguments"));
    }
    
    let map = compiler.current_map();
    let map_list = if let SourceMap::List(_, l) = map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

    compiler.push_map(&map_list[1]);
    let func_reg = compiler.compile_expr(&args[0], &[], false)?;
    compiler.pop_map();

    compiler.push_map(&map_list[2]);
    let list_reg = compiler.compile_expr(&args[1], &[], false)?;
    compiler.pop_map();

    let temp_reg = compiler.scopes.allocate_reg()?;
    let result_reg = compiler.scopes.allocate_reg()?;

    compiler.bytecode.store_opcode(Instr::ForEach, func_reg, list_reg, 0);
    compiler.bytecode.store_value(&[temp_reg]);
    
    compiler.bytecode.store_opcode(Instr::LoadNil, result_reg, 0, 0);
    Ok(result_reg)
}

pub fn compile_filter(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.len() != 2 {
        return Err(CompilationError::from("filter expects 2 arguments"));
    }
    
    let map = compiler.current_map();
    let map_list = if let SourceMap::List(_, l) = map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

    compiler.push_map(&map_list[1]);
    let func_reg = compiler.compile_expr(&args[0], &[], false)?;
    compiler.pop_map();

    compiler.push_map(&map_list[2]);
    let list_reg = compiler.compile_expr(&args[1], &[], false)?;
    compiler.pop_map();

    let val_reg = compiler.scopes.allocate_reg()?;
    let result_reg = compiler.scopes.allocate_reg()?;
    let temp_reg = compiler.scopes.allocate_reg()?;

    compiler.bytecode.store_opcode(Instr::LoadNil, result_reg, 0, 0);

    let start_pos = compiler.bytecode.cursor.position();

    compiler.bytecode.store_opcode(Instr::Filter, func_reg, list_reg, result_reg);
    compiler.bytecode.store_value(&[temp_reg]);
    compiler.bytecode.store_value(&[val_reg]);
    
    compiler.bytecode.store_opcode(Instr::FilterStep, list_reg, result_reg, temp_reg);
    compiler.bytecode.store_value(&[val_reg]);
    
    let end_pos = compiler.bytecode.cursor.position();
    let jump_dist = (start_pos as i64) - (end_pos as i64) - 12;
    compiler.bytecode.store_opcode(Instr::Jump, 0, JumpCondition::Jump as u8, 0);
    compiler.bytecode.store_value(&jump_dist.to_le_bytes());

    Ok(result_reg)
}

pub fn compile_fold(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.len() != 3 {
        return Err(CompilationError::from("fold expects 3 arguments"));
    }
    
    let map = compiler.current_map();
    let map_list = if let SourceMap::List(_, l) = map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

    compiler.push_map(&map_list[1]);
    let func_reg = compiler.compile_expr(&args[0], &[], false)?;
    compiler.pop_map();

    compiler.push_map(&map_list[2]);
    let acc_reg = compiler.compile_expr(&args[1], &[], false)?;
    compiler.pop_map();

    compiler.push_map(&map_list[3]);
    let list_reg = compiler.compile_expr(&args[2], &[], false)?;
    compiler.pop_map();

    let result_reg = compiler.scopes.allocate_reg()?;
    let temp_reg = compiler.scopes.allocate_reg()?;
    
    compiler.bytecode.store_opcode(Instr::CopyReg, result_reg, acc_reg, 0);
    
    compiler.bytecode.store_opcode(Instr::Fold, func_reg, result_reg, list_reg);
    compiler.bytecode.store_value(&[temp_reg]);
    
    Ok(result_reg)
}

pub fn compile_car(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.is_empty() {
        compile_intrinsic_lambda(compiler, Instruction::Car, 1, "car")
    } else if args.len() == 1 {
        let map = compiler.current_map();
        let map_list: &[SourceMap] = if let SourceMap::List(_, l) = map { l } else { &[] };
        let dummy_map = compiler.current_map();
        
        compiler.push_map(map_list.get(1).unwrap_or(dummy_map));
        let arg_reg = compiler.compile_expr(&args[0], &[], false)?;
        compiler.pop_map();
        
        let result_reg = compiler.scopes.allocate_reg()?;
        compiler.bytecode.store_opcode(Instr::Car, result_reg, arg_reg, 0);
        compiler.scopes.reset_reg(result_reg + 1);
        Ok(result_reg)
    } else {
        Err(CompilationError::from("car expects 1 argument"))
    }
}

pub fn compile_cdr(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.is_empty() {
        compile_intrinsic_lambda(compiler, Instruction::Cdr, 1, "cdr")
    } else if args.len() == 1 {
        let map = compiler.current_map();
        let map_list: &[SourceMap] = if let SourceMap::List(_, l) = map { l } else { &[] };
        let dummy_map = compiler.current_map();
        
        compiler.push_map(map_list.get(1).unwrap_or(dummy_map));
        let arg_reg = compiler.compile_expr(&args[0], &[], false)?;
        compiler.pop_map();
        
        let result_reg = compiler.scopes.allocate_reg()?;
        compiler.bytecode.store_opcode(Instr::Cdr, result_reg, arg_reg, 0);
        compiler.scopes.reset_reg(result_reg + 1);
        Ok(result_reg)
    } else {
        Err(CompilationError::from("cdr expects 1 argument"))
    }
}

pub fn compile_cons(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.is_empty() {
        compile_intrinsic_lambda(compiler, Instruction::Cons, 2, "cons")
    } else if args.len() == 2 {
        let map = compiler.current_map();
        let map_list: &[SourceMap] = if let SourceMap::List(_, l) = map { l } else { &[] };
        let dummy_map = compiler.current_map();
        
        compiler.push_map(map_list.get(1).unwrap_or(dummy_map));
        let arg1_reg = compiler.compile_expr(&args[0], &[], false)?;
        compiler.pop_map();

        compiler.push_map(map_list.get(2).unwrap_or(dummy_map));
        let arg2_reg = compiler.compile_expr(&args[1], &[], false)?;
        compiler.pop_map();
        
        let result_reg = compiler.scopes.allocate_reg()?;
        compiler.bytecode.store_opcode(Instr::Cons, result_reg, arg1_reg, arg2_reg);
        compiler.scopes.reset_reg(result_reg + 1);
        Ok(result_reg)
    } else {
        Err(CompilationError::from("cons expects 2 arguments"))
    }
}

pub fn compile_is_pair(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.is_empty() {
        compile_intrinsic_lambda(compiler, Instruction::IsPair, 1, "pair?")
    } else if args.len() == 1 {
        let map = compiler.current_map();
        let map_list: &[SourceMap] = if let SourceMap::List(_, l) = map { l } else { &[] };
        let dummy_map = compiler.current_map();
        
        compiler.push_map(map_list.get(1).unwrap_or(dummy_map));
        let arg_reg = compiler.compile_expr(&args[0], &[], false)?;
        compiler.pop_map();
        
        let result_reg = compiler.scopes.allocate_reg()?;
        compiler.bytecode.store_opcode(Instr::IsPair, result_reg, arg_reg, 0);
        compiler.scopes.reset_reg(result_reg + 1);
        Ok(result_reg)
    } else {
        Err(CompilationError::from("pair? expects 1 argument"))
    }
}

pub fn compile_is_null(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.is_empty() {
        compile_intrinsic_lambda(compiler, Instruction::IsNull, 1, "null?")
    } else if args.len() == 1 {
        let map = compiler.current_map();
        let map_list: &[SourceMap] = if let SourceMap::List(_, l) = map { l } else { &[] };
        let dummy_map = compiler.current_map();
        
        compiler.push_map(map_list.get(1).unwrap_or(dummy_map));
        let arg_reg = compiler.compile_expr(&args[0], &[], false)?;
        compiler.pop_map();
        
        let result_reg = compiler.scopes.allocate_reg()?;
        compiler.bytecode.store_opcode(Instr::IsNull, result_reg, arg_reg, 0);
        compiler.scopes.reset_reg(result_reg + 1);
        Ok(result_reg)
    } else {
        Err(CompilationError::from("null? expects 1 argument"))
    }
}
