use crate::parser::{SExpression, SourceMap};
use crate::vm::vp::Instr;
use crate::vm::compiler::{Compiler, CompilationError};

pub fn compile_define(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.len() != 2 {
        Err(CompilationError::from("Expected 2 arguments"))
    }
    else {
        if let SExpression::Symbol(sym) = &args[0] {
            let map = compiler.current_map();
            let map_list = if let SourceMap::List(_, l) = map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };
            let value_map = &map_list[2];

            compiler.push_map(value_map);
            
            // Check if we are defining a lambda to optimize recursion
            let is_lambda = if let SExpression::List(l) = &args[1] {
                 if let Some(SExpression::BuiltIn(crate::instructions::Instruction::Lambda)) = l.first() {
                     true
                 } else { false }
            } else { false };

            let reg = if is_lambda {
                 if let SExpression::List(l) = &args[1] {
                     let func_value_reg = compiler.scopes.allocate_reg()?;
                     compiler.compile_lambda_into(&l[1..], func_value_reg, &[], Some(sym), None)?
                 } else { unreachable!() }
            } else {
                compiler.compile_expr(&args[1], &[], false)?
            };

            compiler.pop_map();

            if compiler.scopes.scope_stack.is_empty() {
                compiler.bytecode.store_opcode(Instr::Define, reg, 0, 0);
                let symbol_id = compiler.scopes.get_or_intern_symbol(sym);
                compiler.bytecode.store_value(&symbol_id.to_le_bytes());
            } else {
                // Local define (shadowing or internal definition)
                // We just bind the result register to the symbol in the current scope
                compiler.scopes.symbols.insert(sym.clone(), reg);
            }
            Ok(reg)
        }
        else {
            Err(CompilationError::from("Expected a symbol name"))
        }
    }
}

pub fn compile_lambda(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.len() < 2 {
        Err(CompilationError::from("Expected at least 2 arguments"))
    }
    else {
        let func_value_reg = compiler.scopes.allocate_reg()?;
        compiler.compile_lambda_into(args, func_value_reg, &[], None, None)
    }
}
