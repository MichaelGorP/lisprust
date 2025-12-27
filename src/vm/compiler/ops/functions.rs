use crate::parser::SExpression;
use crate::vm::vp::Instr;
use crate::vm::compiler::{Compiler, CompilationError};

pub fn compile_define(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.len() != 2 {
        Err(CompilationError::from("Expected 2 arguments"))
    }
    else {
        if let SExpression::Symbol(sym) = &args[0] {
            let reg = compiler.compile_expr(&args[1], &[], false)?;
            compiler.bytecode.store_opcode(Instr::Define, reg, 0, 0);
            let symbol_id = compiler.scopes.get_or_intern_symbol(sym);
            compiler.bytecode.store_value(&symbol_id.to_le_bytes());
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
        compiler.compile_lambda_into(args, func_value_reg, &[])
    }
}
