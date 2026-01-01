use crate::parser::{SExpression, SourceMap};
use crate::vm::vp::Instr;
use crate::vm::compiler::{Compiler, CompilationError};

pub fn compile_define(compiler: &mut Compiler, args: &[SExpression]) -> Result<u8, CompilationError> {
    if args.len() < 2 {
        Err(CompilationError::from("Expected at least 2 arguments"))
    }
    else {
        let (sym, body_expr, is_func_def) = if let SExpression::Symbol(s) = &args[0] {
            if args.len() != 2 {
                return Err(CompilationError::from("Expected 2 arguments for variable definition"));
            }
            (s, &args[1], false)
        } else if let SExpression::List(l) = &args[0] {
            if l.is_empty() {
                return Err(CompilationError::from("Expected a symbol name or (name args...)"));
            }
            if let SExpression::Symbol(s) = &l[0] {
                (s, &args[1], true)
            } else {
                return Err(CompilationError::from("Expected a symbol name"));
            }
        } else {
            return Err(CompilationError::from("Expected a symbol name or (name args...)"));
        };

        let map = compiler.current_map();
        let map_list = if let SourceMap::List(_, l) = map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };
        
        let reg = if is_func_def {
            // (define (name args...) body) -> (define name (lambda (args...) body))
            if let SExpression::List(l) = &args[0] {
                let lambda_args = &l[1..];
                let mut lambda_def = Vec::new();
                lambda_def.push(SExpression::List(lambda_args.to_vec()));
                lambda_def.extend_from_slice(&args[1..]);
                
                let func_value_reg = compiler.scopes.allocate_reg()?;
                compiler.compile_lambda_into(&lambda_def, func_value_reg, &[], Some(sym), None)?
            } else { unreachable!() }
        } else {
            let value_map = &map_list[2];
            compiler.push_map(value_map);
            
            // Check if we are defining a lambda to optimize recursion
            let is_lambda = if let SExpression::List(l) = body_expr {
                 if let Some(SExpression::BuiltIn(crate::instructions::Instruction::Lambda)) = l.first() {
                     true
                 } else { false }
            } else { false };

            let res = if is_lambda {
                 if let SExpression::List(l) = body_expr {
                     let func_value_reg = compiler.scopes.allocate_reg()?;
                     compiler.compile_lambda_into(&l[1..], func_value_reg, &[], Some(sym), None)?
                 } else { unreachable!() }
            } else {
                compiler.compile_expr(body_expr, &[], false)?
            };
            
            compiler.pop_map();
            res
        };

        if compiler.scopes.scope_stack.is_empty() {
            compiler.bytecode.store_opcode(Instr::Define, reg, 0, 0);
            let symbol_id = compiler.scopes.get_or_intern_symbol(sym);
            compiler.bytecode.store_value(&symbol_id.to_le_bytes());
        } else {
            compiler.scopes.symbols.insert(sym.clone(), reg);
        }
        Ok(reg)
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
