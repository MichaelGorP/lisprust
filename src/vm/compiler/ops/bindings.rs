use crate::parser::SExpression;
use crate::vm::vp::Instr;
use crate::vm::compiler::{Compiler, CompilationError};
use std::collections::HashSet;

pub fn compile_let(compiler: &mut Compiler, args: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
    if args.len() < 2 {
        Err(CompilationError::from("Expected at least 2 arguments"))
    }
    else {
        //parse bindings
        let bindings = &args[0];
        let body = &args[1..];
        if let SExpression::List(bindings_list) = bindings {
            //collect init expressions
            let mut init_regs = Vec::new();
            for binding in bindings_list {
                if let SExpression::List(ref pair) = binding {
                    if pair.len() != 2 {
                        return Err(CompilationError::from("Binding must be (var init)"));
                    }
                    let init_reg = compiler.compile_expr(&pair[1], &[], false)?;
                    init_regs.push(init_reg);
                }
                else {
                    return Err(CompilationError::from("Binding must be a list"));
                }
            }

            compiler.scopes.begin_scope();
            // preserve outer register allocation so nested lexical scopes don't reuse registers
            if let Some(prev) = compiler.scopes.scope_stack.last() {
                compiler.scopes.last_used_reg = prev.last_used_reg;
                compiler.scopes.max_used_registers = prev.max_used_registers;
            }
            //bind variables
            for (i, binding) in bindings_list.iter().enumerate() {
                if let SExpression::List(ref pair) = binding {
                    if let SExpression::Symbol(ref sym) = &pair[0] {
                        let var_reg = compiler.scopes.find_or_alloc(sym)?;
                        compiler.bytecode.store_opcode(Instr::CopyReg, var_reg, init_regs[i], 0);
                    }
                    else {
                        return Err(CompilationError::from("First element of binding must be a symbol"));
                    }
                }
            }

            //compile body
            let mut last_reg = 0;
            for (index, expr) in body.iter().enumerate() {
                last_reg = compiler.compile_expr(expr, &[], is_tail && index == body.len() - 1)?;
            }
            compiler.scopes.end_scope();
            Ok(last_reg)
        }
        else {
            Err(CompilationError::from("First argument must be a list of bindings"))
        }
    }
}

pub fn compile_let_star(compiler: &mut Compiler, args: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
    if args.len() < 2 {
        Err(CompilationError::from("Expected at least 2 arguments"))
    }
    else {
        //parse bindings
        let bindings = &args[0];
        let body = &args[1..];
        if let SExpression::List(bindings_list) = bindings {
            compiler.scopes.begin_scope();
            // preserve outer register allocation for sequential let* bindings
            if let Some(prev) = compiler.scopes.scope_stack.last() {
                compiler.scopes.last_used_reg = prev.last_used_reg;
                compiler.scopes.max_used_registers = prev.max_used_registers;
            }
            for binding in bindings_list {
                if let SExpression::List(ref pair) = binding {
                    if pair.len() != 2 {
                        return Err(CompilationError::from("Binding must be (var init)"));
                    }
                    let init_reg = compiler.compile_expr(&pair[1], &[], false)?;
                    if let SExpression::Symbol(ref sym) = &pair[0] {
                        let var_reg = compiler.scopes.find_or_alloc(sym)?;
                        compiler.bytecode.store_opcode(Instr::CopyReg, var_reg, init_reg, 0);
                    }
                    else {
                        return Err(CompilationError::from("First element of binding must be a symbol"));
                    }
                }
                else {
                    return Err(CompilationError::from("Binding must be a list"));
                }
            }

            //compile body
            let mut last_reg = 0;
            for (index, expr) in body.iter().enumerate() {
                last_reg = compiler.compile_expr(expr, &[], is_tail && index == body.len() - 1)?;
            }
            compiler.scopes.end_scope();
            Ok(last_reg)
        }
        else {
            Err(CompilationError::from("First argument must be a list of bindings"))
        }
    }
}

pub fn compile_letrec(compiler: &mut Compiler, args: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
    if args.len() < 2 {
        Err(CompilationError::from("Expected at least 2 arguments"))
    }
    else {
        //parse bindings
        let bindings = &args[0];
        let body = &args[1..];
        if let SExpression::List(bindings_list) = bindings {
            compiler.scopes.begin_scope();
            //allocate all vars first
            let mut var_regs = Vec::new();
            let mut letrec_vars = HashSet::new();
            for binding in bindings_list {
                if let SExpression::List(ref pair) = binding {
                    if pair.len() != 2 {
                        return Err(CompilationError::from("Binding must be (var init)"));
                    }
                    if let SExpression::Symbol(ref sym) = &pair[0] {
                        let var_reg = compiler.scopes.find_or_alloc(sym)?;
                        var_regs.push(var_reg);
                        letrec_vars.insert(sym.clone());
                    }
                    else {
                        return Err(CompilationError::from("First element of binding must be a symbol"));
                    }
                }
                else {
                    return Err(CompilationError::from("Binding must be a list"));
                }
            }

            // Step 2: MakeRef for each var
            for reg in &var_regs {
                compiler.bytecode.store_opcode(Instr::MakeRef, *reg, 0, 0);
            }

            //compile init expressions
            let mut init_regs = Vec::new();
            for binding in bindings_list {
                if let SExpression::List(ref pair) = binding {
                    // Step 3: Compile init
                    let init_reg = compiler.compile_expr(&pair[1], &[], false)?;
                    init_regs.push(init_reg);
                }
            }

            // Step 4: SetRef
            for (init_reg, var_reg) in init_regs.iter().zip(var_regs.iter()) {
                compiler.bytecode.store_opcode(Instr::SetRef, *var_reg, *init_reg, 0);
            }

            //compile body
            let mut last_reg = 0;
            for (index, expr) in body.iter().enumerate() {
                last_reg = compiler.compile_expr(expr, &[], is_tail && index == body.len() - 1)?;
            }
            compiler.scopes.end_scope();
            Ok(last_reg)
        }
        else {
            Err(CompilationError::from("First argument must be a list of bindings"))
        }
    }
}
