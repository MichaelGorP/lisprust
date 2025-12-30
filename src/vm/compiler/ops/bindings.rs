use crate::parser::{SExpression, SourceMap};
use crate::vm::vp::Instr;
use crate::vm::compiler::{Compiler, CompilationError};
use std::collections::HashSet;

pub fn compile_let(compiler: &mut Compiler, args: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
    if args.len() < 2 {
        Err(CompilationError::from("Expected at least 2 arguments"))
    }
    else {
        let map = compiler.current_map();
        let map_list = if let SourceMap::List(_, l) = map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

        //parse bindings
        let bindings = &args[0];
        let body = &args[1..];
        if let SExpression::List(bindings_list) = bindings {
            let bindings_map = &map_list[1];
            let bindings_map_list = if let SourceMap::List(_, l) = bindings_map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

            //collect init expressions
            let mut init_regs = Vec::new();
            for (i, binding) in bindings_list.iter().enumerate() {
                if let SExpression::List(ref pair) = binding {
                    if pair.len() != 2 {
                        return Err(CompilationError::from("Binding must be (var init)"));
                    }
                    let pair_map = &bindings_map_list[i];
                    let pair_map_list = if let SourceMap::List(_, l) = pair_map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

                    compiler.push_map(&pair_map_list[1]);
                    let init_reg = compiler.compile_expr(&pair[1], &[], false)?;
                    compiler.pop_map();
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
                        let var_reg = compiler.scopes.allocate_reg()?;
                        compiler.scopes.symbols.insert(sym.clone(), var_reg);
                        compiler.bytecode.store_opcode(Instr::CopyReg, var_reg, init_regs[i], 0);
                    }
                    else {
                        return Err(CompilationError::from("First element of binding must be a symbol"));
                    }
                }
            }

            //compile body
            let mut last_reg = 0;
            for (index, (expr, sub_map)) in body.iter().zip(map_list.iter().skip(2)).enumerate() {
                compiler.push_map(sub_map);
                last_reg = compiler.compile_expr(expr, &[], is_tail && index == body.len() - 1)?;
                compiler.pop_map();
            }
            let inner_max = compiler.scopes.max_used_registers;
            compiler.scopes.end_scope();
            compiler.scopes.max_used_registers = std::cmp::max(compiler.scopes.max_used_registers, inner_max);
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
        let map = compiler.current_map();
        let map_list = if let SourceMap::List(_, l) = map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

        //parse bindings
        let bindings = &args[0];
        let body = &args[1..];
        if let SExpression::List(bindings_list) = bindings {
            let bindings_map = &map_list[1];
            let bindings_map_list = if let SourceMap::List(_, l) = bindings_map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

            compiler.scopes.begin_scope();
            // preserve outer register allocation for sequential let* bindings
            if let Some(prev) = compiler.scopes.scope_stack.last() {
                compiler.scopes.last_used_reg = prev.last_used_reg;
                compiler.scopes.max_used_registers = prev.max_used_registers;
            }
            for (i, binding) in bindings_list.iter().enumerate() {
                if let SExpression::List(ref pair) = binding {
                    if pair.len() != 2 {
                        return Err(CompilationError::from("Binding must be (var init)"));
                    }
                    let pair_map = &bindings_map_list[i];
                    let pair_map_list = if let SourceMap::List(_, l) = pair_map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

                    compiler.push_map(&pair_map_list[1]);
                    let init_reg = compiler.compile_expr(&pair[1], &[], false)?;
                    compiler.pop_map();

                    if let SExpression::Symbol(ref sym) = &pair[0] {
                        let var_reg = compiler.scopes.allocate_reg()?;
                        compiler.scopes.symbols.insert(sym.clone(), var_reg);
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
            for (index, (expr, sub_map)) in body.iter().zip(map_list.iter().skip(2)).enumerate() {
                compiler.push_map(sub_map);
                last_reg = compiler.compile_expr(expr, &[], is_tail && index == body.len() - 1)?;
                compiler.pop_map();
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
        let map = compiler.current_map();
        let map_list = if let SourceMap::List(_, l) = map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

        //parse bindings
        let bindings = &args[0];
        let body = &args[1..];
        if let SExpression::List(bindings_list) = bindings {
            let bindings_map = &map_list[1];
            let bindings_map_list = if let SourceMap::List(_, l) = bindings_map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

            compiler.scopes.begin_scope();
            // preserve outer register allocation so nested lexical scopes don't reuse registers
            if let Some(prev) = compiler.scopes.scope_stack.last() {
                compiler.scopes.last_used_reg = prev.last_used_reg;
                compiler.scopes.max_used_registers = prev.max_used_registers;
            }

            //allocate all vars first
            let mut var_regs = Vec::new();
            let mut letrec_vars = HashSet::new();
            for binding in bindings_list {
                if let SExpression::List(ref pair) = binding {
                    if pair.len() != 2 {
                        return Err(CompilationError::from("Binding must be (var init)"));
                    }
                    if let SExpression::Symbol(ref sym) = &pair[0] {
                        let var_reg = compiler.scopes.allocate_reg()?;
                        compiler.scopes.symbols.insert(sym.clone(), var_reg);
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
            for (i, binding) in bindings_list.iter().enumerate() {
                if let SExpression::List(ref pair) = binding {
                    let pair_map = &bindings_map_list[i];
                    let pair_map_list = if let SourceMap::List(_, l) = pair_map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

                    // Step 3: Compile init
                    compiler.push_map(&pair_map_list[1]);
                    let init_reg = compiler.compile_expr(&pair[1], &[], false)?;
                    compiler.pop_map();
                    init_regs.push(init_reg);
                }
            }

            // Step 4: SetRef
            for (init_reg, var_reg) in init_regs.iter().zip(var_regs.iter()) {
                compiler.bytecode.store_opcode(Instr::SetRef, *var_reg, *init_reg, 0);
            }

            //compile body
            let mut last_reg = 0;
            for (index, (expr, sub_map)) in body.iter().zip(map_list.iter().skip(2)).enumerate() {
                compiler.push_map(sub_map);
                last_reg = compiler.compile_expr(expr, &[], is_tail && index == body.len() - 1)?;
                compiler.pop_map();
            }
            let inner_max = compiler.scopes.max_used_registers;
            compiler.scopes.end_scope();
            compiler.scopes.max_used_registers = std::cmp::max(compiler.scopes.max_used_registers, inner_max);
            Ok(last_reg)
        }
        else {
            Err(CompilationError::from("First argument must be a list of bindings"))
        }
    }
}
