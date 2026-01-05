use std::collections::{HashSet, HashMap};
use std::fmt;
use std::error::Error;

use crate::instructions::Instruction;
use crate::parser::{SExpression, SourceMap};
use crate::vm::vp::{FunctionHeader, Instr, JumpCondition, VirtualProgram, VmCallableFunction};

use super::bytecode_builder::BytecodeBuilder;
use super::scope_manager::ScopeManager;
use super::function_manager::FunctionRegistry;

use super::ops;

#[derive(Debug)]
pub struct CompilationError {
    err: String
}

impl CompilationError {
    pub fn from(msg: &str) -> CompilationError {
        CompilationError{err: msg.to_string()}
    }
}

impl fmt::Display for CompilationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.err)
    }
}

impl Error for CompilationError {
    fn description(&self) -> &str {
        &self.err
    }
}

impl From<fmt::Error> for CompilationError {
    fn from(value: fmt::Error) -> CompilationError {
        CompilationError{err: value.to_string()}
    }
}

pub struct Compiler<'a> {
    generate_asm: bool,
    pub(super) bytecode: BytecodeBuilder,
    pub(super) scopes: ScopeManager,
    pub(super) functions: FunctionRegistry,
    source_map_stack: Vec<&'a SourceMap>,
    debug_symbols: HashMap<usize, HashMap<u8, String>>,
    current_function: Option<(String, usize, u8, Option<u8>)>,
}

impl<'a> Compiler<'a> {
    pub fn new(generate_asm: bool) -> Compiler<'a> {
        Compiler {
            generate_asm,
            bytecode: BytecodeBuilder::new(generate_asm),
            scopes: ScopeManager::new(),
            functions: FunctionRegistry::new(),
            source_map_stack: Vec::new(),
            debug_symbols: HashMap::new(),
            current_function: None,
        }
    }

    pub fn register_function(&mut self, name: &str, func: VmCallableFunction, arg_count: Option<usize>) {
        self.functions.register_function(name, func, arg_count);
    }

    pub fn compile(&mut self, root: &SExpression, map: &'a SourceMap) -> Result<VirtualProgram, CompilationError> {
        self.source_map_stack.clear();
        self.source_map_stack.push(map);

        let reg = if let SExpression::List(list) = root {
            let mut last_reg = 0;
            if let SourceMap::List(_, map_list) = map {
                for (expr, sub_map) in list.iter().zip(map_list.iter()) {
                    self.source_map_stack.push(sub_map);
                    last_reg = self.compile_expr(expr, &[], false)?;
                    self.source_map_stack.pop();
                    self.scopes.reset_reg(last_reg + 1);
                }
            } else {
                return Err(CompilationError::from("SourceMap mismatch"));
            }
            last_reg
        } else {
            self.compile_expr(root, &[], false)?
        };

        self.bytecode.store_opcode(Instr::Ret, reg, 0, 0);

        let mut new_builder = BytecodeBuilder::new(self.generate_asm);
        std::mem::swap(&mut self.bytecode, &mut new_builder);
        
        let new_functions = self.functions.take_used_functions();
        let bytes = new_builder.cursor.into_inner();
        let source_map = new_builder.source_map;
        let debug_symbols = std::mem::take(&mut self.debug_symbols);

        let prog = VirtualProgram::new(new_builder.listing, bytes, reg, new_functions, source_map, debug_symbols);
        Ok(prog)
    }

    pub(super) fn current_map(&self) -> &'a SourceMap {
        self.source_map_stack.last().expect("Source map stack underflow")
    }

    pub(super) fn push_map(&mut self, map: &'a SourceMap) {
        self.source_map_stack.push(map);
    }

    pub(super) fn pop_map(&mut self) {
        self.source_map_stack.pop();
    }

    pub(super) fn compile_expr(&mut self, root: &SExpression, args: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
        let map = self.current_map();
        self.bytecode.mark_span(map.span());
        match root {
            SExpression::Atom(a) => {
                let reg = self.scopes.allocate_reg()?;
                self.bytecode.load_atom(a, reg);
                Ok(reg)
            },
            SExpression::BuiltIn(b) => self.compile_builtin(b, args, is_tail),
            SExpression::Symbol(s) => {
                let sym_reg;
                if let Some(reg) = self.scopes.find_symbol(s.as_str()) {
                    sym_reg = reg;
                }
                else {
                    sym_reg = self.scopes.allocate_reg()?;
                    let symbol_id = self.scopes.get_or_intern_symbol(s);
                    self.bytecode.store_opcode(Instr::LoadGlobal, sym_reg, 0, 0);
                    self.bytecode.store_value(&symbol_id.to_le_bytes());
                }
                Ok(sym_reg)
            },
            SExpression::List(l) => {
                self.compile_list(l, is_tail)
            },
            SExpression::Lambda(_) => todo!(),
        }
    }

    fn compile_list(&mut self, list: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
        let map = self.current_map();
        let map_list = if let SourceMap::List(_, l) = map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

        if !list.is_empty() {
            let expr = &list[0];
            let expr_map = &map_list[0];
            
            self.push_map(expr_map);

            match expr {
                SExpression::Atom(_) => todo!(),
                SExpression::BuiltIn(b) => {
                    self.pop_map();
                    self.compile_builtin(b, &list[1..], is_tail)
                },
                SExpression::Symbol(s) => {
                    let result_reg = self.scopes.allocate_reg()?;

                    if (s == "map" || s == "for-each" || s == "filter") && list.len() == 3 {
                        self.pop_map();
                        
                        self.push_map(&map_list[1]);
                        let func_reg = self.compile_expr(&list[1], &[], false)?;
                        self.pop_map();

                        self.push_map(&map_list[2]);
                        let list_reg = self.compile_expr(&list[2], &[], false)?;
                        self.pop_map();

                        let val_reg = if s == "filter" {
                            Some(self.scopes.allocate_reg()?)
                        } else {
                            None
                        };

                        let temp_reg = self.scopes.allocate_reg()?;

                        if s == "map" {
                            self.bytecode.store_opcode(Instr::LoadNil, result_reg, 0, 0);
                        } else if s == "filter" {
                            self.bytecode.store_opcode(Instr::LoadNil, result_reg, 0, 0);
                        }

                        let start_pos = self.bytecode.cursor.position();

                        if s == "map" {
                            self.bytecode.store_opcode(Instr::Map, func_reg, list_reg, result_reg);
                            self.bytecode.store_value(&[temp_reg]);
                            
                            // Loop body: Cons res, temp, res
                            self.bytecode.store_opcode(Instr::Cons, result_reg, temp_reg, result_reg);
                            
                            // Jump back to Map
                            let end_pos = self.bytecode.cursor.position();
                            let jump_dist = (start_pos as i64) - (end_pos as i64) - 12;
                            self.bytecode.store_opcode(Instr::Jump, 0, JumpCondition::Jump as u8, 0);
                            self.bytecode.store_value(&jump_dist.to_le_bytes());
                        } else if s == "for-each" {
                            self.bytecode.store_opcode(Instr::ForEach, func_reg, list_reg, 0);
                            self.bytecode.store_value(&[temp_reg]);
                            
                            let end_pos = self.bytecode.cursor.position();
                            let jump_dist = (start_pos as i64) - (end_pos as i64) - 12;
                            self.bytecode.store_opcode(Instr::Jump, 0, JumpCondition::Jump as u8, 0);
                            self.bytecode.store_value(&jump_dist.to_le_bytes());
                            
                            self.bytecode.store_opcode(Instr::LoadNil, result_reg, 0, 0);
                        } else if s == "filter" {
                            let val_reg = val_reg.unwrap();
                            self.bytecode.store_opcode(Instr::Filter, func_reg, list_reg, result_reg);
                            self.bytecode.store_value(&[temp_reg]);
                            self.bytecode.store_value(&[val_reg]);
                            
                            self.bytecode.store_opcode(Instr::FilterStep, list_reg, result_reg, temp_reg);
                            self.bytecode.store_value(&[val_reg]);
                            
                            let end_pos = self.bytecode.cursor.position();
                            let jump_dist = (start_pos as i64) - (end_pos as i64) - 12;
                            self.bytecode.store_opcode(Instr::Jump, 0, JumpCondition::Jump as u8, 0);
                            self.bytecode.store_value(&jump_dist.to_le_bytes());
                        }
                        return Ok(result_reg);
                    } else if s == "fold" && list.len() == 4 {
                        self.pop_map();
                        
                        self.push_map(&map_list[1]);
                        let func_reg = self.compile_expr(&list[1], &[], false)?;
                        self.pop_map();

                        self.push_map(&map_list[2]);
                        let acc_reg = self.compile_expr(&list[2], &[], false)?;
                        self.pop_map();

                        self.push_map(&map_list[3]);
                        let list_reg = self.compile_expr(&list[3], &[], false)?;
                        self.pop_map();

                        let temp_reg = self.scopes.allocate_reg()?;
                        
                        self.bytecode.store_opcode(Instr::CopyReg, result_reg, acc_reg, 0);
                        
                        let start_pos = self.bytecode.cursor.position();
                        self.bytecode.store_opcode(Instr::Fold, func_reg, result_reg, list_reg);
                        self.bytecode.store_value(&[temp_reg]);
                        
                        let end_pos = self.bytecode.cursor.position();
                        let jump_dist = (start_pos as i64) - (end_pos as i64) - 12;
                        self.bytecode.store_opcode(Instr::Jump, 0, JumpCondition::Jump as u8, 0);
                        self.bytecode.store_value(&jump_dist.to_le_bytes());
                        
                        return Ok(result_reg);
                    }

                    //try registered functions first, not overwritable so far
                    let opt_func = self.functions.get_registered_function(s);
                    if let Some((func, expected_args)) = opt_func {
                        self.pop_map();

                        if let Some(count) = expected_args {
                            if list.len() - 1 != count {
                                return Err(CompilationError::from(&format!("Function {} expects {} arguments, got {}", s, count, list.len() - 1)));
                            }
                        }

                        // evaluate all other expressions as arguments
                        let mut arg_regs = Vec::new();
                        for (expr, sub_map) in list.iter().skip(1).zip(map_list.iter().skip(1)) {
                            self.push_map(sub_map);
                            let reg = self.compile_expr(expr, &[], false)?;
                            self.pop_map();
                            arg_regs.push(reg);
                        }

                        // Copy arguments to a contiguous block
                        let start_reg = self.scopes.allocate_reg()?;
                        // Allocate remaining registers
                        for _ in 1..arg_regs.len() {
                            self.scopes.allocate_reg()?;
                        }
                        
                        for (i, reg) in arg_regs.iter().enumerate() {
                            self.bytecode.store_opcode(Instr::CopyReg, start_reg + i as u8, *reg, 0);
                        }

                        let reg_count = arg_regs.len() as u8;
                        
                        // Check for intrinsics
                        if s == "car" && reg_count == 1 {
                            self.bytecode.store_opcode(Instr::Car, result_reg, start_reg, 0);
                        } else if s == "cdr" && reg_count == 1 {
                            self.bytecode.store_opcode(Instr::Cdr, result_reg, start_reg, 0);
                        } else if s == "cons" && reg_count == 2 {
                            self.bytecode.store_opcode(Instr::Cons, result_reg, start_reg, start_reg + 1);
                        } else if s == "pair?" && reg_count == 1 {
                            self.bytecode.store_opcode(Instr::IsPair, result_reg, start_reg, 0);
                        } else if s == "eq?" && reg_count == 2 {
                            self.bytecode.store_opcode(Instr::IsEq, result_reg, start_reg, start_reg + 1);
                        } else if s == "null?" && reg_count == 1 {
                            self.bytecode.store_opcode(Instr::IsNull, result_reg, start_reg, 0);
                        } else {
                            let func_id = self.functions.get_or_insert_used_function(s, func);

                            self.bytecode.store_opcode(Instr::CallFunction, result_reg, start_reg, reg_count);
                            let id: i64 = func_id as i64;
                            self.bytecode.store_value(&id.to_le_bytes());
                        }
                    }
                    else {
                        // Check for self-recursion optimization
                        let mut is_recursive = false;
                        let mut target_addr = 0;
                        let mut target_param_count = 0;
                        
                        if let Some((name, addr, p_count, self_reg)) = &self.current_function {
                            if name == s && is_tail {
                                // Only optimize if the symbol is NOT shadowed by a local variable
                                // OR if the shadowing variable IS the function itself
                                let is_shadowed = if let Some(reg) = self.scopes.find_symbol(s) {
                                    if let Some(sr) = self_reg {
                                        reg != *sr
                                    } else {
                                        true
                                    }
                                } else {
                                    false
                                };
                                
                                if !is_shadowed {
                                    is_recursive = true;
                                    target_addr = *addr;
                                    target_param_count = *p_count;
                                } else {
                                    // Shadowed, not recursive
                                }
                            }
                        }

                        if is_recursive {
                            self.pop_map();
                            
                            let mut arg_regs = Vec::new();
                            for (expr, sub_map) in list.iter().skip(1).zip(map_list.iter().skip(1)) {
                                self.push_map(sub_map);
                                let reg = self.compile_expr(expr, &[], false)?;
                                self.pop_map();
                                arg_regs.push(reg);
                            }
                            
                            if arg_regs.len() != target_param_count as usize {
                                return Err(CompilationError::from(format!("Argument count mismatch for recursive call: expected {}, got {}", target_param_count, arg_regs.len()).as_str()));
                            }

                            for (i, reg) in arg_regs.iter().enumerate() {
                                self.bytecode.store_opcode(Instr::CopyReg, i as u8, *reg, 0);
                            }
                            
                            self.bytecode.store_opcode(Instr::Jump, 0, JumpCondition::Jump as u8, 0);
                            let jump_pos = self.bytecode.position();
                            let dist = (target_addr as i64) - (jump_pos as i64 + 8);
                            self.bytecode.store_value(&dist.to_le_bytes());
                        }
                        else {
                            // Check for intrinsics
                            if s == "car" && list.len() == 2 {
                                self.pop_map();
                                let sub_map = map_list.get(1).unwrap_or(self.current_map());
                                self.push_map(sub_map);
                                let arg_reg = self.compile_expr(&list[1], &[], false)?;
                                self.pop_map();
                                let result_reg = self.scopes.allocate_reg()?;
                                self.bytecode.store_opcode(Instr::Car, result_reg, arg_reg, 0);
                                self.scopes.reset_reg(result_reg + 1);
                                return Ok(result_reg);
                            } else if s == "cdr" && list.len() == 2 {
                                self.pop_map();
                                let sub_map = map_list.get(1).unwrap_or(self.current_map());
                                self.push_map(sub_map);
                                let arg_reg = self.compile_expr(&list[1], &[], false)?;
                                self.pop_map();
                                let result_reg = self.scopes.allocate_reg()?;
                                self.bytecode.store_opcode(Instr::Cdr, result_reg, arg_reg, 0);
                                self.scopes.reset_reg(result_reg + 1);
                                return Ok(result_reg);
                            } else if s == "cons" && list.len() == 3 {
                                self.pop_map();
                                let sub_map1 = map_list.get(1).unwrap_or(self.current_map());
                                self.push_map(sub_map1);
                                let arg1_reg = self.compile_expr(&list[1], &[], false)?;
                                self.pop_map();
                                let sub_map2 = map_list.get(2).unwrap_or(self.current_map());
                                self.push_map(sub_map2);
                                let arg2_reg = self.compile_expr(&list[2], &[], false)?;
                                self.pop_map();
                                let result_reg = self.scopes.allocate_reg()?;
                                self.bytecode.store_opcode(Instr::Cons, result_reg, arg1_reg, arg2_reg);
                                self.scopes.reset_reg(result_reg + 1);
                                return Ok(result_reg);
                            } else if s == "pair?" && list.len() == 2 {
                                self.pop_map();
                                let sub_map = map_list.get(1).unwrap_or(self.current_map());
                                self.push_map(sub_map);
                                let arg_reg = self.compile_expr(&list[1], &[], false)?;
                                self.pop_map();
                                let result_reg = self.scopes.allocate_reg()?;
                                self.bytecode.store_opcode(Instr::IsPair, result_reg, arg_reg, 0);
                                self.scopes.reset_reg(result_reg + 1);
                                return Ok(result_reg);
                            } else if s == "eq?" && list.len() == 3 {
                                self.pop_map();
                                let sub_map1 = map_list.get(1).unwrap_or(self.current_map());
                                self.push_map(sub_map1);
                                let arg1_reg = self.compile_expr(&list[1], &[], false)?;
                                self.pop_map();
                                let sub_map2 = map_list.get(2).unwrap_or(self.current_map());
                                self.push_map(sub_map2);
                                let arg2_reg = self.compile_expr(&list[2], &[], false)?;
                                self.pop_map();
                                let result_reg = self.scopes.allocate_reg()?;
                                self.bytecode.store_opcode(Instr::IsEq, result_reg, arg1_reg, arg2_reg);
                                self.scopes.reset_reg(result_reg + 1);
                                return Ok(result_reg);
                            } else if s == "null?" && list.len() == 2 {
                                self.pop_map();
                                let sub_map = map_list.get(1).unwrap_or(self.current_map());
                                self.push_map(sub_map);
                                let arg_reg = self.compile_expr(&list[1], &[], false)?;
                                self.pop_map();
                                let result_reg = self.scopes.allocate_reg()?;
                                self.bytecode.store_opcode(Instr::IsNull, result_reg, arg_reg, 0);
                                self.scopes.reset_reg(result_reg + 1);
                                return Ok(result_reg);
                            }

                            let sym_reg; //register for symbol
                            if let Some(reg) = self.scopes.find_symbol(s.as_str()) {
                                sym_reg = reg;
                            }
                            else {
                                sym_reg = self.scopes.allocate_reg()?;
                                let symbol_id = self.scopes.get_or_intern_symbol(s);
                                self.bytecode.store_opcode(Instr::LoadGlobal, sym_reg, 0, 0);
                                self.bytecode.store_value(&symbol_id.to_le_bytes());
                            }

                            self.pop_map();

                            // Resolve sym_reg through aliases to find the definition register
                            // With runtime closures, we don't need to manually copy captures here.
                            // The VM handles unpacking captures from the closure object.
                            
                            let mut arg_regs = Vec::new();
                            
                            // Fix for map mismatch: if map_list is shorter than list (e.g. synthetic lambda), reuse last map or current map
                            let dummy_map = self.current_map();
                            let mut map_iter = map_list.iter().skip(1);
                            
                            for expr in list.iter().skip(1) {
                                let sub_map = map_iter.next().unwrap_or(dummy_map);
                                self.push_map(sub_map);
                                let reg = self.compile_expr(expr, &[], false)?;
                                self.pop_map();
                                arg_regs.push(reg);
                            }

                            // Copy arguments to a contiguous block
                            let start_reg = self.scopes.allocate_reg()?;
                            // Allocate remaining registers
                            for _ in 1..arg_regs.len() {
                                self.scopes.allocate_reg()?;
                            }
                            
                            for (i, reg) in arg_regs.iter().enumerate() {
                                self.bytecode.store_opcode(Instr::CopyReg, start_reg + i as u8, *reg, 0);
                            }
                            let reg_count = arg_regs.len() as u8;

                            if is_tail {
                                // If the function register is within the parameter area we're about to overwrite,
                                // move it to a safe temporary register first.
                                let mut final_sym_reg = sym_reg;
                                // Check if sym_reg is in the target area (0..reg_count)
                                // Note: For tail calls, we copy to 0..reg_count.
                                if sym_reg < reg_count {
                                    let temp_reg = self.scopes.allocate_reg()?;
                                    self.bytecode.store_opcode(Instr::CopyReg, temp_reg, sym_reg, 0);
                                    final_sym_reg = temp_reg;
                                }

                                // For tail-calls the VM expects parameters to live in the
                                // low parameter area (registers starting at 0 relative to
                                // the current window). Move the evaluated argument
                                // registers into that area. Use temporaries to avoid
                                // clobbering when source/dest overlap.
                                if reg_count > 0 {
                                    let mut temps: Vec<u8> = Vec::new();
                                    for i in 0..(reg_count as usize) {
                                        let src = (start_reg as usize + i) as u8;
                                        let temp = self.scopes.allocate_reg()?;
                                        self.bytecode.store_opcode(Instr::CopyReg, temp, src, 0);
                                        temps.push(temp);
                                    }
                                    for i in 0..(reg_count as usize) {
                                        let dest = i as u8; // param slots start at register 0
                                        let temp = temps[i];
                                        self.bytecode.store_opcode(Instr::CopyReg, dest, temp, 0);
                                    }
                                }
                                self.bytecode.store_opcode(Instr::TailCallSymbol, final_sym_reg, 0, result_reg);
                            }
                            else {
                                self.bytecode.store_opcode(Instr::CallSymbol, sym_reg, start_reg, result_reg);
                            }
                        }
                    }
                    self.scopes.reset_reg(result_reg + 1);
                    Ok(result_reg)
                },
                SExpression::List(l) => {
                    // Treat as function call: ((func-expr) args...)
                    let func_reg = self.compile_list(l, false)?;
                    self.pop_map();
                    
                    let mut arg_regs = Vec::new();
                    for (expr, sub_map) in list.iter().skip(1).zip(map_list.iter().skip(1)) {
                        self.push_map(sub_map);
                        let reg = self.compile_expr(expr, &[], false)?;
                        self.pop_map();
                        arg_regs.push(reg);
                    }

                    // Copy arguments to a contiguous block
                    let start_reg = self.scopes.allocate_reg()?;
                    // Allocate remaining registers
                    for _ in 1..arg_regs.len() {
                        self.scopes.allocate_reg()?;
                    }
                    
                    for (i, reg) in arg_regs.iter().enumerate() {
                        self.bytecode.store_opcode(Instr::CopyReg, start_reg + i as u8, *reg, 0);
                    }
                    let reg_count = arg_regs.len() as u8;
                    
                    let result_reg = self.scopes.allocate_reg()?;
                    
                    if is_tail {
                        if reg_count > 0 {
                            let mut temps: Vec<u8> = Vec::new();
                            for i in 0..(reg_count as usize) {
                                let src = (start_reg as usize + i) as u8;
                                let temp = self.scopes.allocate_reg()?;
                                self.bytecode.store_opcode(Instr::CopyReg, temp, src, 0);
                                temps.push(temp);
                            }
                            for i in 0..(reg_count as usize) {
                                let dest = i as u8; 
                                let temp = temps[i];
                                self.bytecode.store_opcode(Instr::CopyReg, dest, temp, 0);
                            }
                        }
                        self.bytecode.store_opcode(Instr::TailCallSymbol, func_reg, 0, result_reg);
                    } else {
                        self.bytecode.store_opcode(Instr::CallSymbol, func_reg, start_reg, result_reg);
                    }
                    self.scopes.reset_reg(result_reg + 1);
                    Ok(result_reg)
                },
                SExpression::Lambda(_) => todo!(),
            }
        }
        else {
            Err(CompilationError::from("Illegal empty application"))
        }
    }

    pub(super) fn compile_lambda_into(&mut self, args: &[SExpression], func_value_reg: u8, forced_captures: &[String], name: Option<&str>, self_binding: Option<u8>) -> Result<u8, CompilationError> {
        // Jump past the lambda body (unconditional jump)
        let jump_addr = self.bytecode.position();
        self.bytecode.store_opcode(Instr::Jump, 0, JumpCondition::Jump as u8, 0);
        self.bytecode.store_value(&0i64.to_le_bytes());

        self.scopes.begin_scope();
        let header_addr = self.bytecode.position();
        // Placeholder for header
        self.bytecode.store_value(&[0; std::mem::size_of::<FunctionHeader>()]);

        //register parameters
        let mut param_count: u8 = 0;
        if let SExpression::List(arg_list) = &args[0] {
            for param in arg_list {
                if let SExpression::Symbol(sym) = param {
                    let reg = self.scopes.allocate_reg()?;
                    self.scopes.symbols.insert(sym.clone(), reg);
                    param_count = param_count.saturating_add(1);
                }
            }
        }

        // Set current function for recursion optimization
        let prev_func = self.current_function.clone();
        if let Some(n) = name {
            self.current_function = Some((n.to_string(), self.bytecode.position() as usize, param_count, self_binding));
        }

        self.scopes.fixed_registers = param_count;
        self.scopes.last_used_reg = self.scopes.fixed_registers;

        // collect captured symbols (free vars) used in the lambda body
        let mut captured_syms: HashSet<String> = HashSet::new();
        fn collect_symbols(expr: &SExpression, out: &mut HashSet<String>) {
            match expr {
                SExpression::Symbol(s) => { out.insert(s.clone()); },
                SExpression::List(list) => { for e in list { collect_symbols(e, out); } },
                _ => {}
            }
        }
        for expr in args.iter().skip(1) {
            collect_symbols(expr, &mut captured_syms);
        }
        
        for cap in forced_captures {
            captured_syms.insert(cap.clone());
        }

        // Sort captured symbols to ensure deterministic register allocation
        let mut sorted_captures: Vec<String> = captured_syms.into_iter().collect();
        sorted_captures.sort();

        // allocate local registers for captured symbols and record mapping (outer_reg, local_reg)
        let mut capture_pairs: Vec<(u8,u8)> = Vec::new();
        for sym in sorted_captures {
            // skip parameters (already in self.symbols)
            if self.scopes.symbols.get(sym.as_str()).is_some() {
                continue;
            }
            // find outer scope register
            let mut found_outer: Option<u8> = None;
            for scope in self.scopes.scope_stack.iter().rev() {
                if let Some(reg) = scope.symbols.get(sym.as_str()) {
                    found_outer = Some(*reg);
                    break;
                }
            }
            if let Some(outer_reg) = found_outer {
                // allocate a new local register for the captured name
                let local_reg = self.scopes.allocate_reg()?;
                self.scopes.symbols.insert(sym.as_str(), local_reg);
                capture_pairs.push((outer_reg, local_reg));
                self.scopes.aliases.insert(local_reg, outer_reg);
            }
        }

        let map = self.current_map();
        let map_list = if let SourceMap::List(_, l) = map { l } else { return Err(CompilationError::from("SourceMap mismatch")); };

        // Scan for internal definitions (letrec semantics)
        let mut internal_defines: Vec<(usize, String, u8)> = Vec::new();
        for (i, expr) in args.iter().skip(1).enumerate() {
            if let SExpression::List(l) = expr {
                if let Some(SExpression::BuiltIn(Instruction::Define)) = l.first() {
                    if l.len() == 3 {
                        if let SExpression::Symbol(name) = &l[1] {
                            let reg = self.scopes.allocate_reg()?;
                            self.scopes.symbols.insert(name.clone(), reg);
                            internal_defines.push((i, name.clone(), reg));
                            
                            // Initialize with Ref(Empty)
                            // We load 0 (Integer) as a placeholder
                            self.bytecode.store_opcode(Instr::LoadInt, reg, 0, 0);
                            self.bytecode.store_value(&0i64.to_le_bytes());
                            self.bytecode.store_opcode(Instr::MakeRef, reg, 0, 0);
                            
                            continue;
                        }
                    }
                }
            }
            break;
        }

        let base_reg = self.scopes.last_used_reg;
        let mut last_reg = 0;
        for (index, (expr, sub_map)) in args.iter().skip(1).zip(map_list.iter().skip(2)).enumerate() {
            self.push_map(sub_map);
            
            let define_info = internal_defines.iter().find(|(i, _, _)| *i == index);
            
            if let Some((_, name, reg)) = define_info {
                if let SExpression::List(l) = expr {
                    let value_expr = &l[2];
                    let value_map = if let SourceMap::List(_, maps) = sub_map {
                        if maps.len() > 2 { &maps[2] } else { sub_map }
                    } else { sub_map };
                    
                    self.push_map(value_map);
                    
                    let is_lambda = if let SExpression::List(vl) = value_expr {
                         if let Some(SExpression::BuiltIn(Instruction::Lambda)) = vl.first() {
                             true
                         } else { false }
                    } else { false };

                    // Compile to a temporary register to avoid overwriting the Ref
                    let temp_reg = self.scopes.allocate_reg()?;

                    let val_reg = if is_lambda {
                         if let SExpression::List(vl) = value_expr {
                             self.compile_lambda_into(&vl[1..], temp_reg, &[], Some(name), Some(*reg))?
                         } else { unreachable!() }
                    } else {
                        self.compile_expr(value_expr, &[], false)?
                    };
                    
                    self.pop_map();
                    
                    // Update the Ref with the compiled value
                    self.bytecode.store_opcode(Instr::SetRef, *reg, val_reg, 0);
                    
                    last_reg = *reg;
                }
            } else {
                last_reg = self.compile_expr(expr, &[], index == args.len() - 2)?;
            }

            self.pop_map();
            self.scopes.reset_reg(base_reg);
        }
        self.scopes.reset_reg(last_reg + 1); //keep the result reg of the last expression
        self.bytecode.store_opcode(Instr::Ret, 0, 0, 0);

        let header = FunctionHeader{param_count: self.scopes.fixed_registers, register_count: self.scopes.max_used_registers, result_reg: last_reg};
        self.bytecode.store_and_reset_pos(header_addr, header.as_u8_slice());

        // Capture debug symbols
        let mut symbols = HashMap::new();
        for (name, reg) in self.scopes.symbols.iter() {
             symbols.insert(*reg, name.to_string());
        }
        self.debug_symbols.insert(header_addr as usize, symbols);

        self.current_function = prev_func;

        self.scopes.end_scope();

        let pos = self.bytecode.position();
        // Jump instruction is 4 bytes (OpCode) + 8 bytes (i64).
        // We want to jump from (jump_addr + 12) to pos.
        // dist = pos - (jump_addr + 12)
        let dist = pos - jump_addr - 12;
        
        // Store distance at jump_addr + 4 (skipping OpCode)
        self.bytecode.store_and_reset_pos(jump_addr + 4, &dist.to_le_bytes());
        //the return of a compiled lambda is a function reference
        let reg = func_value_reg;
        self.bytecode.store_opcode(Instr::LoadFuncRef, reg, 0, 0);
        self.bytecode.store_value(&header_addr.to_le_bytes());

        // Emit MakeClosure instruction
        // We need to collect the registers for the captured variables
        let mut capture_regs = Vec::new();
        for (outer_reg, _local_reg) in &capture_pairs {
            capture_regs.push(*outer_reg);
        }
        
        if !capture_regs.is_empty() {
            self.bytecode.store_make_closure(reg, reg, &capture_regs);
        }

        Ok(reg)
    }

    fn compile_builtin(&mut self, instr: &Instruction, args: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
        match instr {
            Instruction::Define => ops::functions::compile_define(self, args),
            Instruction::Lambda => ops::functions::compile_lambda(self, args),
            Instruction::If => ops::control::compile_if(self, args, is_tail),
            Instruction::Let => ops::bindings::compile_let(self, args, is_tail),
            Instruction::LetStar => ops::bindings::compile_let_star(self, args, is_tail),
            Instruction::Letrec => ops::bindings::compile_letrec(self, args, is_tail),
            Instruction::Cond => ops::control::compile_cond(self, args, is_tail, 1),
            Instruction::Quote => ops::bindings::compile_quote(self, args),
            Instruction::And => ops::logic::compile_and(self, args, is_tail),
            Instruction::Or => ops::logic::compile_or(self, args, is_tail),
            Instruction::Not => ops::logic::compile_not(self, args),
            Instruction::Plus | Instruction::Minus | Instruction::Multiply | Instruction::Divide => {
                ops::math::compile_math_op(self, instr, args)
            },
            Instruction::Eq | Instruction::Lt | Instruction::Gt | Instruction::Leq | Instruction::Geq => {
                ops::math::compile_comparison(self, instr, args)
            }
        }
    }
}
