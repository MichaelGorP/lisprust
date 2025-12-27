use case_insensitive_hashmap::CaseInsensitiveHashMap;

use crate::instructions::Instruction;
use crate::parser::{SExpression, Atom};
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::mem::size_of;
use std::{fmt, io::Cursor};
use std::error::Error;

use super::vp::{FunctionHeader, Instr, JumpCondition, OpCode, VirtualProgram, VmCallableFunction};

#[derive(Debug)]
pub struct CompilationError {
    err: String
}

impl CompilationError {
    fn from(msg: &str) -> CompilationError {
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

struct BytecodeBuilder {
    cursor: Cursor<Vec<u8>>,
    listing: String,
    generate_asm: bool
}

impl BytecodeBuilder {
    fn new(generate_asm: bool) -> BytecodeBuilder {
        BytecodeBuilder{cursor: Cursor::new(vec![]), listing: String::new(), generate_asm}
    }

    fn load_atom(&mut self, atom: &Atom, reg: u8) {
        match atom {
            Atom::Boolean(b) => {
                let opcode = OpCode::new(Instr::LoadBool, reg, *b as u8, 0);
                let _ = self.cursor.write(&opcode.get_data());

                if self.generate_asm {
                    self.listing += &format!("{} {}, {}\n", Instr::LoadBool, reg, *b);
                }
            },
            Atom::Integer(i) => {
                let opcode = OpCode::new_dest(Instr::LoadInt, reg);
                let _ = self.cursor.write(&opcode.get_data());
                let _ = self.cursor.write(&i.to_le_bytes());

                if self.generate_asm {
                    self.listing += &format!("{} {}, {}\n", Instr::LoadInt, reg, *i);
                }
            }
            Atom::Float(f) => {
                let opcode = OpCode::new_dest(Instr::LoadFloat, reg);
                let _ = self.cursor.write(&opcode.get_data());
                let _ = self.cursor.write(&f.to_le_bytes());
                if self.generate_asm {
                    self.listing += &format!("{} {}, {}\n", Instr::LoadFloat, reg, *f);
                }
            },
            Atom::String(s) => {
                let opcode = OpCode::new_dest(Instr::LoadString, reg);
                let _ = self.cursor.write(&opcode.get_data());
                let _ = self.cursor.write(&s.len().to_le_bytes());
                let _ = self.cursor.write(s.as_bytes());
                if self.generate_asm {
                    self.listing += &format!("{} {}, {}\n", Instr::LoadString, reg, s);
                }
            },
        }
    }

    fn store_opcode(&mut self, instr: Instr, dest_reg: u8, r1: u8, r2: u8) {
        let opcode = [instr as u8, dest_reg, r1, r2];
        let _ = self.cursor.write(&opcode);

        if self.generate_asm {
            self.listing += &format!("{} {}, {}, {}\n", instr, dest_reg, r1, r2);
        }
    }

    fn store_value(&mut self, val: &[u8]) {
        let _ = self.cursor.write(&val);

        if self.generate_asm {
            self.listing += &format!("[data; {}]", val.len());
        }
    }

    fn store_at(&mut self, pos: u64, val: &[u8]) {
        self.cursor.set_position(pos);
        let _ = self.cursor.write(val);
    }

    fn store_and_reset_pos(&mut self, pos: u64, val: &[u8]) {
        let cur_pos = self.cursor.position();
        self.cursor.set_position(pos);
        let _ = self.cursor.write(val);
        self.cursor.set_position(cur_pos);
    }



    fn position(&self) -> u64 {
        self.cursor.position()
    }

    fn set_position(&mut self, pos: u64) {
        self.cursor.set_position(pos);
    }
}

struct CompilationScope {
    last_used_reg: u8,
    max_used_registers: u8,
    fixed_registers: u8,
    symbols: CaseInsensitiveHashMap<u8>,
    aliases: HashMap<u8, u8>
}

struct SymbolInterner {
    lookup: CaseInsensitiveHashMap<i64>,
    last_id: i64
}

impl SymbolInterner {
    fn new() -> SymbolInterner {
        SymbolInterner{lookup: CaseInsensitiveHashMap::new(), last_id: 0}
    }

    fn get_or_intern(&mut self, symbol: &str) -> i64 {
        *self.lookup.entry(symbol).or_insert_with(|| { self.last_id += 1; self.last_id })
    }
}

pub struct Compiler {
    generate_asm: bool,
    registered_functions: HashMap<String, VmCallableFunction>,
    used_functions: Vec<VmCallableFunction>,
    function_lookup: HashMap<String, usize>,
    // map from function-value-register -> captured pairs (outer_reg, local_reg)
    captured_map: HashMap<u8, Vec<(u8, u8)>>,
        // map from function-value-register -> function header address in bytecode
        function_value_addrs: HashMap<u8, u64>,
    bytecode: BytecodeBuilder,
    last_used_reg: u8,
    fixed_registers: u8,
    max_used_registers: u8,
    symbols: CaseInsensitiveHashMap<u8>,
    aliases: HashMap<u8, u8>,
    interner: SymbolInterner, //for global symbols
    scope_stack: Vec<CompilationScope>
}

impl Compiler {
    const MAX_REG: u8 = 255;

    pub fn new(generate_asm: bool) -> Compiler {
        Compiler{generate_asm, registered_functions: HashMap::new(), used_functions: Vec::new(), function_lookup: HashMap::new(), captured_map: HashMap::new(), function_value_addrs: HashMap::new(), bytecode: BytecodeBuilder::new(generate_asm), last_used_reg: 0, fixed_registers: 0, max_used_registers: 0, symbols: CaseInsensitiveHashMap::new(), aliases: HashMap::new(), interner: SymbolInterner::new(), scope_stack: Vec::new()}
    }

    pub fn register_function(&mut self, name: &str, func: VmCallableFunction) {
        self.registered_functions.insert(name.into(), func);
    }

    fn begin_scope(&mut self) {
        let mut new_symbols = CaseInsensitiveHashMap::new();
        std::mem::swap(&mut self.symbols, &mut new_symbols);
        let mut new_aliases = HashMap::new();
        std::mem::swap(&mut self.aliases, &mut new_aliases);
        let current_scope = CompilationScope{last_used_reg: self.last_used_reg, max_used_registers: self.max_used_registers, fixed_registers: self.fixed_registers, symbols: new_symbols, aliases: new_aliases};
        self.scope_stack.push(current_scope);
        self.last_used_reg = 0;
        self.max_used_registers = 0;
    }

    fn end_scope(&mut self) {
        if let Some(last_scope) = self.scope_stack.pop() {
            self.last_used_reg = last_scope.last_used_reg;
            self.fixed_registers = last_scope.fixed_registers;
            self.max_used_registers = last_scope.max_used_registers;
            self.symbols = last_scope.symbols;
            self.aliases = last_scope.aliases;
        }
    }

    fn find_or_alloc(&mut self, symbol: &str) -> Result<u8, CompilationError> {
        if let Some(reg) = self.find_symbol(symbol) {
            return Ok(reg);
        }
        let reg = self.allocate_reg()?;
        self.symbols.insert(symbol, reg);
        Ok(reg)
    }

    fn find_symbol(&self, symbol: &str) -> Option<u8> {
        if let Some(reg) = self.symbols.get(symbol) {
            return Some(*reg);
        }
        for scope in self.scope_stack.iter().rev() {
            if let Some(reg) = scope.symbols.get(symbol) {
                return Some(*reg);
            }
        }
        None
    }

    fn allocate_reg(&mut self) -> Result<u8, CompilationError> {
        if self.last_used_reg < Compiler::MAX_REG {
            let reg = self.last_used_reg;
            self.last_used_reg += 1;
            self.max_used_registers = std::cmp::max(self.max_used_registers, self.last_used_reg);
            Ok(reg)
        }
        else {
            Err(CompilationError::from("Maximum number of registers exceeded"))
        }
    }

    fn reset_reg(&mut self, reg: u8) {
        if reg >= self.fixed_registers {
            self.last_used_reg = reg;
        }
    }

    pub fn compile(&mut self, root: &SExpression) -> Result<VirtualProgram, CompilationError> {
        let reg = self.compile_expr(root, &[], false)?;
        let mut new_builder = BytecodeBuilder::new(self.generate_asm);
        std::mem::swap(&mut self.bytecode, &mut new_builder);
        let mut new_functions = Vec::new();
        std::mem::swap(&mut self.used_functions, &mut new_functions);
        self.function_lookup.clear();
        let bytes = new_builder.cursor.into_inner();

        let prog = VirtualProgram::new(new_builder.listing, bytes, reg, new_functions);
        Ok(prog)
    }

    fn compile_expr(&mut self, root: &SExpression, args: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
        match root {
            SExpression::Atom(a) => {
                let reg = self.allocate_reg()?;
                self.bytecode.load_atom(a, reg);
                Ok(reg)
            },
            SExpression::BuiltIn(b) => self.compile_builtin(b, args, is_tail),
            SExpression::Symbol(s) => {
                let sym_reg;
                if let Some(reg) = self.find_symbol(s.as_str()) {
                    sym_reg = reg;
                }
                else {
                    sym_reg = self.allocate_reg()?;
                    let symbol_id = self.interner.get_or_intern(s);
                    self.bytecode.store_opcode(Instr::LoadGlobal, sym_reg, 0, 0);
                    self.bytecode.store_value(&symbol_id.to_le_bytes());
                }
                Ok(sym_reg)
            },
            SExpression::List(l) => self.compile_list(l, is_tail),
            SExpression::Lambda(_) => todo!(),
        }
    }

    fn compile_list(&mut self, list: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
        if !list.is_empty() {
            let expr = &list[0];
            match expr {
                SExpression::Atom(_) => todo!(),
                SExpression::BuiltIn(b) => self.compile_builtin(b, &list[1..], is_tail),
                SExpression::Symbol(s) => {
                    let result_reg = self.allocate_reg()?;
                    //try registered functions first, not overwritable so far
                    let opt_func = self.registered_functions.get(s).copied();
                    if let Some(func) = opt_func {
                        // evaluate all other expressions as arguments
                        let start_reg = self.last_used_reg;
                        for expr in list.iter().skip(1) {
                            let reg = self.compile_expr(expr, &[], false)?;
                            // copy parameters into new registers if they reside in fixed parameter area
                            if reg <= self.fixed_registers {
                                let target_reg = self.allocate_reg()?;
                                self.bytecode.store_opcode(Instr::CopyReg, target_reg, reg, 0);
                            }
                        }

                        let reg_count = self.last_used_reg - start_reg;
                        let func_id = self.function_lookup.entry(s.to_string()).or_insert_with(|| {self.used_functions.push(func); self.used_functions.len()});

                        self.bytecode.store_opcode(Instr::CallFunction, result_reg, start_reg, reg_count);
                        let id: i64 = *func_id as i64;
                        self.bytecode.store_value(&id.to_le_bytes());
                    }
                    else {
                        let sym_reg; //register for symbol
                        if let Some(reg) = self.find_symbol(s.as_str()) {
                            sym_reg = reg;
                        }
                        else {
                            sym_reg = self.allocate_reg()?;
                            let symbol_id = self.interner.get_or_intern(s);
                            self.bytecode.store_opcode(Instr::LoadGlobal, sym_reg, 0, 0);
                            self.bytecode.store_value(&symbol_id.to_le_bytes());
                        }

                        // Resolve sym_reg through aliases to find the definition register
                        let mut current_reg = sym_reg;
                        let mut found_captures = self.captured_map.get(&current_reg).cloned();
                        
                        if found_captures.is_none() {
                             if let Some(outer) = self.aliases.get(&current_reg) {
                                 current_reg = *outer;
                                 found_captures = self.captured_map.get(&current_reg).cloned();
                                 
                                 if found_captures.is_none() {
                                     for scope in self.scope_stack.iter().rev() {
                                         if let Some(outer) = scope.aliases.get(&current_reg) {
                                             current_reg = *outer;
                                             found_captures = self.captured_map.get(&current_reg).cloned();
                                             if found_captures.is_some() { break; }
                                         } else {
                                             break;
                                         }
                                     }
                                 }
                             }
                        }

                        // Before evaluating arguments, snapshot any outer capture sources
                        // so argument evaluation cannot overwrite them. We create a
                        // temporary map from original outer reg -> snapshot reg for
                        // use when emitting the captured CopyReg instructions later.
                        let mut snapshot_map: std::collections::HashMap<u8,u8> = std::collections::HashMap::new();
                        if let Some(captures) = &found_captures {
                            for (outer, _local) in captures.iter() {
                                // Translate outer (def_reg) to current scope register
                                let mut src_reg = *outer;
                                for (l, o) in self.aliases.iter() {
                                    if *o == *outer {
                                        src_reg = *l;
                                        break;
                                    }
                                }
                                
                                let temp = self.allocate_reg()?;
                                // copy current outer value into the temp register
                                self.bytecode.store_opcode(Instr::CopyReg, temp, src_reg, 0);
                                snapshot_map.insert(*outer, temp);
                            }
                        }

                        let start_reg = self.last_used_reg;
                        for expr in list.iter().skip(1) {
                            let reg = self.compile_expr(expr, &[], false)?;
                            // copy parameters into new registers if they reside in fixed parameter area
                            if reg <= self.fixed_registers {
                                let target_reg = self.allocate_reg()?;
                                self.bytecode.store_opcode(Instr::CopyReg, target_reg, reg, 0);
                            }
                        }
                        let reg_count = self.last_used_reg - start_reg;

                        // emit copy ops for captured variables if this symbol is a compiled lambda value
                        // For tail-calls we need to defer emitting the CopyReg ops until after
                        // we've moved evaluated args into the low parameter slots, otherwise
                        // the subsequent param shuffling can overwrite the captured slots.
                        let mut deferred_captures: Vec<(u8,u8)> = Vec::new();
                        
                        if let Some(captures) = found_captures {
                            // ensure there are enough registers reserved for callee locals
                            let mut max_local: usize = 0;
                            for (_outer, local) in captures.iter() {
                                if *local as usize > max_local { max_local = *local as usize; }
                            }
                            let start_usize = start_reg as usize;
                            let needed = start_usize + max_local + 1;
                            while (self.last_used_reg as usize) <= (needed - 1) {
                                let _ = self.allocate_reg()?;
                            }
                            for (outer, local) in captures.iter() {
                                // Destination depends on whether this is a tail-call.
                                // For tail-calls parameters live at the low param
                                // slots (0..), so use that area. For normal calls
                                // use the `start_usize` area where arguments were
                                // evaluated.
                                let dest = if is_tail {
                                    (*local) as u8
                                } else {
                                    (start_usize + *local as usize) as u8
                                };
                                
                                // Translate outer (def_reg) to current scope register
                                let mut src_reg = *outer;
                                for (l, o) in self.aliases.iter() {
                                    if *o == *outer {
                                        src_reg = *l;
                                        break;
                                    }
                                }

                                // If the captured local index falls within the evaluated
                                // argument area (i.e. local < reg_count), prefer the
                                // post-evaluation register `outer` so we pass the
                                // updated argument value to the callee. Only use
                                // the pre-eval snapshot temp when writing into
                                // non-parameter locals to protect outer sources
                                // from being clobbered by argument evaluation.
                                let src = if (*local as usize) < (reg_count as usize) {
                                    src_reg
                                } else {
                                    if let Some(s) = snapshot_map.get(outer) { *s } else { src_reg }
                                };
                                if is_tail {
                                    // Defer actual emission until after tail-call param move
                                    deferred_captures.push((dest, src));
                                } else {
                                    self.bytecode.store_opcode(Instr::CopyReg, dest, src, 0);
                                }
                            }
                        }
                        if is_tail {
                            // For tail-calls the VM expects parameters to live in the
                            // low parameter area (registers starting at 0 relative to
                            // the current window). Move the evaluated argument
                            // registers into that area. Use temporaries to avoid
                            // clobbering when source/dest overlap.
                            if reg_count > 0 {
                                let mut temps: Vec<u8> = Vec::new();
                                for i in 0..(reg_count as usize) {
                                    let src = (start_reg as usize + i) as u8;
                                    let temp = self.allocate_reg()?;
                                    self.bytecode.store_opcode(Instr::CopyReg, temp, src, 0);
                                    temps.push(temp);
                                }
                                for i in 0..(reg_count as usize) {
                                    let dest = i as u8; // param slots start at register 0
                                    let temp = temps[i];
                                    self.bytecode.store_opcode(Instr::CopyReg, dest, temp, 0);
                                }
                            }
                            self.bytecode.store_opcode(Instr::TailCallSymbol, sym_reg, 0, result_reg);
                            // Emit any deferred capture copies now that param slots are populated
                            for (dest, src) in deferred_captures.iter() {
                                self.bytecode.store_opcode(Instr::CopyReg, *dest, *src, 0);
                            }
                        }
                        else {
                            self.bytecode.store_opcode(Instr::CallSymbol, sym_reg, start_reg, result_reg);
                            // non-tail: any deferred_captures would be empty, but handle defensively
                            for (dest, src) in deferred_captures.iter() {
                                self.bytecode.store_opcode(Instr::CopyReg, *dest, *src, 0);
                            }
                        }
                    }
                    self.reset_reg(result_reg + 1);
                    Ok(result_reg)
                },
                SExpression::List(l) => {
                    let ret = self.compile_list(l, is_tail)?;
                    if list.len() == 1 {
                        Ok(ret)
                    }
                    else {
                        self.compile_list(&list[1..], is_tail)
                    }
                },
                SExpression::Lambda(_) => todo!(),
            }
        }
        else {
            Err(CompilationError::from("Empty list")) //TODO
        }
    }

    fn compile_lambda_into(&mut self, args: &[SExpression], func_value_reg: u8, forced_captures: &[String]) -> Result<u8, CompilationError> {
        //jump past the lambda body
        self.bytecode.store_opcode(Instr::Jump, 0, JumpCondition::Jump as u8, 0);
        let jump_addr = self.bytecode.position();
        self.bytecode.store_value(&[0; std::mem::size_of::<i64>()]);

        self.begin_scope();
        let header_addr = self.bytecode.position();
        self.bytecode.store_value(&[0; std::mem::size_of::<FunctionHeader>()]);
        //register parameters
        let mut param_count: u8 = 0;
        if let SExpression::List(arg_list) = &args[0] {
            for param in arg_list {
                if let SExpression::Symbol(sym) = param {
                    self.find_or_alloc(sym.as_str())?;
                    param_count = param_count.saturating_add(1);
                }
            }
        }
        self.fixed_registers = param_count;
        self.last_used_reg = self.fixed_registers;

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
            if self.symbols.get(sym.as_str()).is_some() {
                continue;
            }
            // find outer scope register
            let mut found_outer: Option<u8> = None;
            for scope in self.scope_stack.iter().rev() {
                if let Some(reg) = scope.symbols.get(sym.as_str()) {
                    found_outer = Some(*reg);
                    break;
                }
            }
            if let Some(outer_reg) = found_outer {
                // allocate a new local register for the captured name
                let local_reg = self.allocate_reg()?;
                self.symbols.insert(sym.as_str(), local_reg);
                capture_pairs.push((outer_reg, local_reg));
                self.aliases.insert(local_reg, outer_reg);
            }
        }

        // Insert capture map keyed by the target register
        if !capture_pairs.is_empty() {
            self.captured_map.insert(func_value_reg, capture_pairs.clone());
        }
        let mut last_reg = 0;
        for (index, expr) in args.iter().skip(1).enumerate() {
            last_reg = self.compile_expr(expr, &[], index == args.len() - 2)?;
            self.reset_reg(last_reg);
        }
        self.reset_reg(last_reg + 1); //keep the result reg of the last expression
        self.bytecode.store_opcode(Instr::Ret, 0, 0, 0);

        let header = FunctionHeader{param_count: self.fixed_registers, register_count: self.max_used_registers, result_reg: last_reg};
        self.bytecode.store_and_reset_pos(header_addr, header.as_u8_slice());

        self.end_scope();

        self.bytecode.store_and_reset_pos(jump_addr, &(self.bytecode.position() - jump_addr - std::mem::size_of::<i64>() as u64).to_le_bytes());
        //the return of a compiled lambda is a function reference
        let reg = func_value_reg;
        self.bytecode.store_opcode(Instr::LoadFuncRef, reg, 0, 0);
        self.bytecode.store_value(&header_addr.to_le_bytes());

        // record mapping from function-value register to header address
        self.function_value_addrs.insert(reg, header_addr);

        // If we inserted an early CAPTURE_MAP we already added it; if not, add now
        if capture_pairs.is_empty() == false && !self.captured_map.contains_key(&reg) {
            self.captured_map.insert(reg, capture_pairs);
        }

        Ok(reg)
    }

    fn compile_builtin(&mut self, instr: &Instruction, args: &[SExpression], is_tail: bool) -> Result<u8, CompilationError> {
        match instr {
            Instruction::Define => {
                if args.len() != 2 {
                    Err(CompilationError::from("Expected 2 arguments"))
                }
                else {
                    if let SExpression::Symbol(sym) = &args[0] {
                        let reg = self.compile_expr(&args[1], &[], false)?;
                        self.bytecode.store_opcode(Instr::Define, reg, 0, 0);
                        let symbol_id = self.interner.get_or_intern(sym);
                        self.bytecode.store_value(&symbol_id.to_le_bytes());
                        Ok(reg)
                    }
                    else {
                        Err(CompilationError::from("Expected a symbol name"))
                    }
                }
            },
            Instruction::Lambda => {
                if args.len() < 2 {
                    Err(CompilationError::from("Expected at least 2 arguments"))
                }
                else {
                    let func_value_reg = self.allocate_reg()?;
                    self.compile_lambda_into(args, func_value_reg, &[])
                }
            },
            Instruction::If => {
                if args.len() < 2 || args.len() > 3 {
                    Err(CompilationError::from("Expected 2 or 3 arguments"))
                }
                else {
                    let reg = self.compile_expr(&args[0], &[], false)?;
                    self.bytecode.store_opcode(Instr::Jump, reg, JumpCondition::JumpFalse as u8, 0);
                    self.reset_reg(reg); //not needed after the check
                    let target_pos = self.bytecode.position();
                    self.bytecode.store_value(&[0; size_of::<i64>()]);
                    //compile_expr might return an existing register, so no code is generated. But we need some code for now, so copy to a target register
                    let target_reg = self.allocate_reg()?;
                    let ok_reg = self.compile_expr(&args[1], &[], is_tail)?;
                    self.bytecode.store_opcode(Instr::CopyReg, target_reg, ok_reg, 0);
                    self.reset_reg(target_reg + 1); //not needed, copied
                    //update jump target
                    let mut false_jump_target = self.bytecode.position() - target_pos - std::mem::size_of::<i64>() as u64;
                    if args.len() == 3 {
                        //we have to jump past the else expression
                        self.bytecode.store_opcode(Instr::Jump, reg, JumpCondition::Jump as u8, 0);
                        let target_pos = self.bytecode.position();
                        self.bytecode.store_value(&[0; size_of::<i64>()]);
                        false_jump_target += 4 + size_of::<i64>() as u64;
                        //compile else expression
                        let ok_reg = self.compile_expr(&args[2], &[], is_tail)?;
                        self.bytecode.store_opcode(Instr::CopyReg, target_reg, ok_reg, 0);
                        self.bytecode.store_and_reset_pos(target_pos, &(self.bytecode.position() - target_pos - std::mem::size_of::<i64>() as u64).to_le_bytes());
                        self.reset_reg(target_reg + 1)
                    }
                    self.bytecode.store_and_reset_pos(target_pos, &false_jump_target.to_le_bytes());
                    Ok(target_reg)
                }
            },
            Instruction::Let => {
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
                                if let SExpression::Symbol(_) = &pair[0] {
                                    let init_reg = self.compile_expr(&pair[1], &[], false)?;
                                    init_regs.push(init_reg);
                                }
                                else {
                                    return Err(CompilationError::from("First element of binding must be a symbol"));
                                }
                            }
                            else {
                                return Err(CompilationError::from("Binding must be a list"));
                            }
                        }
                        //now begin scope and allocate vars
                        self.begin_scope();
                        // preserve outer register allocation so nested lexical scopes don't reuse registers
                        if let Some(prev) = self.scope_stack.last() {
                            self.last_used_reg = prev.last_used_reg;
                            self.max_used_registers = prev.max_used_registers;
                        }
                        // preserve outer register allocation so nested lexical scopes don't reuse registers
                        if let Some(prev) = self.scope_stack.last() {
                            self.last_used_reg = prev.last_used_reg;
                            self.max_used_registers = prev.max_used_registers;
                        }
                        let mut var_regs = Vec::new();
                        for binding in bindings_list {
                            if let SExpression::List(ref pair) = binding {
                                if let SExpression::Symbol(ref sym) = &pair[0] {
                                    let var_reg = self.find_or_alloc(sym)?;
                                    var_regs.push(var_reg);
                                }
                            }
                        }
                        //copy from init_regs to var_regs
                        for (init_reg, var_reg) in init_regs.iter().zip(var_regs.iter()) {
                            self.bytecode.store_opcode(Instr::CopyReg, *var_reg, *init_reg, 0);
                            if let Some(caps) = self.captured_map.get(init_reg).cloned() {
                                self.captured_map.insert(*var_reg, caps);
                                if let Some(addr) = self.function_value_addrs.get(init_reg) {
                                    self.function_value_addrs.insert(*var_reg, *addr);
                                }
                            }
                        }
                        //compile body
                        let mut last_reg = 0;
                        for (index, expr) in body.iter().enumerate() {
                            last_reg = self.compile_expr(expr, &[], is_tail && index == body.len() - 1)?;
                        }
                        self.end_scope();
                        Ok(last_reg)
                    }
                    else {
                        Err(CompilationError::from("First argument must be a list of bindings"))
                    }
                }
            },
            Instruction::LetStar => {
                if args.len() < 2 {
                    Err(CompilationError::from("Expected at least 2 arguments"))
                }
                else {
                    let bindings = &args[0];
                    let body = &args[1..];
                        if let SExpression::List(bindings_list) = bindings {
                        self.begin_scope();
                        // preserve outer register allocation for letrec
                        if let Some(prev) = self.scope_stack.last() {
                            self.last_used_reg = prev.last_used_reg;
                            self.max_used_registers = prev.max_used_registers;
                        }
                        // preserve outer register allocation for sequential let* bindings
                        if let Some(prev) = self.scope_stack.last() {
                            self.last_used_reg = prev.last_used_reg;
                            self.max_used_registers = prev.max_used_registers;
                        }
                        for binding in bindings_list {
                            if let SExpression::List(ref pair) = binding {
                                if pair.len() != 2 {
                                    return Err(CompilationError::from("Binding must be (var init)"));
                                }
                                if let SExpression::Symbol(ref sym) = &pair[0] {
                                    let init_reg = self.compile_expr(&pair[1], &[], false)?;
                                    let var_reg = self.find_or_alloc(sym)?;
                                        self.bytecode.store_opcode(Instr::CopyReg, var_reg, init_reg, 0);
                                        if let Some(caps) = self.captured_map.get(&init_reg).cloned() {
                                            self.captured_map.insert(var_reg, caps);
                                            if let Some(addr) = self.function_value_addrs.get(&init_reg) {
                                                self.function_value_addrs.insert(var_reg, *addr);
                                            }
                                        }
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
                            last_reg = self.compile_expr(expr, &[], is_tail && index == body.len() - 1)?;
                        }
                        self.end_scope();
                        Ok(last_reg)
                    }
                    else {
                        Err(CompilationError::from("First argument must be a list of bindings"))
                    }
                }
            },
            Instruction::Letrec => {
                if args.len() < 2 {
                    Err(CompilationError::from("Expected at least 2 arguments"))
                }
                else {
                    let bindings = &args[0];
                    let body = &args[1..];
                    if let SExpression::List(bindings_list) = bindings {
                        self.begin_scope();
                        //allocate all vars first
                        let mut var_regs = Vec::new();
                        let mut letrec_vars = HashSet::new();
                        for binding in bindings_list {
                            if let SExpression::List(ref pair) = binding {
                                if pair.len() != 2 {
                                    return Err(CompilationError::from("Binding must be (var init)"));
                                }
                                if let SExpression::Symbol(ref sym) = &pair[0] {
                                    let var_reg = self.find_or_alloc(sym)?;
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
                        // Pre-analyze lambdas to populate captured_map early.
                        for (i, binding) in bindings_list.iter().enumerate() {
                            if let SExpression::List(ref pair) = binding {
                                if let SExpression::List(inner) = &pair[1] {
                                    if !inner.is_empty() {
                                        if let SExpression::BuiltIn(Instruction::Lambda) = inner[0] {
                                            let args = &inner[1..];
                                            if args.len() >= 2 {
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
                                                
                                                // Force capture of all letrec variables to support mutual recursion
                                                for var in &letrec_vars {
                                                    captured_syms.insert(var.clone());
                                                }
                                                
                                                let mut params = HashSet::new();
                                                if let SExpression::List(arg_list) = &args[0] {
                                                    for param in arg_list {
                                                        if let SExpression::Symbol(sym) = param {
                                                            params.insert(sym.clone());
                                                        }
                                                    }
                                                }
                                                
                                                let mut sorted_captures: Vec<String> = captured_syms.into_iter().collect();
                                                sorted_captures.sort();
                                                
                                                let mut capture_pairs: Vec<(u8,u8)> = Vec::new();
                                                let mut local_reg_idx = params.len() as u8;
                                                
                                                for sym in sorted_captures {
                                                    if params.contains(&sym) { continue; }
                                                    
                                                    let mut found_outer: Option<u8> = None;
                                                    for scope in self.scope_stack.iter().rev() {
                                                        if let Some(reg) = scope.symbols.get(sym.as_str()) {
                                                            found_outer = Some(*reg);
                                                            break;
                                                        }
                                                    }
                                                    
                                                    if let Some(outer_reg) = found_outer {
                                                        capture_pairs.push((outer_reg, local_reg_idx));
                                                        local_reg_idx += 1;
                                                    }
                                                }
                                                
                                                if !capture_pairs.is_empty() {
                                                    self.captured_map.insert(var_regs[i], capture_pairs);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        //now compile inits
                        for (i, binding) in bindings_list.iter().enumerate() {
                            if let SExpression::List(ref pair) = binding {
                                // If initializer is a lambda literal, compile it directly into
                                // the binding register to avoid a separate temp func reg
                                // and subsequent CopyReg which can confuse captured_map keys.
                                let is_inline_lambda = match &pair[1] {
                                    SExpression::List(inner) if !inner.is_empty() => {
                                        matches!(&inner[0], SExpression::BuiltIn(Instruction::Lambda))
                                    }
                                    _ => false
                                };
                                if is_inline_lambda {
                                    if let SExpression::List(inner) = &pair[1] {
                                        let forced: Vec<String> = letrec_vars.iter().cloned().collect();
                                        let _ = self.compile_lambda_into(&inner[1..], var_regs[i], &forced)?;
                                    }
                                    continue;
                                }
                                let init_reg = self.compile_expr(&pair[1], &[], false)?;
                                self.bytecode.store_opcode(Instr::CopyReg, var_regs[i], init_reg, 0);
                                if let Some(caps) = self.captured_map.get(&init_reg).cloned() {
                                    self.captured_map.insert(var_regs[i], caps);
                                }
                            }
                        }
                        //compile body
                        let mut last_reg = 0;
                        for (index, expr) in body.iter().enumerate() {
                            last_reg = self.compile_expr(expr, &[], is_tail && index == body.len() - 1)?;
                        }
                        self.end_scope();
                        Ok(last_reg)
                    }
                    else {
                        Err(CompilationError::from("First argument must be a list of bindings"))
                    }
                }
            },
            Instruction::Not => {
                if args.len() != 1 {
                    Err(CompilationError::from("Expected 1 argument"))
                }
                else {
                    //try to optimize check into one comparison
                    let inverted = match &args[0] {
                        SExpression::List(list) if !list.is_empty() => {
                            match &list[0] {
                                SExpression::BuiltIn(b) => {
                                    match b {
                                        Instruction::Eq => Some(Instr::Neq),
                                        Instruction::Lt => Some(Instr::Geq),
                                        Instruction::Gt => Some(Instr::Leq),
                                        Instruction::Leq => Some(Instr::Gt),
                                        Instruction::Geq => Some(Instr::Lt),
                                        _ => None
                                    }
                                },
                                _ => None
                            }
                        },
                        _ => None
                    };

                    if let Some(instr) = inverted {
                        let SExpression::List(list) = &args[0] else {
                            return Err(CompilationError::from("Expected a list")); //cannot happen, checked above
                        };
                        self.compile_comparison_op(&list[1..], instr)
                    }
                    else {
                        let reg = self.compile_expr(&args[0], &[], false)?;
                        self.bytecode.store_opcode(Instr::Not, reg, reg, 0);
                        Ok(reg)
                    }
                }
            },
            Instruction::And => {
                let mut result_reg = 0;
                //empty and evaluates to true
                if args.is_empty() {
                    //write true into target register
                    let result_reg = self.allocate_reg()?;
                    self.bytecode.load_atom(&Atom::Boolean(true), result_reg);
                }
                //positions of jump marks
                let mut jump_marks : Vec<u64> = vec![];
                for (i, expr) in args.iter().enumerate() {
                    result_reg = self.compile_expr(expr, &[], false)?;
                    if i == args.len() - 1 {
                        //after the last check, write false into target register. If the check succeeded, skip it
                        self.bytecode.store_opcode(Instr::Jump, result_reg, JumpCondition::JumpTrue as u8, 0);
                        self.bytecode.store_value(&(4 as i64).to_le_bytes()); //skip one opcode

                        //now, we have the jump target for all other jumps
                        let jump_target = self.bytecode.position();
                        self.bytecode.load_atom(&Atom::Boolean(false), result_reg);

                        //replace all jump targets
                        let end = self.bytecode.position();
                        for pos in &jump_marks {
                            let distance : i64 = (jump_target - pos - size_of::<i64>() as u64) as i64;
                            self.bytecode.store_at(*pos,&distance.to_le_bytes());
                        }
                        self.bytecode.set_position(end);
                    }
                    else {
                        //if the condition did not evaluate to true, jump to end and skip all other checks
                        self.bytecode.store_opcode(Instr::Jump, result_reg, JumpCondition::JumpFalse as u8, 0);
                        jump_marks.push(self.bytecode.position());
                        self.bytecode.store_value(&[0; size_of::<i64>()]);
                    }
                    self.reset_reg(result_reg);
                }
                self.reset_reg(result_reg + 1);
                Ok(result_reg)
            },
            Instruction::Or => {
                let mut result_reg = 0;
                //empty or evaluates to false
                if args.is_empty() {
                    //write false into target register
                    let result_reg = self.allocate_reg()?;
                    self.bytecode.load_atom(&Atom::Boolean(false), result_reg);
                }
                //positions of jump marks
                let mut jump_marks : Vec<u64> = vec![];
                for (i, expr) in args.iter().enumerate() {
                    result_reg = self.compile_expr(expr, &[], false)?;
                    if i == args.len() - 1 {
                        //now, we have the jump target for all other jumps
                        let jump_target = self.bytecode.position();

                        //replace all jump targets
                        let end = self.bytecode.position();
                        for pos in &jump_marks {
                            let distance : i64 = (jump_target - pos - size_of::<i64>() as u64) as i64;
                            self.bytecode.store_at(*pos,&distance.to_le_bytes());
                        }
                        self.bytecode.set_position(end);
                    }
                    else {
                        //if the condition did not evaluate to false, jump to end and skip all other checks
                        self.bytecode.store_opcode(Instr::Jump, result_reg, JumpCondition::JumpTrue as u8, 0);
                        jump_marks.push(self.bytecode.position());
                        self.bytecode.store_value(&[0; size_of::<i64>()]);
                    }
                    self.reset_reg(result_reg);
                }
                self.reset_reg(result_reg + 1);
                Ok(result_reg)
            },
            Instruction::Eq => self.compile_comparison_op(args, Instr::Eq),
            Instruction::Lt => self.compile_comparison_op(args, Instr::Lt),
            Instruction::Gt => self.compile_comparison_op(args, Instr::Gt),
            Instruction::Leq => self.compile_comparison_op(args, Instr::Leq),
            Instruction::Geq => self.compile_comparison_op(args, Instr::Geq),
            Instruction::Plus => self.compile_binary_op(args, Instr::Add),
            Instruction::Minus => self.compile_binary_op(args, Instr::Sub),
            Instruction::Multiply => self.compile_binary_op(args, Instr::Mul),
            Instruction::Divide => self.compile_binary_op(args, Instr::Div),
        }
    }

    fn compile_binary_op(&mut self, args: &[SExpression], instr: Instr) -> Result<u8, CompilationError> {
        if args.len() >= 2 {
            let result_reg = self.allocate_reg()?;
            let mut r1 = self.compile_expr(&args[0], &[], false)?;
            for i in 1..args.len() {
                let rnext = self.compile_expr(&args[i], &[], false)?;
                self.bytecode.store_opcode(instr, result_reg, r1, rnext);
                self.reset_reg(result_reg + 1);
                r1 = result_reg;
            }
            self.reset_reg(result_reg + 1);
            Ok(result_reg)
        }
        else {
            todo!()
        }
    }

    fn compile_comparison_op(&mut self, args: &[SExpression], instr: Instr) -> Result<u8, CompilationError> {
        let result_reg = self.allocate_reg()?;
        self.bytecode.load_atom(&Atom::Boolean(true), result_reg);
        if args.is_empty() {    
            Ok(result_reg)
        }
        else {
            let r1 = self.compile_expr(&args[0], &[], false)?;
            if args.len() >= 2 {
                for i in 1..args.len() {
                    let rnext = self.compile_expr(&args[i], &[], false)?;
                    self.bytecode.store_opcode(instr, result_reg, r1, rnext);
                    if i < args.len() - 1 {
                        self.bytecode.store_opcode(Instr::CopyReg, r1, rnext, 0)
                    }
                    self.reset_reg(r1 + 1)
                }
            }
            else {
                //compare it to itself to check the type and produce the result true
                self.bytecode.store_opcode(Instr::Eq, result_reg, r1, r1);
            }
            self.reset_reg(result_reg + 1);
            Ok(result_reg)
        }
    }
}