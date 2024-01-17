use case_insensitive_hashmap::CaseInsensitiveHashMap;

use crate::instructions::Instruction;
use crate::parser::{SExpression, Atom};
use std::io::Write;
use std::mem::size_of;
use std::{fmt, io::Cursor};
use std::error::Error;

use super::vp::{VirtualProgram, Instr, OpCode, JumpCondition, FunctionHeader};

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

    fn store_string(&mut self, val: &str) {
        let _ = self.cursor.write(&val.len().to_le_bytes());
        let _ = self.cursor.write(val.as_bytes());

        //println!("[string: {}]", val);
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
    symbols: CaseInsensitiveHashMap<u8>
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
    bytecode: BytecodeBuilder,
    last_used_reg: u8,
    fixed_registers: u8,
    max_used_registers: u8,
    symbols: CaseInsensitiveHashMap<u8>,
    interner: SymbolInterner, //for global symbols
    scope_stack: Vec<CompilationScope>
}

impl Compiler {
    const MAX_REG: u8 = 255;

    pub fn new(generate_asm: bool) -> Compiler {
        Compiler{generate_asm, bytecode: BytecodeBuilder::new(generate_asm), last_used_reg: 0, fixed_registers: 0, max_used_registers: 0, symbols: CaseInsensitiveHashMap::new(), interner: SymbolInterner::new(), scope_stack: Vec::new()}
    }

    fn begin_scope(&mut self) {
        let mut new_symbols = CaseInsensitiveHashMap::new();
        std::mem::swap(&mut self.symbols, &mut new_symbols);
        let current_scope = CompilationScope{last_used_reg: self.last_used_reg, fixed_registers: self.fixed_registers, max_used_registers: self.max_used_registers, symbols: new_symbols};
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
        let prog = VirtualProgram::new(new_builder.listing, new_builder.cursor.into_inner(), reg);
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

                    //evaluate all other expressions as arguments
                    let start_reg = self.last_used_reg;
                    for expr in list.iter().skip(1) {
                        let reg = self.compile_expr(expr, &[], false)?;
                        //hack: copy parameters into new registers
                        if reg <= self.fixed_registers {
                            let target_reg = self.allocate_reg()?;
                            self.bytecode.store_opcode(Instr::CopyReg, target_reg, reg, 0);
                        }
                    }

                    if is_tail {
                        self.bytecode.store_opcode(Instr::TailCallSymbol, sym_reg, start_reg, result_reg);
                    }
                    else {
                        self.bytecode.store_opcode(Instr::CallSymbol, sym_reg, start_reg, result_reg);
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
                    //jump past the lambda body
                    self.bytecode.store_opcode(Instr::Jump, 0, JumpCondition::Jump as u8, 0);
                    let jump_addr = self.bytecode.position();
                    self.bytecode.store_value(&[0; std::mem::size_of::<i64>()]);

                    self.begin_scope();
                    let header_addr = self.bytecode.position();
                    self.bytecode.store_value(&[0; std::mem::size_of::<FunctionHeader>()]);
                    let symbols_before = self.symbols.len();
                    //register parameters
                    if let SExpression::List(arg_list) = &args[0] {
                        for param in arg_list {
                            if let SExpression::Symbol(sym) = param {
                                self.find_or_alloc(sym.as_str())?;
                            }
                        }
                    }
                    let used_registers = (self.symbols.len() + 1 - symbols_before) as u8;
                    self.fixed_registers = used_registers;
                    self.last_used_reg = self.fixed_registers;

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
                    let reg = self.allocate_reg()?;
                    self.bytecode.store_opcode(Instr::LoadFuncRef, reg, 0, 0);
                    self.bytecode.store_value(&header_addr.to_le_bytes());

                    Ok(reg)
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
            Instruction::Plus => self.compile_binary_op(args, Instr::Add),
            Instruction::Minus => self.compile_binary_op(args, Instr::Sub),
            Instruction::Multiply => self.compile_binary_op(args, Instr::Mul),
            Instruction::Divide => self.compile_binary_op(args, Instr::Div),
            Instruction::Eq => self.compile_comparison_op(args, Instr::Eq),
            Instruction::Lt => self.compile_comparison_op(args, Instr::Lt),
            Instruction::Gt => self.compile_comparison_op(args, Instr::Gt),
            Instruction::Leq => self.compile_comparison_op(args, Instr::Leq),
            Instruction::Geq => self.compile_comparison_op(args, Instr::Geq),
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