use std::cell::Cell;
use std::collections::{HashSet, HashMap};
use rustc_hash::FxHashMap;

use crate::parser::{SExpression, Atom};
use crate::vm::gc::{Arena, Handle, Trace, GcVisitor};

use super::vp::{ClosureData, FunctionData, FunctionHeader, Instr, JumpCondition, Value, ValueKind, HeapValue, VirtualProgram, VmContext, Pair};
use super::jit::Jit;

macro_rules! binary_op {
    ($self:ident, $opcode:ident, $op:tt) => {
        {
            let v1 = $self.resolve_value(&$self.registers[$opcode[2] as usize + $self.window_start]);
            let v2 = $self.resolve_value(&$self.registers[$opcode[3] as usize + $self.window_start]);
            
            let res_reg = $opcode[1] as usize + $self.window_start;
            match (v1.kind(), v2.kind()) {
                (ValueKind::Integer(lhs), ValueKind::Integer(rhs)) => $self.registers[res_reg] = Value::integer(lhs $op rhs),
                (ValueKind::Integer(lhs), ValueKind::Float(rhs)) => $self.registers[res_reg] = Value::float(lhs as f32 $op rhs),
                (ValueKind::Float(lhs), ValueKind::Float(rhs)) => $self.registers[res_reg] = Value::float(lhs $op rhs),
                (ValueKind::Float(lhs), ValueKind::Integer(rhs)) => $self.registers[res_reg] = Value::float(lhs $op rhs as f32),
                (v1, v2) => {
                    eprintln!("Binary op failed: {:?} {:?}", v1, v2);
                    break;
                }
            }
        }
    };
}

macro_rules! comparison_op {
    ($self:ident, $opcode:ident, $prog:ident, $debugger:ident, $op:tt) => {
        {
            let v1 = $self.resolve_value(&$self.registers[$opcode[2] as usize + $self.window_start]);
            let v2 = $self.resolve_value(&$self.registers[$opcode[3] as usize + $self.window_start]);

            let res_reg = $opcode[1] as usize + $self.window_start;
            let matches = match (v1.kind(), v2.kind()) {
                (ValueKind::Integer(lhs), ValueKind::Integer(rhs)) => lhs $op rhs,
                (ValueKind::Integer(lhs), ValueKind::Float(rhs)) => (lhs as f32) $op rhs,
                (ValueKind::Float(lhs), ValueKind::Float(rhs)) => lhs $op rhs,
                (ValueKind::Float(lhs), ValueKind::Integer(rhs)) => lhs $op rhs as f32,
                _ => break,
            };
            
            $self.registers[res_reg] = Value::boolean(matches);

            if $debugger.is_none() {
                //try if the next instruction is a jump
                if let Some(opcode) = $prog.read_opcode() {
                    if let Ok(Instr::Jump) = opcode[0].try_into() {
                        if let Some(distance) = $prog.read_int() {
                            if opcode[2] == JumpCondition::Jump as u8 {
                                $prog.jump(distance);
                                continue;
                            }
                            //everything that is not false, is true
                            let check = $self.registers[opcode[1] as usize + $self.window_start].is_true();
                            if (check && opcode[2] == JumpCondition::JumpTrue as u8) || (!check && opcode[2] == JumpCondition::JumpFalse as u8) {
                                $prog.jump(distance);
                            }
                            continue;
                        } else {
                            break;
                        }
                    }
                    else {
                        $prog.jump(-4);
                    }
                } else {
                    break;
                }
            }
        }
    };
}

const fn empty_value() -> Value {
    Value::nil()
}

#[derive(Debug, Clone)]
pub struct CallState {
    pub window_start: usize,
    pub result_reg: u8,
    pub target_reg: u8,
    pub return_addr: u64
}

#[derive(Clone)]
pub struct MapCache {
    pub handle: Handle,
    pub header: FunctionHeader,
    pub address: u64,
    pub captures: Option<Vec<Value>>,
    pub jit_code: u64,
    pub fast_jit_code: u64,
}

pub trait Debugger {
    fn on_step(&mut self, vm: &Vm, prog: &VirtualProgram);
}

#[repr(C)]
pub struct Vm {
    pub heap: Arena<HeapValue>,
    pub registers: Vec<Value>,
    pub global_vars: Vec<Value>,
    pub symbol_table: FxHashMap<String, Handle>,
    pub(super) call_states: Vec<CallState>,
    pub window_start: usize,
    pub jit: Jit,
    pub jit_enabled: bool,
    pub scratch_buffer: Vec<Value>,
    pub roots_buffer: Vec<Handle>,
    pub tail_call_pending: bool,
    pub next_jit_code: u64,
    pub map_cache: Option<MapCache>,
    pub symbol_opt_cache: FxHashMap<u64, Handle>,
    pub jit_constants: Vec<Handle>,
}

impl VmContext for Vm {
    fn heap(&mut self) -> &mut Arena<HeapValue> {
        &mut self.heap
    }

    fn collect(&mut self) {
        self.collect_garbage();
    }

    fn push_scratch(&mut self, val: Value) {
        self.scratch_buffer.push(val);
    }

    fn pop_scratch(&mut self) {
        self.scratch_buffer.pop();
    }
}

impl Vm {
    pub fn new(jit_enabled: bool) -> Vm {
        const EMPTY : Value = empty_value();
        Vm {heap: Arena::new(), registers: vec![EMPTY; 64000], global_vars: Vec::new(), symbol_table: FxHashMap::default(), call_states: Vec::new(), window_start: 0, jit: Jit::new(), jit_enabled, scratch_buffer: Vec::with_capacity(32), roots_buffer: Vec::with_capacity(1024), tail_call_pending: false, next_jit_code: 0, map_cache: None, symbol_opt_cache: FxHashMap::default(), jit_constants: Vec::with_capacity(1024)}
    }

    pub fn collect_garbage(&mut self) {
        if self.heap.allocated_objects < self.heap.next_gc_threshold {
            return;
        }
        
        // Use Copying GC
        let registers = &mut self.registers;
        let global_vars = &mut self.global_vars;
        let symbol_table = &mut self.symbol_table;
        let scratch_buffer = &mut self.scratch_buffer;
        let map_cache = &mut self.map_cache;
        let symbol_opt_cache = &mut self.symbol_opt_cache;
        
        self.heap.collect_from_roots(|visitor| {
            // Visit registers
            for v in registers {
                v.trace(visitor);
            }
            
            // Visit globals
            for v in global_vars {
                v.trace(visitor);
            }
            
            // Visit symbol table (the values are Handles)
            for h in symbol_table.values_mut() {
                visitor.visit(h);
            }
            
            // Visit scratch buffer
            for v in scratch_buffer {
                v.trace(visitor);
            }
            
            // Visit MapCache
            if let Some(cache) = map_cache {
                visitor.visit(&mut cache.handle);
                if let Some(caps) = &mut cache.captures {
                    for v in caps {
                        v.trace(visitor);
                    }
                }
            }
            
            // Visit Symbol Opt Cache
            for h in symbol_opt_cache.values_mut() {
                visitor.visit(h);
            }
            
            // Visit JIT constants
            for h in self.jit_constants.iter_mut() {
                visitor.visit(h);
            }
        });
    }

    pub fn run_jit_function(&mut self, prog: *mut VirtualProgram, start_addr: u64, end_addr: u64) -> bool {
        match self.jit.compile(&self.global_vars, &mut self.heap, &mut self.jit_constants, &mut self.symbol_table, unsafe { &mut *prog }, start_addr, end_addr) {
            Ok(func) => {
                unsafe {
                    let mut current_func = func;
                    loop {
                        current_func(self as *mut Vm, prog, self.registers.as_mut_ptr().add(self.window_start));
                        if !self.tail_call_pending {
                            break;
                        }
                        self.tail_call_pending = false;
                        if self.next_jit_code != 0 {
                            current_func = std::mem::transmute(self.next_jit_code as *const u8);
                        } else {
                            // Should not happen if tail_call_pending is true
                            break;
                        }
                    }
                }
                true
            },
            Err(e) => {
                println!("JIT compilation failed: {}", e);
                false
            }
        }
    }

    pub fn registers(&self) -> &Vec<Value> {
        &self.registers
    }


    pub fn call_stack(&self) -> &[CallState] {
        &self.call_states
    }

    fn resolve_value(&self, val: &Value) -> Value {
        if let ValueKind::Object(handle) = val.kind() {
            if let Some(HeapValue::Ref(r)) = self.heap.get(handle) {
                return *r;
            }
        }
        *val
    }

    pub(super) fn scan_function_end(&self, prog: &mut VirtualProgram, start_addr: u64) -> u64 {
        let old_pos = prog.current_address();
        
        let mut visited = HashSet::new();
        let mut queue = vec![start_addr];
        let mut max_addr = start_addr;
        
        while let Some(addr) = queue.pop() {
            if visited.contains(&addr) { continue; }
            visited.insert(addr);
            
            prog.jump_to(addr);
            
            loop {
                let Some(opcode) = prog.read_opcode() else { break; };
                let instr: Result<Instr, _> = opcode[0].try_into();
                
                match instr {
                    Ok(Instr::Jump) => {
                        let cond = opcode[2];
                        let dist = prog.read_int().unwrap_or(0);
                        let after_read = prog.current_address();
                        let target = (after_read as i64 + dist) as u64;
                        
                        if !visited.contains(&target) {
                            queue.push(target);
                        }
                        
                        if cond != JumpCondition::Jump as u8 {
                            // Fallthrough
                        } else {
                            if after_read > max_addr { max_addr = after_read; }
                            break; // Unconditional jump ends block
                        }
                    },
                    Ok(Instr::Ret) | Ok(Instr::TailCallSymbol) => {
                        if prog.current_address() > max_addr { max_addr = prog.current_address(); }
                        break;
                    },
                    Ok(Instr::LoadInt) | Ok(Instr::LoadFloat) | Ok(Instr::Define) | Ok(Instr::LoadGlobal) | Ok(Instr::LoadFuncRef) | Ok(Instr::CallFunction) => { let _ = prog.read_int(); },
                    Ok(Instr::LoadString) => { let _ = prog.read_string(); },
                    Ok(Instr::Map) => { 
                        let _ = prog.read_byte();
                        let target = prog.current_address() + 16;
                        if !visited.contains(&target) { queue.push(target); }
                    },
                    Ok(Instr::ForEach) => { 
                        let _ = prog.read_byte();
                        let target = prog.current_address() + 12;
                        if !visited.contains(&target) { queue.push(target); }
                    },
                    Ok(Instr::Fold) => { 
                        let _ = prog.read_byte();
                        let target = prog.current_address() + 12;
                        if !visited.contains(&target) { queue.push(target); }
                    },
                    Ok(Instr::Filter) => { 
                        let _ = prog.read_byte(); 
                        let _ = prog.read_byte();
                        let target = prog.current_address() + 17;
                        if !visited.contains(&target) { queue.push(target); }
                    },
                    Ok(Instr::FilterStep) => { let _ = prog.read_byte(); },
                    Ok(Instr::MakeClosure) => {
                        let count = opcode[3];
                        for _ in 0..count {
                            let _ = prog.read_byte();
                        }
                    },
                    _ => {}
                }
                
                if prog.current_address() > max_addr { max_addr = prog.current_address(); }
            }
        }
        
        prog.jump_to(old_pos);
        max_addr
    }

    fn reverse_list(&mut self, mut list: Value) -> Value {
        let mut result = Value::nil();
        while let ValueKind::Object(handle) = list.kind() {
            if let Some(HeapValue::Pair(p)) = self.heap.get(handle) {
                let car = p.car;
                let cdr = p.cdr;
                let new_pair = HeapValue::Pair(Pair { car, cdr: result });
                let new_handle = self.heap.alloc(new_pair);
                result = Value::object(new_handle);
                list = cdr;
            } else {
                break;
            }
        }
        result
    }

    pub fn run(&mut self, prog: &mut VirtualProgram) -> Option<Value> {
        self.run_debug(prog, None)
    }

    pub fn run_debug(&mut self, prog: &mut VirtualProgram, mut debugger: Option<&mut dyn Debugger>) -> Option<Value> {
        loop {
            if let Some(dbg) = &mut debugger {
                dbg.on_step(self, prog);
            }

            let Some(opcode) = prog.read_opcode() else {
                break;
            };

            match opcode[0].try_into() {
                Ok(Instr::LoadInt) => {
                    let Some(val) = prog.read_int() else {
                        return None;
                    };
                    self.registers[opcode[1] as usize + self.window_start] = Value::integer(val);
                },
                Ok(Instr::LoadFloat) => {
                    let Some(val) = prog.read_float() else {
                        return None;
                    };
                    self.registers[opcode[1] as usize + self.window_start] = Value::float(val as f32);
                },
                Ok(Instr::LoadBool) => {
                    self.registers[opcode[1] as usize + self.window_start] = Value::boolean(opcode[2] != 0);
                },
                Ok(Instr::LoadString) => {
                    let Some(val) = prog.read_string() else {
                        return None;
                    };
                    self.collect_garbage();
                    self.registers[opcode[1] as usize + self.window_start] = Value::object(self.heap.alloc(HeapValue::String(val)));
                },
                Ok(Instr::LoadSymbol) => {
                    let Some(val) = prog.read_string() else {
                        return None;
                    };
                    self.collect_garbage();
                    let handle = if let Some(&h) = self.symbol_table.get(&val) {
                        h
                    } else {
                        let h = self.heap.alloc(HeapValue::Symbol(val.clone()));
                        self.symbol_table.insert(val, h);
                        h
                    };
                    self.registers[opcode[1] as usize + self.window_start] = Value::object(handle);
                },
                Ok(Instr::LoadNil) => {
                    let idx = opcode[1] as usize + self.window_start;
                    if idx >= self.registers.len() {
                        println!("LoadNil panic: idx={}, ws={}, reg={}, len={}", idx, self.window_start, opcode[1], self.registers.len());
                    }
                    self.registers[idx] = Value::nil();
                },
                Ok(Instr::CopyReg) => {
                    self.registers[opcode[1] as usize + self.window_start] = self.registers[opcode[2] as usize + self.window_start];
                },
                Ok(Instr::SwapReg) => {
                    let src_reg = self.window_start + opcode[1] as usize;
                    let target_reg = self.window_start + opcode[2] as usize;
                    self.registers.swap(src_reg, target_reg);
                },
                Ok(Instr::Add) => {
                    binary_op!(self, opcode, +)
                },
                Ok(Instr::Sub) => binary_op!(self, opcode, -),
                Ok(Instr::Mul) => binary_op!(self, opcode, *),
                Ok(Instr::Div) => binary_op!(self, opcode, /),
                Ok(Instr::Eq) => {
                    let v1 = self.resolve_value(&self.registers[opcode[2] as usize + self.window_start]);
                    let v2 = self.resolve_value(&self.registers[opcode[3] as usize + self.window_start]);
                    let res_reg = opcode[1] as usize + self.window_start;
                    
                    let matches = v1 == v2;
                    self.registers[res_reg] = Value::boolean(matches);

                    if debugger.is_none() {
                        if let Some(opcode) = prog.read_opcode() {
                            if let Ok(Instr::Jump) = opcode[0].try_into() {
                                if let Some(distance) = prog.read_int() {
                                    if opcode[2] == JumpCondition::Jump as u8 {
                                        prog.jump(distance);
                                        continue;
                                    }
                                    let check = self.registers[opcode[1] as usize + self.window_start].is_true();
                                    if (check && opcode[2] == JumpCondition::JumpTrue as u8) || (!check && opcode[2] == JumpCondition::JumpFalse as u8) {
                                        prog.jump(distance);
                                    }
                                    continue;
                                } else {
                                    break;
                                }
                            } else {
                                prog.jump(-4);
                            }
                        } else {
                            break;
                        }
                    }
                },
                Ok(Instr::Neq) => comparison_op!(self, opcode, prog, debugger, !=),
                Ok(Instr::Lt) => comparison_op!(self, opcode, prog, debugger, <),
                Ok(Instr::Gt) => comparison_op!(self, opcode, prog, debugger, >),
                Ok(Instr::Leq) => comparison_op!(self, opcode, prog, debugger, <=),
                Ok(Instr::Geq) => comparison_op!(self, opcode, prog, debugger, >=),
                Ok(Instr::Not) => {
                    let value = &self.registers[opcode[2] as usize + self.window_start];
                    match value.kind() {
                        ValueKind::Boolean(b) => self.registers[opcode[1] as usize + self.window_start] = Value::boolean(!b),
                        _ => self.registers[opcode[1] as usize] = Value::boolean(false)
                    };

                    //try if the next instruction is a jump
                    let Some(opcode) = prog.read_opcode() else {
                        break;
                    };
                    if let Ok(Instr::Jump) = opcode[0].try_into() {
                        let Some(distance) = prog.read_int() else {
                            break;
                        };
                        if opcode[2] == JumpCondition::Jump as u8 {
                            prog.jump(distance);
                            continue;
                        }
                        //everything that is not false, is true
                        let check = self.registers[opcode[1] as usize + self.window_start].is_true();
                        if (check && opcode[2] == JumpCondition::JumpTrue as u8) || (!check && opcode[2] == JumpCondition::JumpFalse as u8) {
                            prog.jump(distance);
                        }
                    }
                    else {
                        prog.jump(-4);
                    }
                }
                Ok(Instr::Jump) => {
                    let Some(distance) = prog.read_int() else {
                        break;
                    };
                    if opcode[2] == JumpCondition::Jump as u8 {
                        prog.jump(distance);
                        continue;
                    }
                    //everything that is not false, is true
                    let check = self.registers[opcode[1] as usize + self.window_start].is_true();
                    if (check && opcode[2] == JumpCondition::JumpTrue as u8) || (!check && opcode[2] == JumpCondition::JumpFalse as u8) {
                        prog.jump(distance);
                    }
                },
                Ok(Instr::Define) => {
                    let Some(sym_id) = prog.read_int() else {
                        break;
                    };
                    if sym_id as usize >= self.global_vars.len() {
                        self.global_vars.resize(sym_id as usize + 1, Value::nil());
                    }
                    self.global_vars[sym_id as usize] = self.registers[opcode[1] as usize + self.window_start].clone();
                },
                Ok(Instr::LoadGlobal) => {
                    let Some(sym_id) = prog.read_int() else {
                        break;
                    };
                    let value = if (sym_id as usize) < self.global_vars.len() {
                        Some(&self.global_vars[sym_id as usize])
                    } else {
                        None
                    };
                    match value {
                        Some(v) => self.registers[opcode[1] as usize + self.window_start] = v.clone(),
                        _ => self.registers[opcode[1] as usize + self.window_start] = empty_value()
                    }
                },
                Ok(Instr::LoadFuncRef) => {
                    let Some(header_addr) = prog.read_int() else {
                        break;
                    };
                    let Some(header) = prog.read_function_header(header_addr as u64) else {
                        break;
                    };
                    let func_addr = header_addr as usize + std::mem::size_of::<FunctionHeader>();
                    self.collect_garbage();
                    self.registers[opcode[1] as usize + self.window_start] = Value::object(self.heap.alloc(HeapValue::FuncRef(FunctionData{header, address: func_addr as u64, jit_code: Cell::new(0), fast_jit_code: Cell::new(0)})));
                },
                Ok(Instr::CallSymbol) => {
                    let func_reg = opcode[1] as usize + self.window_start;
                    let resolved_func = self.resolve_value(&self.registers[func_reg]);

                    let (header, address, captures) = if let ValueKind::Object(handle) = resolved_func.kind() {
                        match self.heap.get(handle) {
                            Some(HeapValue::FuncRef(f)) => (f.header, f.address, None),
                            Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone())),
                            _ => return None
                        }
                    } else {
                        return None;
                    };

                    let param_start = opcode[2];
                    let size = param_start as usize + header.register_count as usize + self.window_start;
                    if size >= self.registers.len() {
                        self.registers.resize(size, empty_value());
                    }
                    let old_ws = self.window_start;
                    let ret_addr = prog.current_address();
                    let state = CallState{window_start: old_ws, result_reg: header.result_reg, target_reg: opcode[3], return_addr: ret_addr};
                    self.call_states.push(state);
                    self.window_start += param_start as usize;
                    
                    // Copy captures into registers
                    if let Some(caps) = captures {
                        let start_reg = header.param_count as usize;
                        for (i, val) in caps.into_iter().enumerate() {
                            self.registers[self.window_start + start_reg + i] = val;
                        }
                    }
                    
                    if self.jit_enabled {
                        let end_addr = if self.jit.is_compiled(address) {
                            0
                        } else {
                            self.scan_function_end(prog, address)
                        };
                        if self.run_jit_function(prog as *mut VirtualProgram, address, end_addr) {
                            let state = self.call_states.pop().unwrap();
                            let source_reg = self.window_start + state.result_reg as usize;
                            let target_reg = state.window_start + state.target_reg as usize;
                            self.registers.swap(source_reg, target_reg);

                            self.window_start = old_ws;
                        } else {
                            prog.jump_to(address);
                        }
                    } else {
                        prog.jump_to(address);
                    }
                },
                Ok(Instr::TailCallSymbol) => {
                    // For tail-calls, clone the function value instead of swapping it out.
                    let resolved_func = self.resolve_value(&self.registers[opcode[1] as usize + self.window_start]);

                    let (header, address, captures) = if let ValueKind::Object(handle) = resolved_func.kind() {
                        match self.heap.get(handle) {
                            Some(HeapValue::FuncRef(f)) => (f.header, f.address, None),
                            Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone())),
                            _ => return None
                        }
                    } else {
                        return None;
                    };

                    let size = self.window_start + header.register_count as usize;
                    if size >= self.registers.len() {
                        self.registers.resize(size, empty_value());
                    }

                    let param_start = opcode[2];
                    // Copy parameters into the target area for tail-call instead of swapping.
                    let mut params: Vec<Value> = Vec::new();
                    for i in 0..(header.param_count as usize) {
                        let idx = self.window_start + param_start as usize + i;
                        params.push(self.registers[idx].clone());
                    }
                    for (i, param) in params.into_iter().enumerate() {
                        let target_reg = self.window_start + i;
                        self.registers[target_reg] = param;
                    }

                    if let Some(last_frame) = self.call_states.last_mut() {
                        last_frame.result_reg = header.result_reg;
                    }
                    
                    // Copy captures into registers (after parameters)
                    if let Some(caps) = captures {
                        let start_reg = header.param_count as usize;
                        for (i, val) in caps.into_iter().enumerate() {
                            let target = self.window_start + start_reg + i;
                            self.registers[target] = val;
                        }
                    }

                    if self.jit_enabled {
                        let end_addr = if self.jit.is_compiled(address) {
                            0
                        } else {
                            self.scan_function_end(prog, address)
                        };
                        self.run_jit_function(prog as *mut VirtualProgram, address, end_addr);
                        
                        // Simulate Ret
                        if let Some(state) = self.call_states.pop() {
                            let source_reg = self.window_start + state.result_reg as usize;
                            let target_reg = state.window_start + state.target_reg as usize;
                            self.registers.swap(source_reg, target_reg);

                            self.window_start = state.window_start;
                            prog.jump_to(state.return_addr);
                        } else {
                            return None; // End of program
                        }
                    } else {
                        prog.jump_to(address);
                    }
                },
                Ok(Instr::CallFunction) => {
                    let Some(func_id) = prog.read_int() else {
                        println!("CallFunction failed to read func_id");
                        break;
                    };
                    let Some(function) = prog.get_function(func_id) else {
                        println!("CallFunction failed to get function {}", func_id);
                        break;
                    };
                    let start_reg = opcode[2] as usize;
                    let reg_count = opcode[3] as usize;
                    let args = self.registers[self.window_start + start_reg.. self.window_start + start_reg + reg_count].to_vec();
                    match function(self, &args) {
                        Ok(v) => self.registers[opcode[1] as usize + self.window_start] = v,
                        Err(e) => panic!("Runtime error: {}", e),
                    }
                },
                Ok(Instr::Car) => {
                    let arg = self.registers[opcode[2] as usize + self.window_start];
                    if let ValueKind::Object(handle) = arg.kind() {
                        if let Some(HeapValue::Pair(p)) = self.heap.get(handle) {
                            self.registers[opcode[1] as usize + self.window_start] = p.car;
                        } else {
                            panic!("Runtime error: car expects a pair");
                        }
                    } else {
                        panic!("Runtime error: car expects a pair");
                    }
                },
                Ok(Instr::Cdr) => {
                    let arg = self.registers[opcode[2] as usize + self.window_start];
                    if let ValueKind::Object(handle) = arg.kind() {
                        if let Some(HeapValue::Pair(p)) = self.heap.get(handle) {
                            self.registers[opcode[1] as usize + self.window_start] = p.cdr;
                        } else {
                            panic!("Runtime error: cdr expects a pair");
                        }
                    } else {
                        panic!("Runtime error: cdr expects a pair");
                    }
                },
                Ok(Instr::Cons) => {
                    let car = self.registers[opcode[2] as usize + self.window_start];
                    let cdr = self.registers[opcode[3] as usize + self.window_start];
                    self.scratch_buffer.push(car);
                    self.scratch_buffer.push(cdr);
                    self.collect_garbage();
                    self.scratch_buffer.pop();
                    self.scratch_buffer.pop();
                    self.registers[opcode[1] as usize + self.window_start] = Value::object(self.heap.alloc(HeapValue::Pair(Pair { car, cdr })));
                },
                Ok(Instr::IsPair) => {
                    let arg = self.registers[opcode[2] as usize + self.window_start];
                    let is_pair = if let ValueKind::Object(handle) = arg.kind() {
                        matches!(self.heap.get(handle), Some(HeapValue::Pair(_)))
                    } else {
                        false
                    };
                    self.registers[opcode[1] as usize + self.window_start] = Value::boolean(is_pair);
                },
                Ok(Instr::IsEq) => {
                    let arg1 = self.registers[opcode[2] as usize + self.window_start];
                    let arg2 = self.registers[opcode[3] as usize + self.window_start];
                    self.registers[opcode[1] as usize + self.window_start] = Value::boolean(arg1 == arg2);
                },
                Ok(Instr::IsNull) => {
                    let arg = self.registers[opcode[2] as usize + self.window_start];
                    self.registers[opcode[1] as usize + self.window_start] = Value::boolean(arg.is_nil());
                },
                Ok(Instr::Map) => {
                    let func_reg = opcode[1] as usize + self.window_start;
                    let list_reg = opcode[2] as usize + self.window_start;
                    let res_reg = opcode[3] as usize + self.window_start;
                    let temp_reg = prog.read_byte().unwrap() as usize + self.window_start;

                    let list_val = self.registers[list_reg];
                    if list_val.is_nil() {
                        prog.jump(16); // Skip Cons (4) + Jump (12)
                        let res = self.registers[res_reg];
                        self.registers[res_reg] = self.reverse_list(res);
                    } else {
                        // Initialize result register if it's the first iteration (check if it's nil or garbage?)
                        // Actually, we can't easily check if it's the first iteration here.
                        // But wait, Map builds the list in reverse.
                        // The initial value of res_reg should be nil.
                        // But res_reg is updated in the loop (Cons).
                        // If we set it to nil every time, we lose the list!
                        // So initialization must happen BEFORE the loop.
                        // But Map opcode IS the loop header (conceptually).
                        // The compiler emits: Map ... -> Cons ... -> Jump back to Map.
                        // So Map is executed every iteration.
                        // We cannot initialize res_reg inside Map opcode!
                        
                        // So I MUST emit initialization in the compiler!
                        // I missed that.
                        
                        if let ValueKind::Object(handle) = list_val.kind() {
                            if let Some(HeapValue::Pair(p)) = self.heap.get(handle) {
                                let car = p.car;
                                let cdr = p.cdr;
                                self.registers[list_reg] = cdr;

                                let resolved_func = self.resolve_value(&self.registers[func_reg]);
                                let (header, address, captures) = if let ValueKind::Object(handle) = resolved_func.kind() {
                                    match self.heap.get(handle) {
                                        Some(HeapValue::FuncRef(f)) => (f.header, f.address, None),
                                        Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone())),
                                        _ => panic!("Map expects a function")
                                    }
                                } else {
                                    panic!("Map expects a function");
                                };

                                let param_start = temp_reg - self.window_start;
                                let size = temp_reg + header.register_count as usize;
                                println!("Map: ws={}, temp={}, size={}, len={}, reg_count={}", self.window_start, temp_reg, size, self.registers.len(), header.register_count);
                                if size >= self.registers.len() {
                                    self.registers.resize(size, empty_value());
                                }
                                let old_ws = self.window_start;
                                let ret_addr = prog.current_address();
                                let state = CallState{window_start: old_ws, result_reg: header.result_reg, target_reg: param_start as u8, return_addr: ret_addr};
                                self.call_states.push(state);
                                self.window_start += param_start;
                                
                                if let Some(caps) = captures {
                                    let start_reg = header.param_count as usize;
                                    for (i, val) in caps.into_iter().enumerate() {
                                        self.registers[self.window_start + start_reg + i] = val;
                                    }
                                }

                                self.registers[self.window_start] = car;

                                if self.jit_enabled {
                                    let end_addr = self.scan_function_end(prog, address);
                                    if self.run_jit_function(prog as *mut VirtualProgram, address, end_addr) {
                                        let state = self.call_states.pop().unwrap();
                                        let source_reg = self.window_start + state.result_reg as usize;
                                        let target_reg = state.window_start + state.target_reg as usize;
                                        self.registers.swap(source_reg, target_reg);
                                        self.window_start = old_ws;
                                    } else {
                                        prog.jump_to(address);
                                    }
                                } else {
                                    prog.jump_to(address);
                                }
                            } else {
                                panic!("Map expects a list");
                            }
                        } else {
                            panic!("Map expects a list");
                        }
                    }
                },
                Ok(Instr::ForEach) => {
                    let func_reg = opcode[1] as usize + self.window_start;
                    let list_reg = opcode[2] as usize + self.window_start;
                    let temp_reg = prog.read_byte().unwrap() as usize + self.window_start;

                    let list_val = self.registers[list_reg];
                    if list_val.is_nil() {
                        // Done
                    } else {
                        if let ValueKind::Object(handle) = list_val.kind() {
                            if let Some(HeapValue::Pair(p)) = self.heap.get(handle) {
                                let car = p.car;
                                let cdr = p.cdr;
                                self.registers[list_reg] = cdr;

                                let resolved_func = self.resolve_value(&self.registers[func_reg]);
                                let (header, address, captures) = if let ValueKind::Object(handle) = resolved_func.kind() {
                                    match self.heap.get(handle) {
                                        Some(HeapValue::FuncRef(f)) => (f.header, f.address, None),
                                        Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone())),
                                        _ => panic!("ForEach expects a function")
                                    }
                                } else {
                                    panic!("ForEach expects a function");
                                };

                                let param_start = temp_reg - self.window_start;
                                let size = temp_reg + header.register_count as usize;
                                if size >= self.registers.len() {
                                    self.registers.resize(size, empty_value());
                                }
                                let old_ws = self.window_start;
                                let ret_addr = prog.current_address() - 5; // Return to ForEach (5 bytes back: Opcode(4) + Byte(1))
                                let state = CallState{window_start: old_ws, result_reg: header.result_reg, target_reg: param_start as u8, return_addr: ret_addr};
                                self.call_states.push(state);
                                self.window_start += param_start;
                                
                                if let Some(caps) = captures {
                                    let start_reg = header.param_count as usize;
                                    for (i, val) in caps.into_iter().enumerate() {
                                        self.registers[self.window_start + start_reg + i] = val;
                                    }
                                }

                                self.registers[self.window_start] = car;

                                if self.jit_enabled {
                                    let end_addr = self.scan_function_end(prog, address);
                                    if self.run_jit_function(prog as *mut VirtualProgram, address, end_addr) {
                                        let state = self.call_states.pop().unwrap();
                                        let source_reg = self.window_start + state.result_reg as usize;
                                        let target_reg = state.window_start + state.target_reg as usize;
                                        self.registers.swap(source_reg, target_reg);
                                        self.window_start = old_ws;
                                    } else {
                                        prog.jump_to(address);
                                    }
                                } else {
                                    prog.jump_to(address);
                                }
                            } else {
                                panic!("ForEach expects a list");
                            }
                        } else {
                            panic!("ForEach expects a list");
                        }
                    }
                },
                Ok(Instr::Filter) => {
                    let func_reg = opcode[1] as usize + self.window_start;
                    let list_reg = opcode[2] as usize + self.window_start;
                    let res_reg = opcode[3] as usize + self.window_start;
                    let temp_reg = prog.read_byte().unwrap() as usize + self.window_start;
                    let val_reg = prog.read_byte().unwrap() as usize + self.window_start;

                    let list_val = self.registers[list_reg];
                    if list_val.is_nil() {
                        prog.jump(17); // Skip FilterStep (5) + Jump (12)
                        let res = self.registers[res_reg];
                        self.registers[res_reg] = self.reverse_list(res);
                    } else {
                        if let ValueKind::Object(handle) = list_val.kind() {
                            if let Some(HeapValue::Pair(p)) = self.heap.get(handle) {
                                let car = p.car;
                                // Don't advance list yet, FilterStep does it
                                
                                self.registers[val_reg] = car; // Save car

                                let resolved_func = self.resolve_value(&self.registers[func_reg]);
                                let (header, address, captures) = if let ValueKind::Object(handle) = resolved_func.kind() {
                                    match self.heap.get(handle) {
                                        Some(HeapValue::FuncRef(f)) => (f.header, f.address, None),
                                        Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone())),
                                        _ => panic!("Filter expects a function")
                                    }
                                } else {
                                    panic!("Filter expects a function");
                                };

                                let param_start = temp_reg - self.window_start;
                                let size = temp_reg + header.register_count as usize;
                                if size >= self.registers.len() {
                                    self.registers.resize(size, empty_value());
                                }
                                let old_ws = self.window_start;
                                let ret_addr = prog.current_address(); // Return to FilterStep
                                let state = CallState{window_start: old_ws, result_reg: header.result_reg, target_reg: param_start as u8, return_addr: ret_addr};
                                self.call_states.push(state);
                                self.window_start += param_start;
                                
                                if let Some(caps) = captures {
                                    let start_reg = header.param_count as usize;
                                    for (i, val) in caps.into_iter().enumerate() {
                                        self.registers[self.window_start + start_reg + i] = val;
                                    }
                                }

                                self.registers[self.window_start] = car;

                                if self.jit_enabled {
                                    let end_addr = self.scan_function_end(prog, address);
                                    if self.run_jit_function(prog as *mut VirtualProgram, address, end_addr) {
                                        let state = self.call_states.pop().unwrap();
                                        let source_reg = self.window_start + state.result_reg as usize;
                                        let target_reg = state.window_start + state.target_reg as usize;
                                        self.registers.swap(source_reg, target_reg);
                                        self.window_start = old_ws;
                                    } else {
                                        prog.jump_to(address);
                                    }
                                } else {
                                    prog.jump_to(address);
                                }
                            } else {
                                panic!("Filter expects a list");
                            }
                        } else {
                            panic!("Filter expects a list");
                        }
                    }
                },
                Ok(Instr::Fold) => {
                    let func_reg = opcode[1] as usize + self.window_start;
                    let acc_reg = opcode[2] as usize + self.window_start;
                    let list_reg = opcode[3] as usize + self.window_start;
                    let temp_reg = prog.read_byte().unwrap() as usize + self.window_start;

                    let list_val = self.registers[list_reg];
                    if list_val.is_nil() {
                        // Done
                    } else {
                        if let ValueKind::Object(handle) = list_val.kind() {
                            if let Some(HeapValue::Pair(p)) = self.heap.get(handle) {
                                let car = p.car;
                                let cdr = p.cdr;
                                self.registers[list_reg] = cdr;

                                let resolved_func = self.resolve_value(&self.registers[func_reg]);
                                let (header, address, captures) = if let ValueKind::Object(handle) = resolved_func.kind() {
                                    match self.heap.get(handle) {
                                        Some(HeapValue::FuncRef(f)) => (f.header, f.address, None),
                                        Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone())),
                                        _ => panic!("Fold expects a function")
                                    }
                                } else {
                                    panic!("Fold expects a function");
                                };

                                let param_start = temp_reg - self.window_start;
                                let size = temp_reg + header.register_count as usize;
                                if size >= self.registers.len() {
                                    self.registers.resize(size, empty_value());
                                }
                                let old_ws = self.window_start;
                                let ret_addr = prog.current_address() - 5; // Return to Fold (5 bytes back: Opcode(4) + Byte(1))
                                let state = CallState{window_start: old_ws, result_reg: header.result_reg, target_reg: (acc_reg - self.window_start) as u8, return_addr: ret_addr};
                                self.call_states.push(state);
                                self.window_start += param_start;
                                
                                if let Some(caps) = captures {
                                    let start_reg = header.param_count as usize;
                                    for (i, val) in caps.into_iter().enumerate() {
                                        self.registers[self.window_start + start_reg + i] = val;
                                    }
                                }

                                // Fold expects 2 args: val, acc
                                self.registers[self.window_start] = car;
                                self.registers[self.window_start + 1] = self.registers[acc_reg];

                                if self.jit_enabled {
                                    let end_addr = self.scan_function_end(prog, address);
                                    if self.run_jit_function(prog as *mut VirtualProgram, address, end_addr) {
                                        let state = self.call_states.pop().unwrap();
                                        let source_reg = self.window_start + state.result_reg as usize;
                                        let target_reg = state.window_start + state.target_reg as usize;
                                        self.registers.swap(source_reg, target_reg);
                                        self.window_start = old_ws;
                                    } else {
                                        prog.jump_to(address);
                                    }
                                } else {
                                    prog.jump_to(address);
                                }
                            } else {
                                panic!("Fold expects a list");
                            }
                        } else {
                            panic!("Fold expects a list");
                        }
                    }
                },
                Ok(Instr::FilterStep) => {
                    let list_reg = opcode[1] as usize + self.window_start;
                    let res_reg = opcode[2] as usize + self.window_start;
                    let temp_reg = opcode[3] as usize + self.window_start;
                    let val_reg = prog.read_byte().unwrap() as usize + self.window_start;

                    let keep = self.registers[temp_reg].is_true();
                    if keep {
                        let val = self.registers[val_reg];
                        let res = self.registers[res_reg];
                        let new_pair = HeapValue::Pair(Pair { car: val, cdr: res });
                        let new_handle = self.heap.alloc(new_pair);
                        self.registers[res_reg] = Value::object(new_handle);
                    }
                    
                    // Advance list
                    let list_val = self.registers[list_reg];
                    if let ValueKind::Object(handle) = list_val.kind() {
                        if let Some(HeapValue::Pair(p)) = self.heap.get(handle) {
                            self.registers[list_reg] = p.cdr;
                        }
                    }
                },
                Ok(Instr::MakeClosure) => {
                    let dest_reg = opcode[1] as usize + self.window_start;
                    let func_reg = opcode[2] as usize + self.window_start;
                    let count = opcode[3] as usize;
                    
                    let mut captures = Vec::with_capacity(count);
                    for _ in 0..count {
                        let Some(reg_idx) = prog.read_byte() else { break; };
                        let val = self.registers[reg_idx as usize + self.window_start];
                        captures.push(val);
                    }
                    
                    let func_val = self.registers[func_reg];

                    if let ValueKind::Object(handle) = func_val.kind() {
                        if let Some(HeapValue::FuncRef(fd)) = self.heap.get(handle) {
                             let fd_clone = fd.clone();
                             for c in &captures {
                                 self.scratch_buffer.push(*c);
                             }
                             self.collect_garbage();
                             for _ in &captures {
                                 self.scratch_buffer.pop();
                             }
                             self.registers[dest_reg] = Value::object(self.heap.alloc(HeapValue::Closure(ClosureData{function: fd_clone, captures})));
                        } else {
                             self.registers[dest_reg] = Value::nil();
                        }
                    } else {
                        self.registers[dest_reg] = Value::nil(); 
                    }
                },
                Ok(Instr::MakeRef) => {
                    let reg = opcode[1] as usize + self.window_start;
                    let val = self.registers[reg];
                    self.collect_garbage();
                    self.registers[reg] = Value::object(self.heap.alloc(HeapValue::Ref(val)));
                },
                Ok(Instr::SetRef) => {
                    let dest_reg = opcode[1] as usize + self.window_start;
                    let src_reg = opcode[2] as usize + self.window_start;
                    if let ValueKind::Object(handle) = self.registers[dest_reg].kind() {
                        if let Some(HeapValue::Ref(r)) = self.heap.get_mut(handle) {
                            *r = self.registers[src_reg];
                        }
                    }
                },
                Ok(Instr::Deref) => {
                    let dest_reg = opcode[1] as usize + self.window_start;
                    let src_reg = opcode[2] as usize + self.window_start;
                    let val = if let ValueKind::Object(handle) = self.registers[src_reg].kind() {
                        if let Some(HeapValue::Ref(r)) = self.heap.get(handle) {
                            Some(*r)
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    
                    if let Some(v) = val {
                        self.registers[dest_reg] = v;
                    } else {
                        self.registers[dest_reg] = self.registers[src_reg];
                    }
                },
                Ok(Instr::Ret) => {
                    let Some(state) = self.call_states.pop() else {
                        break; //nothing to return from
                    };
                    let source_reg = self.window_start + state.result_reg as usize;
                    let target_reg = state.window_start + state.target_reg as usize;
                    self.registers.swap(source_reg, target_reg);
                    self.window_start = state.window_start;
                    prog.jump_to(state.return_addr);
                },
                _ => {
                    break;
                },
            }

        }

        //cleanup
        /*
        if self.registers.len() > 256 {
            // Only truncate if we are sure we don't need the registers?
            // Actually, if we finished execution, we might want to keep registers for inspection?
            // But for now, let's just ensure we don't panic.
            let res_reg = prog.get_result_reg() as usize + self.window_start;
            if res_reg < 256 {
                self.registers.truncate(256);
            }
        }
        */
        self.registers.shrink_to_fit();

        let res_reg = prog.get_result_reg() as usize + self.window_start;

        //convert result
        Some(self.registers[res_reg].clone())
    }

}

pub fn value_to_sexpr(value: &Value, heap: &Arena<HeapValue>) -> Option<SExpression> {
    match value.kind() {
        ValueKind::Nil => Some(SExpression::List(vec![])),
        ValueKind::Boolean(b) => Some(SExpression::Atom(Atom::Boolean(b))),
        ValueKind::Integer(i) => Some(SExpression::Atom(Atom::Integer(i))),
        ValueKind::Float(f) => Some(SExpression::Atom(Atom::Float(f as f64))),
        ValueKind::Object(handle) => match heap.get(handle) {
            Some(HeapValue::String(s)) => Some(SExpression::Atom(Atom::String(s.clone()))),
            Some(HeapValue::Symbol(s)) => Some(SExpression::Symbol(s.clone())),
            Some(HeapValue::Pair(_pair)) => {
                let mut expressions = Vec::new();
                let mut current = *value;
                loop {
                    match current.kind() {
                        ValueKind::Nil => break,
                        ValueKind::Object(h) => match heap.get(h) {
                            Some(HeapValue::Pair(p)) => {
                                let car = p.car;
                                let sexpr = value_to_sexpr(&car, heap);
                                expressions.push(sexpr.unwrap_or(SExpression::Atom(Atom::Integer(0))));
                                current = p.cdr;
                            },
                            _ => {
                                let sexpr = value_to_sexpr(&current, heap);
                                expressions.push(sexpr.unwrap_or(SExpression::Atom(Atom::Integer(0))));
                                break;
                            }
                        },
                        _ => {
                             let sexpr = value_to_sexpr(&current, heap);
                             expressions.push(sexpr.unwrap_or(SExpression::Atom(Atom::Integer(0))));
                             break;
                        }
                    }
                }
                Some(SExpression::List(expressions))
            },
            Some(HeapValue::FuncRef(_)) => None,
            Some(HeapValue::Closure(_)) => None,
            Some(HeapValue::Ref(r)) => value_to_sexpr(r, heap),
            None => None
        },
        _ => None
    }
}