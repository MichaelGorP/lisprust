use std::rc::Rc;
use std::cell::{Cell, RefCell};
use std::collections::HashSet;

use crate::parser::{SExpression, Atom};

use super::vp::{ClosureData, FunctionData, FunctionHeader, Instr, JumpCondition, Value, HeapValue, VirtualProgram};
use super::jit::Jit;

macro_rules! binary_op {
    ($self:ident, $opcode:ident, $op:tt) => {
        {
            let v1 = $self.resolve_value(&$self.registers[$opcode[2] as usize + $self.window_start]);
            let v2 = $self.resolve_value(&$self.registers[$opcode[3] as usize + $self.window_start]);
            
            let res_reg = $opcode[1] as usize + $self.window_start;
            match (v1, v2) {
                (Value::Integer(lhs), Value::Integer(rhs)) => $self.registers[res_reg] = Value::Integer(lhs $op rhs),
                (Value::Integer(lhs), Value::Float(rhs)) => $self.registers[res_reg] = Value::Float(lhs as f64 $op rhs),
                (Value::Float(lhs), Value::Float(rhs)) => $self.registers[res_reg] = Value::Float(lhs $op rhs),
                (Value::Float(lhs), Value::Integer(rhs)) => $self.registers[res_reg] = Value::Float(lhs $op rhs as f64),
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
            let matches = match (v1, v2) {
                (Value::Integer(lhs), Value::Integer(rhs)) => lhs $op rhs,
                (Value::Integer(lhs), Value::Float(rhs)) => (lhs as f64) $op rhs,
                (Value::Float(lhs), Value::Float(rhs)) => lhs $op rhs,
                (Value::Float(lhs), Value::Integer(rhs)) => lhs $op rhs as f64,
                _ => break,
            };
            
            $self.registers[res_reg] = Value::Boolean(matches);

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
    Value::Empty
}

#[derive(Debug, Clone)]
pub struct CallState {
    pub window_start: usize,
    pub result_reg: u8,
    pub target_reg: u8,
    pub return_addr: u64
}

pub trait Debugger {
    fn on_step(&mut self, vm: &Vm, prog: &VirtualProgram);
}

#[repr(C)]
pub struct Vm {
    pub registers: Vec<Value>,
    pub global_vars: Vec<Value>,
    pub(super) call_states: Vec<CallState>,
    pub window_start: usize,
    pub jit: Jit,
    pub jit_enabled: bool,
    pub scratch_buffer: Vec<Value>,
    pub tail_call_pending: bool,
    pub next_jit_code: u64,
}

impl Vm {
    pub fn new(jit_enabled: bool) -> Vm {
        const EMPTY : Value = empty_value();
        Vm {registers: vec![EMPTY; 64000], global_vars: Vec::new(), call_states: Vec::new(), window_start: 0, jit: Jit::new(), jit_enabled, scratch_buffer: Vec::with_capacity(32), tail_call_pending: false, next_jit_code: 0}
    }

    pub fn run_jit_function(&mut self, prog: *mut VirtualProgram, start_addr: u64, end_addr: u64) {
        match self.jit.compile(&self.global_vars, unsafe { &mut *prog }, start_addr, end_addr) {
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
            },
            Err(e) => {
                println!("JIT compilation failed: {}", e);
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
        if let Value::Object(o) = val {
            if let HeapValue::Ref(r) = &**o {
                return r.borrow().clone();
            }
        }
        val.clone()
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
                // eprintln!("Exec: {:?} {:?}", instr, opcode);
                
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
                    Ok(Instr::LoadInt) | Ok(Instr::LoadFloat) | Ok(Instr::Define) | Ok(Instr::LoadGlobal) | Ok(Instr::LoadFuncRef) => { let _ = prog.read_int(); },
                    Ok(Instr::LoadString) => { let _ = prog.read_string(); },
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

    pub fn run(&mut self, prog: &mut VirtualProgram) -> Option<SExpression> {
        self.run_debug(prog, None)
    }

    pub fn run_debug(&mut self, prog: &mut VirtualProgram, mut debugger: Option<&mut dyn Debugger>) -> Option<SExpression> {
        loop {
            if let Some(dbg) = &mut debugger {
                dbg.on_step(self, prog);
            }

            let Some(opcode) = prog.read_opcode() else {
                break;
            };
            // let pc = prog.current_address() - 4;
            // let instr: Result<Instr, _> = opcode[0].try_into();
            // eprintln!("PC: {}, Instr: {:?}", pc, instr);

            match opcode[0].try_into() {
                Ok(Instr::LoadInt) => {
                    let Some(val) = prog.read_int() else {
                        return None;
                    };
                    self.registers[opcode[1] as usize + self.window_start] = Value::Integer(val);
                },
                Ok(Instr::LoadFloat) => {
                    let Some(val) = prog.read_float() else {
                        return None;
                    };
                    self.registers[opcode[1] as usize + self.window_start] = Value::Float(val);
                },
                Ok(Instr::LoadBool) => {
                    self.registers[opcode[1] as usize + self.window_start] = Value::Boolean(opcode[2] != 0);
                },
                Ok(Instr::LoadString) => {
                    let Some(val) = prog.read_string() else {
                        return None;
                    };
                    self.registers[opcode[1] as usize + self.window_start] = Value::Object(Rc::new(HeapValue::String(val)));
                },
                Ok(Instr::CopyReg) => {
                    self.registers[opcode[1] as usize + self.window_start] = self.registers[opcode[2] as usize + self.window_start].clone();
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
                Ok(Instr::Eq) => comparison_op!(self, opcode, prog, debugger, ==),
                Ok(Instr::Neq) => comparison_op!(self, opcode, prog, debugger, !=),
                Ok(Instr::Lt) => comparison_op!(self, opcode, prog, debugger, <),
                Ok(Instr::Gt) => comparison_op!(self, opcode, prog, debugger, >),
                Ok(Instr::Leq) => comparison_op!(self, opcode, prog, debugger, <=),
                Ok(Instr::Geq) => comparison_op!(self, opcode, prog, debugger, >=),
                Ok(Instr::Not) => {
                    let value = &self.registers[opcode[2] as usize + self.window_start];
                    match value {
                        Value::Boolean(b) => self.registers[opcode[1] as usize + self.window_start] = Value::Boolean(!*b),
                        _ => self.registers[opcode[1] as usize] = Value::Boolean(false)
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
                        self.global_vars.resize(sym_id as usize + 1, Value::Empty);
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
                    // eprintln!("LoadFuncRef: header_addr={}, func_addr={}", header_addr, func_addr);
                    self.registers[opcode[1] as usize + self.window_start] = Value::Object(Rc::new(HeapValue::FuncRef(FunctionData{header, address: func_addr as u64, jit_code: Cell::new(0), fast_jit_code: Cell::new(0)})));
                },
                Ok(Instr::CallSymbol) => {
                    let func_reg = opcode[1] as usize + self.window_start;
                    let resolved_func = self.resolve_value(&self.registers[func_reg]);

                    let (header, address, captures) = if let Some(f) = resolved_func.as_func_ref() {
                        (f.header, f.address, None)
                    } else if let Some(c) = resolved_func.as_closure() {
                        (c.function.header, c.function.address, Some(c.captures.clone()))
                    } else {
                        break;
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
                        let end_addr = self.scan_function_end(prog, address);
                        self.run_jit_function(prog as *mut VirtualProgram, address, end_addr);
                        
                        let state = self.call_states.pop().unwrap();
                        let source_reg = self.window_start + state.result_reg as usize;
                        let target_reg = state.window_start + state.target_reg as usize;
                        self.registers.swap(source_reg, target_reg);

                        self.window_start = old_ws;
                    } else {
                        prog.jump_to(address);
                    }
                },
                Ok(Instr::TailCallSymbol) => {
                    // For tail-calls, clone the function value instead of swapping it out.
                    let resolved_func = self.resolve_value(&self.registers[opcode[1] as usize + self.window_start]);

                    let (header, address, captures) = if let Some(f) = resolved_func.as_func_ref() {
                        (f.header, f.address, None)
                    } else if let Some(c) = resolved_func.as_closure() {
                        (c.function.header, c.function.address, Some(c.captures.clone()))
                    } else {
                        break;
                    };

                    // eprintln!("TailCallSymbol: jumping to {}, param_count={}", address, header.param_count);

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
                        let end_addr = self.scan_function_end(prog, address);
                        // println!("Scanned end for {}: {}", address, end_addr);
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
                        break;
                    };
                    let Some(function) = prog.get_function(func_id) else {
                        break;
                    };
                    let start_reg = opcode[2] as usize;
                    let reg_count = opcode[3] as usize;
                    self.registers[opcode[1] as usize + self.window_start] = function(&self.registers[self.window_start + start_reg.. self.window_start + start_reg + reg_count]);
                }
                Ok(Instr::MakeClosure) => {
                    let dest_reg = opcode[1] as usize + self.window_start;
                    let func_reg = opcode[2] as usize + self.window_start;
                    let count = opcode[3] as usize;
                    
                    let mut captures = Vec::with_capacity(count);
                    for _ in 0..count {
                        let Some(reg_idx) = prog.read_byte() else { break; };
                        let val = self.registers[reg_idx as usize + self.window_start].clone();
                        captures.push(val);
                    }
                    
                    let func_val = &self.registers[func_reg];

                    if let Some(fd) = func_val.as_func_ref() {
                        self.registers[dest_reg] = Value::Object(Rc::new(HeapValue::Closure(ClosureData{function: fd.clone(), captures})));
                    } else {
                        self.registers[dest_reg] = Value::Empty; 
                    }
                },
                Ok(Instr::MakeRef) => {
                    let reg = opcode[1] as usize + self.window_start;
                    let val = self.registers[reg].clone();
                    self.registers[reg] = Value::Object(Rc::new(HeapValue::Ref(RefCell::new(val))));
                },
                Ok(Instr::SetRef) => {
                    let dest_reg = opcode[1] as usize + self.window_start;
                    let src_reg = opcode[2] as usize + self.window_start;
                    if let Some(r) = self.registers[dest_reg].as_ref() {
                        *r.borrow_mut() = self.registers[src_reg].clone();
                    }
                },
                Ok(Instr::Deref) => {
                    let dest_reg = opcode[1] as usize + self.window_start;
                    let src_reg = opcode[2] as usize + self.window_start;
                    let val = if let Some(r) = self.registers[src_reg].as_ref() {
                        Some(r.borrow().clone())
                    } else {
                        None
                    };
                    
                    if let Some(v) = val {
                        self.registers[dest_reg] = v;
                    } else {
                        self.registers[dest_reg] = self.registers[src_reg].clone();
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
        self.registers.truncate(256);
        self.registers.shrink_to_fit();

        let res_reg = prog.get_result_reg() as usize + self.window_start;

        //convert result
        value_to_sexpr(&self.registers[res_reg])
    }

}

fn value_to_sexpr(value: &Value) -> Option<SExpression> {
    match value {
        Value::Empty => None,
        Value::Boolean(b) => Some(SExpression::Atom(Atom::Boolean(*b))),
        Value::Integer(i) => Some(SExpression::Atom(Atom::Integer(*i))),
        Value::Float(f) => Some(SExpression::Atom(Atom::Float(*f))),
        Value::Object(o) => match &**o {
            HeapValue::String(s) => Some(SExpression::Atom(Atom::String(s.clone()))),
            HeapValue::List(l) => {
                let mut expressions = Vec::with_capacity(l.len());
                let data_ref = l.values();
                for value in &data_ref[l.offset() .. l.offset() + l.len()] {
                    let sexpr = value_to_sexpr(value);
                    expressions.push(sexpr.unwrap_or(SExpression::Atom(Atom::Integer(0))));
                }
                Some(SExpression::List(expressions))
            },
            HeapValue::FuncRef(_) => None,
            HeapValue::Closure(_) => None,
            HeapValue::Ref(r) => value_to_sexpr(&r.borrow())
        }
    }
}