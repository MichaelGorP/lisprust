use std::collections::HashMap;

use crate::parser::{SExpression, Atom};

use super::vp::{FunctionData, FunctionHeader, Instr, JumpCondition, Value, VirtualProgram};

macro_rules! binary_op {
    ($self:ident, $opcode:ident, $op:tt) => {
        {
            let r1 = &$self.registers[$opcode[2] as usize + $self.window_start];
            let r2 = &$self.registers[$opcode[3] as usize + $self.window_start];
            let res_reg = $opcode[1] as usize + $self.window_start;
            match (r1, r2) {
                (Value::Integer(lhs), Value::Integer(rhs)) => $self.registers[res_reg] = Value::Integer(*lhs $op *rhs),
                (Value::Integer(lhs), Value::Float(rhs)) => $self.registers[res_reg] = Value::Float(*lhs as f64 $op *rhs),
                (Value::Float(lhs), Value::Float(rhs)) => $self.registers[res_reg] = Value::Float(*lhs $op *rhs),
                (Value::Float(lhs), Value::Integer(rhs)) => $self.registers[res_reg] = Value::Float(*lhs $op *rhs as f64),
                _ => break,
            }
        }
    };
}

macro_rules! comparison_op {
    ($self:ident, $opcode:ident, $prog:ident, $op:tt) => {
        {
            let r1 = &$self.registers[$opcode[2] as usize + $self.window_start];
            let r2 = &$self.registers[$opcode[3] as usize + $self.window_start];
            let res_reg = $opcode[1] as usize + $self.window_start;
            let matches = match (r1, r2) {
                (Value::Integer(lhs), Value::Integer(rhs)) => *lhs $op *rhs,
                (Value::Integer(lhs), Value::Float(rhs)) => (*lhs as f64) $op *rhs,
                (Value::Float(lhs), Value::Float(rhs)) => *lhs $op *rhs,
                (Value::Float(lhs), Value::Integer(rhs)) => *lhs $op *rhs as f64,
                _ => break,
            };
            //only override register, if it is true
            if let Value::Boolean(b) = $self.registers[res_reg] {
                if (b && !matches) {
                    $self.registers[res_reg] = Value::Boolean(matches);
                }
            }

            //try if the next instruction is a jump
            let Some(opcode) = $prog.read_opcode() else {
                break;
            };
            if let Ok(Instr::Jump) = opcode[0].try_into() {
                let Some(distance) = $prog.read_int() else {
                    break;
                };
                if opcode[2] == JumpCondition::Jump as u8 {
                    $prog.jump(distance);
                    continue;
                }
                //everything that is not false, is true
                let check = $self.registers[opcode[1] as usize + $self.window_start].is_true();
                if (check && opcode[2] == JumpCondition::JumpTrue as u8) || (!check && opcode[2] == JumpCondition::JumpFalse as u8) {
                    $prog.jump(distance);
                }
            }
            else {
                $prog.jump(-4);
            }
        }
    };
}

const fn empty_value() -> Value {
    Value::Empty
}

struct CallState {
    window_start: usize,
    result_reg: u8,
    target_reg: u8,
    return_addr: u64
}

pub struct Vm {
    registers: Vec<Value>,
    call_states: Vec<CallState>,
    window_start: usize
}

impl Vm {
    pub fn new() -> Vm {
        const EMPTY : Value = empty_value();
        Vm {registers: vec![EMPTY; 256], call_states: Vec::new(), window_start: 0}
    }

    pub fn run(&mut self, prog: &mut VirtualProgram) -> Option<SExpression> {
        let mut global_vars = HashMap::new();

        loop {
            let Some(opcode) = prog.read_opcode() else {
                break;
            };
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
                    self.registers[opcode[1] as usize + self.window_start] = Value::String(val);
                },
                Ok(Instr::CopyReg) => {
                    self.registers[opcode[1] as usize + self.window_start] = self.registers[opcode[2] as usize + self.window_start].clone();
                },
                Ok(Instr::SwapReg) => {
                    let src_reg = self.window_start + opcode[1] as usize;
                    let target_reg = self.window_start + opcode[2] as usize;
                    self.registers.swap(src_reg, target_reg);
                },
                Ok(Instr::Add) => binary_op!(self, opcode, +),
                Ok(Instr::Sub) => binary_op!(self, opcode, -),
                Ok(Instr::Mul) => binary_op!(self, opcode, *),
                Ok(Instr::Div) => binary_op!(self, opcode, /),
                Ok(Instr::Eq) => comparison_op!(self, opcode, prog, ==),
                Ok(Instr::Neq) => comparison_op!(self, opcode, prog, !=),
                Ok(Instr::Lt) => comparison_op!(self, opcode, prog, <),
                Ok(Instr::Gt) => comparison_op!(self, opcode, prog, >),
                Ok(Instr::Leq) => comparison_op!(self, opcode, prog, <=),
                Ok(Instr::Geq) => comparison_op!(self, opcode, prog, >=),
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
                    global_vars.insert(sym_id, self.registers[opcode[1] as usize + self.window_start].clone());
                },
                Ok(Instr::LoadGlobal) => {
                    let Some(sym_id) = prog.read_int() else {
                        break;
                    };
                    let value = global_vars.get(&sym_id);
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
                    self.registers[opcode[1] as usize + self.window_start] = Value::FuncRef(FunctionData{header, address: func_addr as u64});
                },
                Ok(Instr::CallSymbol) => {
                    let mut func = empty_value();
                    std::mem::swap(&mut func, &mut self.registers[opcode[1] as usize + self.window_start]);
                    let Value::FuncRef(func) = func else {
                        break;
                    };

                    let param_start = opcode[2];
                    let size = param_start as usize + func.header.register_count as usize + self.window_start;
                    if size >= self.registers.len() {
                        self.registers.resize(size, empty_value());
                    }
                    let state = CallState{window_start: self.window_start, result_reg: func.header.result_reg, target_reg: opcode[3], return_addr: prog.current_address()};
                    self.call_states.push(state);
                    self.window_start += param_start as usize;
                    prog.jump_to(func.address);
                },
                Ok(Instr::TailCallSymbol) => {
                    let mut func = empty_value();
                    std::mem::swap(&mut func, &mut self.registers[opcode[1] as usize + self.window_start]);
                    let Value::FuncRef(func) = func else {
                        break;
                    };

                    let param_start = opcode[2];
                    for i in self.window_start .. self.window_start + func.header.param_count as usize {
                        let source_reg = i;
                        let target_reg = i + param_start as usize;
                        self.registers.swap(source_reg, target_reg);
                    }

                    if let Some(last_frame) = self.call_states.last_mut() {
                        last_frame.result_reg = func.header.result_reg;
                    }
                    
                    prog.jump_to(func.address);
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
                _ => break,
            }
        }

        //cleanup
        self.registers.truncate(256);
        self.registers.shrink_to_fit();

        //convert result
        match &self.registers[prog.get_result_reg() as usize + self.window_start] {
            Value::Empty => None,
            Value::Boolean(b) => Some(SExpression::Atom(Atom::Boolean(*b))),
            Value::Integer(i) => Some(SExpression::Atom(Atom::Integer(*i))),
            Value::Float(f) => Some(SExpression::Atom(Atom::Float(*f))),
            Value::String(s) => Some(SExpression::Atom(Atom::String(s.clone()))),
            Value::List(_) => todo!(),
            Value::FuncRef(_) => todo!()
        }
    }
}