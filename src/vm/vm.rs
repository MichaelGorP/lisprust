use case_insensitive_hashmap::CaseInsensitiveHashMap;

use crate::parser::{SExpression, Atom};

use super::vp::{VirtualProgram, Instr, JumpCondition};

macro_rules! binary_op {
    ($self:ident, $opcode:ident, $op:tt) => {
        {
            let r1 = &$self.registers[$opcode[2] as usize];
            let r2 = &$self.registers[$opcode[3] as usize];
            let res_reg = $opcode[1] as usize;
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
    ($self:ident, $opcode:ident, $op:tt) => {
        {
            let r1 = &$self.registers[$opcode[2] as usize];
            let r2 = &$self.registers[$opcode[3] as usize];
            let res_reg = $opcode[1] as usize;
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
        }
    };
}

#[derive(PartialEq, Clone, Debug)]
enum Value {
    Empty,
    Boolean(bool),
    Integer(i64),
    Float(f64),
    String(String),
    List(Vec<Value>)
}

impl Value {
    fn is_true(&self) -> bool {
        match self {
            Self::Boolean(b) if !b => false,
            _ => true
        }
    }
}

const fn empty_value() -> Value {
    Value::Empty
}

pub struct Vm {
    registers: [Value; 256]
}

impl Vm {
    pub fn new() -> Vm {
        const EMPTY : Value = empty_value();
        Vm {registers: [EMPTY; 256]}
    }

    pub fn run(&mut self, prog: &mut VirtualProgram) -> Option<SExpression> {
        let mut global_vars = CaseInsensitiveHashMap::new();

        loop {
            let Some(opcode) = prog.read_opcode() else {
                break;
            };
            match opcode[0].try_into() {
                Ok(Instr::LoadInt) => {
                    let Some(val) = prog.read_int() else {
                        return None;
                    };
                    self.registers[opcode[1] as usize] = Value::Integer(val);
                },
                Ok(Instr::LoadFloat) => {
                    let Some(val) = prog.read_float() else {
                        return None;
                    };
                    self.registers[opcode[1] as usize] = Value::Float(val);
                },
                Ok(Instr::LoadBool) => {
                    self.registers[opcode[1] as usize] = Value::Boolean(opcode[2] != 0);
                },
                Ok(Instr::LoadString) => {
                    let Some(val) = prog.read_string() else {
                        return None;
                    };
                    self.registers[opcode[1] as usize] = Value::String(val);
                },
                Ok(Instr::CopyReg) => {
                    self.registers[opcode[1] as usize] = self.registers[opcode[2] as usize].clone();
                },
                Ok(Instr::Add) => binary_op!(self, opcode, +),
                Ok(Instr::Sub) => binary_op!(self, opcode, -),
                Ok(Instr::Mul) => binary_op!(self, opcode, *),
                Ok(Instr::Div) => binary_op!(self, opcode, /),
                Ok(Instr::Eq) => comparison_op!(self, opcode, ==),
                Ok(Instr::Lt) => comparison_op!(self, opcode, <),
                Ok(Instr::Gt) => comparison_op!(self, opcode, >),
                Ok(Instr::Leq) => comparison_op!(self, opcode, <=),
                Ok(Instr::Geq) => comparison_op!(self, opcode, >=),
                Ok(Instr::Not) => {
                    let value = &self.registers[opcode[2] as usize];
                    match value {
                        Value::Boolean(b) => self.registers[opcode[1] as usize] = Value::Boolean(!*b),
                        _ => self.registers[opcode[1] as usize] = Value::Boolean(false)
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
                    let check = self.registers[opcode[1] as usize].is_true();
                    if (check && opcode[2] == JumpCondition::JumpTrue as u8) || (!check && opcode[2] == JumpCondition::JumpFalse as u8) {
                        prog.jump(distance);
                    }
                },
                Ok(Instr::Define) => {
                    let Some(sym_name) = prog.read_string() else {
                        break;
                    };
                    global_vars.insert(sym_name, self.registers[opcode[1] as usize].clone());
                },
                Ok(Instr::LoadGlobal) => {
                    let Some(sym_name) = prog.read_string() else {
                        break;
                    };
                    let value = global_vars.get(sym_name);
                    match value {
                        Some(v) => self.registers[opcode[1] as usize] = v.clone(),
                        _ => self.registers[opcode[1] as usize] = empty_value()
                    }
                },
                _ => break,
            }
        }

        //convert result
        match &self.registers[prog.get_result_reg() as usize] {
            Value::Empty => None,
            Value::Boolean(b) => Some(SExpression::Atom(Atom::Boolean(*b))),
            Value::Integer(i) => Some(SExpression::Atom(Atom::Integer(*i))),
            Value::Float(f) => Some(SExpression::Atom(Atom::Float(*f))),
            Value::String(s) => Some(SExpression::Atom(Atom::String(s.clone()))),
            Value::List(_) => todo!(),
        }
    }
}