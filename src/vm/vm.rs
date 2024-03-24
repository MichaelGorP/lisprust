use std::{collections::HashMap, vec, cell::RefCell};

use crate::parser::{SExpression, Atom};

use super::vp::{VirtualProgram, Instr, JumpCondition, FunctionHeader};

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

macro_rules! new_comparison {
    ($context:ident, $opcode:ident, $op:tt) => {
        {
            let r1 = &$context.registers[$opcode.r2 as usize + $context.window_start];
            let r2 = &$context.registers[$opcode.r3 as usize + $context.window_start];
            let res_reg = $opcode.r1 as usize + $context.window_start;
            let matches = match (r1, r2) {
                (Value::Integer(lhs), Value::Integer(rhs)) => *lhs $op *rhs,
                (Value::Integer(lhs), Value::Float(rhs)) => (*lhs as f64) $op *rhs,
                (Value::Float(lhs), Value::Float(rhs)) => *lhs $op *rhs,
                (Value::Float(lhs), Value::Integer(rhs)) => *lhs $op *rhs as f64,
                _ => false,
            };
            //only override register, if it is true
            if let Value::Boolean(b) = $context.registers[res_reg] {
                if (b && !matches) {
                    $context.registers[res_reg] = Value::Boolean(matches);
                }
            }
        }
    };
}


type OpCodeHandler = for<'a> fn(&'a OpCodeData, &'a Vec<OpCodeData>, &RefCell<ExecutionContext>) -> Option<RetType<'a>>;

struct RetType<'a> {
    handler: OpCodeHandler,
    opcode: &'a OpCodeData<'a>
}

struct ExecutionContext {
    pc: usize,
    registers: Vec<Value>,
    call_states: Vec<CallState>,
    window_start: usize,
    global_vars: HashMap<i64, Value>
}

struct OpCodeData<'a> {
    handler: OpCodeHandler,
    data_ref: &'a [u8],
    jump_target: usize,
    r1: u8,
    r2: u8,
    r3: u8
}


macro_rules! ret {
    ($context: ident, $program: ident) => {
        {
            $context.pc += 1;
            let next_op = &$program[$context.pc];
            Some(RetType{handler: next_op.handler, opcode: next_op})
        }
    };
}

fn copy_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    let r1 = opcode.r1 as usize + context.window_start;
    let r2 = opcode.r2 as usize + context.window_start;
    context.registers[r1] = context.registers[r2].clone();
    ret!(context, program)
}

fn add_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    let r1 = &context.registers[opcode.r2 as usize + context.window_start];
    let r2 = &context.registers[opcode.r3 as usize + context.window_start];
    let res_reg = opcode.r1 as usize + context.window_start;
    match (r1, r2) {
        (Value::Integer(lhs), Value::Integer(rhs)) => context.registers[res_reg] = Value::Integer(*lhs + *rhs),
        (Value::Integer(lhs), Value::Float(rhs)) => context.registers[res_reg] = Value::Float(*lhs as f64 + *rhs),
        (Value::Float(lhs), Value::Float(rhs)) => context.registers[res_reg] = Value::Float(*lhs + *rhs),
        (Value::Float(lhs), Value::Integer(rhs)) => context.registers[res_reg] = Value::Float(*lhs + *rhs as f64),
        _ => return None,
    };
    ret!(context, program)
}

fn sub_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    let r1 = &context.registers[opcode.r2 as usize + context.window_start];
    let r2 = &context.registers[opcode.r3 as usize + context.window_start];
    let res_reg = opcode.r1 as usize + context.window_start;
    match (r1, r2) {
        (Value::Integer(lhs), Value::Integer(rhs)) => context.registers[res_reg] = Value::Integer(*lhs - *rhs),
        (Value::Integer(lhs), Value::Float(rhs)) => context.registers[res_reg] = Value::Float(*lhs as f64  *rhs),
        (Value::Float(lhs), Value::Float(rhs)) => context.registers[res_reg] = Value::Float(*lhs - *rhs),
        (Value::Float(lhs), Value::Integer(rhs)) => context.registers[res_reg] = Value::Float(*lhs - *rhs as f64),
        _ => return None,
    };
    ret!(context, program)
}

fn eq_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    new_comparison!(context, opcode, ==);
    ret!(context, program)
}

fn neq_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    new_comparison!(context, opcode, !=);
    ret!(context, program)
}

fn lt_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    new_comparison!(context, opcode, <);
    ret!(context, program)
}

fn gt_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    new_comparison!(context, opcode, >);
    ret!(context, program)
}

fn leq_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    new_comparison!(context, opcode, <=);
    ret!(context, program)
}

fn geq_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    new_comparison!(context, opcode, >=);
    ret!(context, program)
}

fn load_int_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    let val = i64::from_le_bytes(opcode.data_ref.try_into().unwrap());
    let ws = context.window_start;
    context.registers[opcode.r1 as usize + ws] = Value::Integer(val);
    ret!(context, program)
}

fn load_bool_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    let ws = context.window_start;
    context.registers[opcode.r1 as usize + ws] = Value::Boolean(opcode.r2 != 0);
    ret!(context, program)
}

fn define_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    let sym_id = i64::from_le_bytes(opcode.data_ref.try_into().unwrap());
    let ws = context.window_start;
    let value = context.registers[opcode.r1 as usize + ws].clone();
    context.global_vars.insert(sym_id, value);
    ret!(context, program)
}

fn load_global_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    let sym_id = i64::from_le_bytes(opcode.data_ref.try_into().unwrap());
    let ws = context.window_start;
    let value = context.global_vars.get(&sym_id);
    match value {
        Some(v) => context.registers[opcode.r1 as usize + ws] = v.clone(),
        _ => context.registers[opcode.r1 as usize + ws] = empty_value()
    }
    ret!(context, program)
}

fn not_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    let ws = context.window_start;

    let value = &context.registers[opcode.r2 as usize + ws];
    match value {
        Value::Boolean(b) => context.registers[opcode.r1 as usize + ws] = Value::Boolean(!*b),
        _ => context.registers[opcode.r1 as usize + ws] = Value::Boolean(false)
    };
    ret!(context, program)
}

fn jump_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    if opcode.r2 == JumpCondition::Jump as u8 {
        context.pc = opcode.jump_target;
        let next_op = &program[context.pc];
        return Some(RetType{handler: next_op.handler, opcode: next_op});
    }
    let ws = context.window_start;
    let value = &context.registers[opcode.r1 as usize + ws];
    let check = value.is_true();
    if (check && opcode.r2 == JumpCondition::JumpTrue as u8) || (!check && opcode.r2 == JumpCondition::JumpFalse as u8) {
        context.pc = opcode.jump_target;
        let next_op = &program[context.pc];
        return Some(RetType{handler: next_op.handler, opcode: next_op});
    }
    ret!(context, program)
}

fn load_func_ref_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();

    let buf : [u8; std::mem::size_of::<FunctionHeader>()] = opcode.data_ref.try_into().unwrap();
    let header: FunctionHeader = unsafe { std::mem::transmute(buf) };
    
    let index = opcode.r1 as usize + context.window_start;
    context.registers[index] = Value::FuncRef(FunctionData{header, address: opcode.jump_target as u64});
    ret!(context, program)
}

fn call_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();

    let mut func = empty_value();
    let ws = context.window_start;
    std::mem::swap(&mut func, &mut context.registers[opcode.r1 as usize + ws]);
    let Value::FuncRef(func) = func else {
        return None;
    };

    let param_start = opcode.r2;
    let size = param_start as usize + func.header.register_count as usize + context.window_start;
    if size >= context.registers.len() {
        context.registers.resize(size, empty_value());
    }

    let state = CallState{window_start: context.window_start, result_reg: func.header.result_reg, target_reg: opcode.r3, return_addr: opcode.jump_target as u64};
    context.call_states.push(state);
    context.window_start += param_start as usize;
    //prog.jump_to(func.address);
    context.pc = func.address as usize;

    let next_op = &program[context.pc];
    Some(RetType{handler: next_op.handler, opcode: next_op})
}

/*
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
*/

fn call_tail_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();

    let mut func = empty_value();
    let ws = context.window_start;
    std::mem::swap(&mut func, &mut context.registers[opcode.r1 as usize + ws]);
    let Value::FuncRef(func) = func else {
        return None;
    };

    let param_start = opcode.r2;
    for i in context.window_start .. context.window_start + func.header.param_count as usize {
        let source_reg = i;
        let target_reg = i + param_start as usize;
        context.registers.swap(source_reg, target_reg);
    }

    if let Some(last_frame) = context.call_states.last_mut() {
        last_frame.result_reg = func.header.result_reg;
    }
    
    context.pc = func.address as usize;
    let next_op = &program[context.pc];
    Some(RetType{handler: next_op.handler, opcode: next_op})
}

fn ret_handler<'a>(opcode: &'a OpCodeData, program: &'a Vec<OpCodeData>, context_ref: &RefCell<ExecutionContext>) -> Option<RetType<'a>> {
    let mut context = context_ref.borrow_mut();
    let Some(state) = context.call_states.pop() else {
        return None;
    };

    let source_reg = context.window_start + state.result_reg as usize;
    let target_reg = state.window_start + state.target_reg as usize;
    context.registers.swap(source_reg, target_reg);
    context.window_start = state.window_start;
    context.pc = state.return_addr as usize;

    let next_op = &program[context.pc];
    Some(RetType{handler: next_op.handler, opcode: next_op})
}

#[derive(PartialEq, Clone, Debug)]
struct FunctionData {
    header: FunctionHeader,
    address: u64
}

#[derive(PartialEq, Clone, Debug)]
enum Value {
    Empty,
    Boolean(bool),
    Integer(i64),
    Float(f64),
    String(String),
    List(Vec<Value>),
    FuncRef(FunctionData)
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

    pub fn run2(&mut self, prog: &mut VirtualProgram) -> Option<SExpression> {
        let mut program = vec![];
        let data = prog.get_data();
        let mut op_lookup = HashMap::new();
        let mut jump_instructions = vec![];
        loop {
            let Some(opcode) = prog.read_opcode() else {
                break;
            };
            op_lookup.insert(prog.current_address() - 4, program.len());
            match opcode[0].try_into() {
                Ok(Instr::Add) => program.push(OpCodeData{handler: add_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0}),
                Ok(Instr::Sub) => program.push(OpCodeData{handler: sub_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0}),
                Ok(Instr::LoadInt) => {
                    program.push(OpCodeData{handler: load_int_handler, data_ref: &data[prog.current_address() as usize..], r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0});
                    let _ = prog.read_int();
                },
                Ok(Instr::LoadBool) => program.push(OpCodeData{handler: load_bool_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0}),
                Ok(Instr::Define) => {
                    program.push(OpCodeData{handler: define_handler, data_ref: &data[prog.current_address() as usize..], r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0});
                    let _ = prog.read_int();
                },
                Ok(Instr::LoadGlobal) => {
                    program.push(OpCodeData{handler: load_global_handler, data_ref: &data[prog.current_address() as usize..], r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0});
                    let _ = prog.read_int();
                },
                Ok(Instr::CopyReg) => program.push(OpCodeData{handler: copy_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0}),
                Ok(Instr::Eq) => program.push(OpCodeData{handler: eq_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0}),
                Ok(Instr::Neq) => program.push(OpCodeData{handler: neq_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0}),
                Ok(Instr::Lt) => program.push(OpCodeData{handler: lt_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0}),
                Ok(Instr::Gt) => program.push(OpCodeData{handler: gt_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0}),
                Ok(Instr::Leq) => program.push(OpCodeData{handler: leq_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0}),
                Ok(Instr::Geq) => program.push(OpCodeData{handler: geq_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0}),
                Ok(Instr::Not) => program.push(OpCodeData{handler: not_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0}),
                Ok(Instr::Jump) => {
                    let mut distance = prog.read_int().unwrap() as usize;
                    if opcode[2] != JumpCondition::Jump as u8 {
                        distance = prog.current_address() as usize + distance;
                    }
                    program.push(OpCodeData{handler: jump_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: distance});
                    jump_instructions.push(program.len() - 1);
                },
                Ok(Instr::LoadFuncRef) => {
                    let header_addr = prog.read_int().unwrap() as usize;
                    let func_addr = header_addr + std::mem::size_of::<FunctionHeader>() as usize;
                    program.push(OpCodeData{handler: load_func_ref_handler, data_ref: &data[header_addr..], r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: func_addr});
                    jump_instructions.push(program.len() - 1);
                },
                Ok(Instr::CallSymbol) => {
                    program.push(OpCodeData{handler: call_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: program.len()})
                },
                Ok(Instr::TailCallSymbol) => program.push(OpCodeData{handler: call_tail_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0}),
                Ok(Instr::Ret) => program.push(OpCodeData{handler: ret_handler, data_ref: &data, r1: opcode[1], r2: opcode[2], r3: opcode[3], jump_target: 0}),
                _ => {
                    println!("{}", opcode[0]);
                },
            };
        };

        if program.is_empty() {
            return None;
        }

        //update jump targets
        for index in jump_instructions {
            let jump = &mut program[index];
            let target = op_lookup.get(&(jump.jump_target as u64)).unwrap();
            jump.jump_target = *target as usize;
        }

        const EMPTY : Value = empty_value();
        let mut context = RefCell::new(ExecutionContext{pc: 0, registers: vec![EMPTY; 256], call_states: vec![], window_start: 0, global_vars: HashMap::new()});

        let mut handler = program[0].handler;
        let mut opcode = &program[0];
        loop {
            let ret = handler(opcode, &program, &mut context);
            let Some(ret_data) = ret else {
                break;
            };
            handler = ret_data.handler;
            opcode = ret_data.opcode;
        }

        let ctx = context.borrow();
        match &ctx.registers[prog.get_result_reg() as usize + ctx.window_start] {
            Value::Empty => None,
            Value::Boolean(b) => Some(SExpression::Atom(Atom::Boolean(*b))),
            Value::Integer(i) => Some(SExpression::Atom(Atom::Integer(*i))),
            Value::Float(f) => Some(SExpression::Atom(Atom::Float(*f))),
            Value::String(s) => Some(SExpression::Atom(Atom::String(s.clone()))),
            Value::List(_) => todo!(),
            Value::FuncRef(_) => todo!()
        }
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