use std::{cell::Cell, io::{Cursor, Read}, mem::size_of, ops::Range, collections::HashMap};
use crate::vm::gc::{Handle, Trace, Arena};

use enum_display::EnumDisplay;

#[repr(u8)]
#[derive(Clone, Copy, EnumDisplay, Debug, PartialEq, Eq)]
pub(super) enum Instr {
    //register handling
    LoadInt,
    LoadFloat,
    LoadBool,
    LoadString,
    LoadSymbol,
    LoadNil,
    CopyReg,
    SwapReg,
    //arithmetic
    Add,
    Sub,
    Mul,
    Div,
    //comparisons
    Eq,
    Neq,
    Lt,
    Gt,
    Leq,
    Geq,
    //control flow
    Not,
    Jump,
    //definitions, symbols, and function handling
    Define,
    LoadGlobal,
    LoadFuncRef,
    CallSymbol,
    TailCallSymbol, //does a call without creating a new call frame
    CallFunction,
    Ret,
    MakeClosure,
    MakeRef,
    SetRef,
    Deref
}

#[repr(u8)]
#[derive(Clone, Copy)]
pub(super) enum JumpCondition {
    JumpTrue,
    JumpFalse,
    Jump
}

impl TryFrom<u8> for Instr {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            x if x == Instr::LoadInt as u8 => Ok(Instr::LoadInt),
            x if x == Instr::LoadFloat as u8 => Ok(Instr::LoadFloat),
            x if x == Instr::LoadBool as u8 => Ok(Instr::LoadBool),
            x if x == Instr::LoadString as u8 => Ok(Instr::LoadString),
            x if x == Instr::LoadSymbol as u8 => Ok(Instr::LoadSymbol),
            x if x == Instr::LoadNil as u8 => Ok(Instr::LoadNil),
            x if x == Instr::CopyReg as u8 => Ok(Instr::CopyReg),
            x if x == Instr::SwapReg as u8 => Ok(Instr::SwapReg),
            x if x == Instr::Add as u8 => Ok(Instr::Add),
            x if x == Instr::Sub as u8 => Ok(Instr::Sub),
            x if x == Instr::Mul as u8 => Ok(Instr::Mul),
            x if x == Instr::Div as u8 => Ok(Instr::Div),
            x if x == Instr::Eq as u8 => Ok(Instr::Eq),
            x if x == Instr::Neq as u8 => Ok(Instr::Neq),
            x if x == Instr::Lt as u8 => Ok(Instr::Lt),
            x if x == Instr::Gt as u8 => Ok(Instr::Gt),
            x if x == Instr::Leq as u8 => Ok(Instr::Leq),
            x if x == Instr::Geq as u8 => Ok(Instr::Geq),
            x if x == Instr::Not as u8 => Ok(Instr::Not),
            x if x == Instr::Jump as u8 => Ok(Instr::Jump),
            x if x == Instr::Define as u8 => Ok(Instr::Define),
            x if x == Instr::LoadGlobal as u8 => Ok(Instr::LoadGlobal),
            x if x == Instr::LoadFuncRef as u8 => Ok(Instr::LoadFuncRef),
            x if x == Instr::CallSymbol as u8 => Ok(Instr::CallSymbol),
            x if x == Instr::TailCallSymbol as u8 => Ok(Instr::TailCallSymbol),
            x if x == Instr::CallFunction as u8 => Ok(Instr::CallFunction),
            x if x == Instr::Ret as u8 => Ok(Instr::Ret),
            x if x == Instr::MakeClosure as u8 => Ok(Instr::MakeClosure),
            x if x == Instr::MakeRef as u8 => Ok(Instr::MakeRef),
            x if x == Instr::SetRef as u8 => Ok(Instr::SetRef),
            x if x == Instr::Deref as u8 => Ok(Instr::Deref),
            _ => Err(())
        }
    }
}

pub(super) struct OpCode {
    data: [u8; 4]
}

impl OpCode {
    pub fn new_dest(instr: Instr, dest_reg: u8) -> OpCode {
        OpCode{data: [instr as u8, dest_reg, 0, 0]}
    }

    pub fn new(instr: Instr, dest_reg: u8, r1: u8, r2: u8) -> OpCode {
        OpCode{data: [instr as u8, dest_reg, r1, r2]}
    }

    pub fn get_data(&self) -> [u8; 4] {
        self.data
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(packed)]
pub struct FunctionHeader {
    pub param_count: u8,
    pub register_count: u8,
    pub result_reg: u8
}

impl FunctionHeader {
    pub fn as_u8_slice(&self) -> &[u8] {
         unsafe { core::slice::from_raw_parts((self as *const FunctionHeader) as *const u8, std::mem::size_of::<FunctionHeader>()) }
    }

    pub fn read(reader: &mut Cursor<Vec<u8>>) -> FunctionHeader {
        let mut buf = [0; std::mem::size_of::<FunctionHeader>()];
        let _ = reader.read(&mut buf);
        let header: FunctionHeader = unsafe { std::mem::transmute(buf) };
        header
    }
}


#[derive(Debug, Clone)]
#[repr(C)]
pub struct FunctionData {
    pub header: FunctionHeader,
    pub address: u64,
    pub jit_code: Cell<u64>, // 0 if None
    pub fast_jit_code: Cell<u64> // 0 if None
}

impl Trace<HeapValue> for FunctionData {
    fn trace(&self, _arena: &mut Arena<HeapValue>) {}
}

impl PartialEq for FunctionData {
    fn eq(&self, other: &Self) -> bool {
        self.header == other.header && self.address == other.address
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Pair {
    pub car: Value,
    pub cdr: Value,
}

impl Trace<HeapValue> for Pair {
    fn trace(&self, arena: &mut Arena<HeapValue>) {
        self.car.trace(arena);
        self.cdr.trace(arena);
    }
}

#[derive(PartialEq, Clone)]
pub struct ClosureData {
    pub function: FunctionData,
    pub captures: Vec<Value>
}

impl std::fmt::Debug for ClosureData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ClosureData")
         .field("function", &self.function)
         .field("captures", &self.captures)
         .finish()
    }
}

impl Trace<HeapValue> for ClosureData {
    fn trace(&self, arena: &mut Arena<HeapValue>) {
        self.function.trace(arena);
        for capture in &self.captures {
            capture.trace(arena);
        }
    }
}

#[derive(PartialEq, Clone)]
pub enum HeapValue {
    String(String),
    Symbol(String),
    Pair(Pair),
    FuncRef(FunctionData),
    Closure(ClosureData),
    Ref(Value)
}

impl std::fmt::Debug for HeapValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl std::fmt::Display for HeapValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HeapValue::String(s) => write!(f, "{:?}", s),
            HeapValue::Symbol(s) => write!(f, "{}", s),
            HeapValue::Pair(_) => write!(f, "(...)"),
            HeapValue::FuncRef(_) => write!(f, "#<function>"),
            HeapValue::Closure(_) => write!(f, "#<closure>"),
            HeapValue::Ref(_) => write!(f, "#<ref>"),
        }
    }
}

impl Trace<HeapValue> for HeapValue {
    fn trace(&self, arena: &mut Arena<HeapValue>) {
        match self {
            HeapValue::String(_) | HeapValue::Symbol(_) => {},
            HeapValue::Pair(p) => p.trace(arena),
            HeapValue::FuncRef(f) => f.trace(arena),
            HeapValue::Closure(c) => c.trace(arena),
            HeapValue::Ref(v) => v.trace(arena),
        }
    }
}

#[derive(PartialEq, Clone, Copy)]
#[repr(C, u8)]
pub enum Value {
    Empty,
    Boolean(bool),
    Integer(i64),
    Float(f64),
    Object(Handle)
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Empty => write!(f, "()"),
            Value::Boolean(b) => write!(f, "{}", if *b { "#t" } else { "#f" }),
            Value::Integer(i) => write!(f, "{}", i),
            Value::Float(fl) => write!(f, "{}", fl),
            Value::Object(_) => write!(f, "#<object>"),
        }
    }
}

impl Trace<HeapValue> for Value {
    fn trace(&self, arena: &mut Arena<HeapValue>) {
        match self {
            Value::Object(handle) => arena.mark(*handle),
            _ => {}
        }
    }
}

impl Value {
    pub fn is_true(&self) -> bool {
        match self {
            Self::Boolean(b) if !b => false,
            _ => true
        }
    }
}


pub trait VmContext {
    fn heap(&mut self) -> &mut Arena<HeapValue>;
    fn collect(&mut self);
    fn push_scratch(&mut self, val: Value);
    fn pop_scratch(&mut self);
}

pub type VmCallableFunction = fn(&mut dyn VmContext, &[Value]) -> Result<Value, String>;

#[derive(Clone)]
pub struct VirtualProgram {
    listing: String,
    pub cursor: Cursor<Vec<u8>>,
    functions: Vec<VmCallableFunction>,
    result_reg: u8,
    pub source_map: Vec<(usize, Range<usize>)>,
    pub debug_symbols: HashMap<usize, HashMap<u8, String>>
}


impl VirtualProgram {
    pub(super) fn new(listing: String, bytecode: Vec<u8>, result_reg: u8, functions: Vec<VmCallableFunction>, source_map: Vec<(usize, Range<usize>)>, debug_symbols: HashMap<usize, HashMap<u8, String>>) -> VirtualProgram {
        let prog = VirtualProgram{listing, cursor: Cursor::new(bytecode), result_reg, functions, source_map, debug_symbols};
        prog
    }

    pub fn get_listing(&self) -> String {
        self.listing.clone()
    }

    pub fn get_bytecode(&self) -> &[u8] {
        self.cursor.get_ref()
    }

    pub fn get_result_reg(&self) -> u8 {
        self.result_reg
    }

    pub fn current_address(&self) -> u64 {
        self.cursor.position()
    }

    pub(super) fn read_opcode(&mut self) -> Option<[u8; 4]> {
        let mut buffer = [0 as u8; 4];
        if let Ok(()) = self.cursor.read_exact(&mut buffer) {
            Some(buffer)
        }
        else {
            None
        }
    }

    pub(super) fn read_byte(&mut self) -> Option<u8> {
        let mut buffer = [0 as u8; 1];
        if let Ok(()) = self.cursor.read_exact(&mut buffer) {
            Some(buffer[0])
        }
        else {
            None
        }
    }

    pub(super) fn read_int(&mut self) -> Option<i64> {
        let mut buffer = [0 as u8; size_of::<i64>()];
        if let Ok(()) = self.cursor.read_exact(&mut buffer) {
            Some(i64::from_le_bytes(buffer))
        }
        else {
            None
        }
    }

    pub(super) fn read_float(&mut self) -> Option<f64> {
        let mut buffer = [0 as u8; size_of::<f64>()];
        if let Ok(()) = self.cursor.read_exact(&mut buffer) {
            Some(f64::from_le_bytes(buffer))
        }
        else {
            None
        }
    }

    pub(super) fn read_string(&mut self) -> Option<String> {
        let mut buffer = [0 as u8; size_of::<usize>()];
        if let Ok(()) = self.cursor.read_exact(&mut buffer) {
            let size = usize::from_le_bytes(buffer);
            // guard against bogus sizes to avoid huge allocations when disassembling
            if size > 1_000_000 {
                return None;
            }
            let mut str_buf: Vec<u8> = Vec::with_capacity(size);
            str_buf.resize(size, 0);
            if let Ok(()) = self.cursor.read_exact(&mut str_buf) {
                if let Ok(str) = String::from_utf8(str_buf) {
                    return Some(str);
                }
            }
        }
        return None;
    }

    pub(super) fn read_function_header(&mut self, addr: u64) -> Option<FunctionHeader> {
        let pos = self.cursor.position();
        self.cursor.set_position(addr);
        let header = FunctionHeader::read(&mut self.cursor);
        self.cursor.set_position(pos);
        Some(header)
    }

    pub(super) fn jump(&mut self, distance: i64) {
        let old = self.cursor.position();
        let pos = (old as i64) + distance;
        self.cursor.set_position(pos as u64);
    }

    pub(super) fn jump_to(&mut self, pos: u64) {
        self.cursor.set_position(pos);
    }

    pub(super) fn get_function(&self, id: i64) -> Option<VmCallableFunction> {
        self.functions.get(id as usize - 1).copied()
    }
}