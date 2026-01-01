use std::{cell::Cell, io::{Cursor, Read}, mem::size_of, ops::Range, collections::HashMap};
use gc::{Gc, GcCell, Trace, Finalize};

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

impl Finalize for FunctionData {}
unsafe impl Trace for FunctionData {
    unsafe fn trace(&self) {}
    unsafe fn root(&self) {}
    unsafe fn unroot(&self) {}
    fn finalize_glue(&self) { self.finalize(); }
}

impl PartialEq for FunctionData {
    fn eq(&self, other: &Self) -> bool {
        self.header == other.header && self.address == other.address
    }
}

pub struct Pair {
    pub car: GcCell<Value>,
    pub cdr: GcCell<Value>,
}

impl Finalize for Pair {}
unsafe impl Trace for Pair {
    unsafe fn trace(&self) {
        self.car.trace();
        self.cdr.trace();
    }
    unsafe fn root(&self) {
        self.car.root();
        self.cdr.root();
    }
    unsafe fn unroot(&self) {
        self.car.unroot();
        self.cdr.unroot();
    }
    fn finalize_glue(&self) {
        self.finalize();
        self.car.finalize_glue();
        self.cdr.finalize_glue();
    }
}

impl Clone for Pair {
    fn clone(&self) -> Self {
        Pair {
            car: GcCell::new(self.get_car()),
            cdr: GcCell::new(self.get_cdr()),
        }
    }
}

impl Pair {
    pub fn get_car(&self) -> Value {
        self.car.borrow().clone()
    }

    pub fn get_cdr(&self) -> Value {
        self.cdr.borrow().clone()
    }
}

impl PartialEq for Pair {
    fn eq(&self, other: &Self) -> bool {
        self.get_car() == other.get_car() && self.get_cdr() == other.get_cdr()
    }
}

impl std::fmt::Debug for Pair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Pair")
         .field("car", &self.get_car())
         .field("cdr", &self.get_cdr())
         .finish()
    }
}

#[derive(PartialEq, Clone, Debug)]
pub struct ClosureData {
    pub function: FunctionData,
    pub captures: Vec<Value>
}

impl Finalize for ClosureData {}
unsafe impl Trace for ClosureData {
    unsafe fn trace(&self) {
        self.function.trace();
        self.captures.trace();
    }
    unsafe fn root(&self) {
        self.function.root();
        self.captures.root();
    }
    unsafe fn unroot(&self) {
        self.function.unroot();
        self.captures.unroot();
    }
    fn finalize_glue(&self) {
        self.finalize();
        self.function.finalize_glue();
        self.captures.finalize_glue();
    }
}

#[derive(PartialEq, Clone, Debug)]
pub enum HeapValue {
    String(String),
    Symbol(String),
    Pair(Pair),
    FuncRef(FunctionData),
    Closure(ClosureData),
    Ref(GcCell<Value>)
}

impl Finalize for HeapValue {}
unsafe impl Trace for HeapValue {
    unsafe fn trace(&self) {
        match self {
            HeapValue::String(_) | HeapValue::Symbol(_) => {},
            HeapValue::Pair(p) => p.trace(),
            HeapValue::FuncRef(f) => f.trace(),
            HeapValue::Closure(c) => c.trace(),
            HeapValue::Ref(r) => r.trace(),
        }
    }
    unsafe fn root(&self) {
        match self {
            HeapValue::String(_) | HeapValue::Symbol(_) => {},
            HeapValue::Pair(p) => p.root(),
            HeapValue::FuncRef(f) => f.root(),
            HeapValue::Closure(c) => c.root(),
            HeapValue::Ref(r) => r.root(),
        }
    }
    unsafe fn unroot(&self) {
        match self {
            HeapValue::String(_) | HeapValue::Symbol(_) => {},
            HeapValue::Pair(p) => p.unroot(),
            HeapValue::FuncRef(f) => f.unroot(),
            HeapValue::Closure(c) => c.unroot(),
            HeapValue::Ref(r) => r.unroot(),
        }
    }
    fn finalize_glue(&self) {
        self.finalize();
        match self {
            HeapValue::String(_) | HeapValue::Symbol(_) => {},
            HeapValue::Pair(p) => p.finalize_glue(),
            HeapValue::FuncRef(f) => f.finalize_glue(),
            HeapValue::Closure(c) => c.finalize_glue(),
            HeapValue::Ref(r) => r.finalize_glue(),
        }
    }
}

#[derive(PartialEq, Clone, Debug)]
#[repr(C, u8)]
pub enum Value {
    Empty,
    Boolean(bool),
    Integer(i64),
    Float(f64),
    Object(Gc<HeapValue>)
}

impl Finalize for Value {}
unsafe impl Trace for Value {
    unsafe fn trace(&self) {
        match self {
            Value::Object(o) => o.trace(),
            _ => {}
        }
    }
    unsafe fn root(&self) {
        match self {
            Value::Object(o) => o.root(),
            _ => {}
        }
    }
    unsafe fn unroot(&self) {
        match self {
            Value::Object(o) => o.unroot(),
            _ => {}
        }
    }
    fn finalize_glue(&self) {
        self.finalize();
        match self {
            Value::Object(o) => o.finalize_glue(),
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

    pub fn as_func_ref(&self) -> Option<&FunctionData> {
        if let Value::Object(o) = self {
            if let HeapValue::FuncRef(f) = &**o {
                return Some(f);
            }
        }
        None
    }

    pub fn as_closure(&self) -> Option<&ClosureData> {
        if let Value::Object(o) = self {
            if let HeapValue::Closure(c) = &**o {
                return Some(c);
            }
        }
        None
    }
    
    pub fn as_ref(&self) -> Option<&GcCell<Value>> {
        if let Value::Object(o) = self {
            if let HeapValue::Ref(r) = &**o {
                return Some(r);
            }
        }
        None
    }
}


pub type VmCallableFunction = fn(&[Value]) -> Value;

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