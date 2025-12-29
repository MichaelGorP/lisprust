use std::mem::size_of;
use std::rc::Rc;
use std::cell::RefCell;

#[derive(PartialEq, Clone, Debug)]
#[repr(C)]
pub struct FunctionHeader {
    pub param_count: u8,
    pub register_count: u8,
    pub result_reg: u8,
}

#[derive(PartialEq, Clone, Debug)]
#[repr(C)]
pub struct FunctionData {
    pub header: FunctionHeader,
    pub address: u64,
    pub jit_code: u64 
}

#[derive(PartialEq, Clone, Debug)]
pub struct ListSlice {
    data_ptr: Rc<RefCell<Vec<Value>>>,
    offset: usize,
    length: usize
}

#[derive(PartialEq, Clone, Debug)]
pub struct ClosureData {
    pub function: FunctionData,
    pub captures: Vec<Value>
}

#[derive(PartialEq, Clone, Debug)]
#[repr(C, u8)]
pub enum Value {
    Empty,
    Boolean(bool),
    Integer(i64),
    Float(f64),
    String(Rc<String>),
    List(ListSlice),
    FuncRef(FunctionData),
    Closure(Rc<ClosureData>),
    Ref(Rc<RefCell<Value>>)
}

fn main() {
    println!("Size of Value: {}", size_of::<Value>());
    println!("Offset of Integer: {}", 0); // It's a union, so data starts at offset 1 (tag is u8) + padding
    
    // Let's check alignment
    println!("Align of Value: {}", std::mem::align_of::<Value>());
}