use std::mem::size_of;
use std::rc::Rc;
use std::cell::RefCell;
use std::sync::atomic::AtomicU64;

#[derive(PartialEq, Clone, Debug)]
#[repr(C)]
pub struct FunctionHeader {
    pub param_count: u8,
    pub register_count: u8,
    pub result_reg: u8,
}

#[derive(Debug, Clone)]
#[repr(C)]
pub struct FunctionData {
    pub header: FunctionHeader,
    pub address: u64,
    pub jit_code: u64 
}

impl PartialEq for FunctionData {
    fn eq(&self, other: &Self) -> bool {
        self.header == other.header && self.address == other.address
    }
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
    Closure(ClosureData),
    Ref(Rc<RefCell<Value>>)
}

fn main() {
    println!("Size of Value: {}", size_of::<Value>());
    println!("Size of ListSlice: {}", size_of::<ListSlice>());
    println!("Size of FunctionData: {}", size_of::<FunctionData>());
    println!("Offset of Integer: {}", 0); // It's a union, so data starts at offset 1 (tag is u8) + padding
    
    // Let's check alignment
    println!("Align of Value: {}", std::mem::align_of::<Value>());

    // Check offsets
    let val = Value::FuncRef(FunctionData {
        header: FunctionHeader { param_count: 0, register_count: 0, result_reg: 0 },
        address: 0,
        jit_code: 0xDEADBEEF
    });
    
    let base_ptr = &val as *const Value as usize;
    if let Value::FuncRef(fd) = &val {
        let jit_ptr = &fd.jit_code as *const u64 as usize;
        println!("Offset of jit_code in Value: {}", jit_ptr - base_ptr);
    }
}