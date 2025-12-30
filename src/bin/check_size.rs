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
pub enum HeapValue {
    String(String),
    List(ListSlice),
    FuncRef(FunctionData),
    Closure(ClosureData),
    Ref(RefCell<Value>)
}

#[derive(PartialEq, Clone, Debug)]
#[repr(C, u8)]
pub enum Value {
    Empty,
    Boolean(bool),
    Integer(i64),
    Float(f64),
    Object(Rc<HeapValue>)
}

fn main() {
    println!("Size of Value: {}", size_of::<Value>());
    println!("Size of HeapValue: {}", size_of::<HeapValue>());
    println!("Size of ListSlice: {}", size_of::<ListSlice>());
    println!("Size of FunctionData: {}", size_of::<FunctionData>());
    
    println!("Align of Value: {}", std::mem::align_of::<Value>());
}