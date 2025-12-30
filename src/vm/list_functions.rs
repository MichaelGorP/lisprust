use std::rc::Rc;
use super::{compiler::Compiler, vp::Value, vp::ListSlice, vp::HeapValue};

pub fn register_functions(compiler: &mut Compiler) {
    compiler.register_function("list", list_impl);
}


fn list_impl(input: &[Value]) -> Value {
    let list = ListSlice::new(input);
    return Value::Object(Rc::new(HeapValue::List(list)))
}