use super::{compiler::Compiler, vp::Value};

pub fn register_functions(compiler: &mut Compiler) {
    compiler.register_function("sin", sin_impl);
}


fn sin_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        if let Value::Float(f) = input[0] {
            return Value::Float(f.sin())
        }
    }
    return Value::Empty
}