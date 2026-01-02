use super::{compiler::Compiler, vp::{Value, VmContext, HeapValue}, gc::Arena};

pub fn register_functions(compiler: &mut Compiler) {
    compiler.register_function("error", error, None);
}

fn error(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() < 1 {
        return Err("error expects at least 1 argument".to_string());
    }
    // Construct error message
    let mut msg = String::from("Error: ");
    let heap = ctx.heap();
    for arg in args {
        msg.push_str(&format!("{} ", value_to_string(arg, heap)));
    }
    
    Err(msg)
}

fn value_to_string(val: &Value, heap: &Arena<HeapValue>) -> String {
    match val {
        Value::Object(handle) => {
            match heap.get(*handle) {
                Some(HeapValue::String(s)) => format!("{:?}", s),
                Some(HeapValue::Symbol(s)) => s.clone(),
                Some(HeapValue::Pair(_)) => "(...)".to_string(),
                Some(HeapValue::FuncRef(_)) => "#<function>".to_string(),
                Some(HeapValue::Closure(_)) => "#<closure>".to_string(),
                Some(HeapValue::Ref(_)) => "#<ref>".to_string(),
                None => "#<invalid>".to_string(),
            }
        },
        _ => format!("{}", val),
    }
}
