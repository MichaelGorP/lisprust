use super::{compiler::Compiler, vp::Value, vp::VmContext};

pub fn register_functions(compiler: &mut Compiler) {
    compiler.register_function("error", error, None);
}

fn error(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() < 1 {
        return Err("error expects at least 1 argument".to_string());
    }
    // Construct error message
    let mut msg = String::from("Error: ");
    for arg in args {
        msg.push_str(&format!("{:?} ", arg));
    }
    
    Err(msg)
}
