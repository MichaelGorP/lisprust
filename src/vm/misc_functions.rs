use super::{compiler::Compiler, vp::Value};

pub fn register_functions(compiler: &mut Compiler) {
    compiler.register_function("error", error);
}

fn error(args: &[Value]) -> Value {
    if args.len() < 1 {
        panic!("error expects at least 1 argument");
    }
    // Print error message
    print!("Error: ");
    for arg in args {
        print!("{:?} ", arg);
    }
    println!();
    
    panic!("Runtime Error");
}
