use std::env;
use std::fs;

use lisp::parser::SExpression;

use lisp::vm::compiler::Compiler;
use lisp::vm::vm::Vm;
use lisp::lexer;
use lisp::parser;

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut generate_asm = false;
    let mut debug_mode = false;
    let mut use_jit = true;
    let mut filename = None;

    for a in args.iter().skip(1) {
        if a == "--asm" {
            generate_asm = true;
        } else if a == "--debug" {
            debug_mode = true;
        } else if a == "--no-jit" {
            use_jit = false;
        } else {
            filename = Some(a);
        }
    }

    if debug_mode {
        eprintln!("Starting DAP server...");
        start_dap_server();
        return;
    }

    let source = if let Some(f) = filename {
        fs::read_to_string(f).expect("Could not read file")
    } else {
        eprintln!("Usage: {} <filename> [--asm] [--debug]", args[0]);
        return;
    };

    let tokens = lexer::tokenize(&source).unwrap_or(vec![]);

    let parser = parser::Parser::new();
    let list = parser.parse(&tokens).unwrap_or((SExpression::from(parser::Atom::Boolean(false)), parser::SourceMap::Leaf(0..0), 0));

    let mut compiler = Compiler::new(generate_asm);
    println!("Value size: {}", std::mem::size_of::<lisp::vm::vp::Value>());
    let Ok(mut prog) = compiler.compile(&list.0, &list.1) else {
        return;
    };

    if generate_asm {
        let listing = prog.get_listing();
        print!("{}", listing);
    }

    let mut vm = Vm::new(use_jit);
    let start = std::time::Instant::now();
    let res = vm.run(&mut prog);
    let duration = start.elapsed();
    if let Some(SExpression::Atom(lit)) = res {
        println!("VM result: {}", lit)
    } else {
        println!("VM result: None");
    }
    println!("Execution time: {:?}", duration);
}

fn start_dap_server() {
    eprintln!("DAP server not implemented yet.");
}
