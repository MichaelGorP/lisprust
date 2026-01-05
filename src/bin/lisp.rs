use std::env;
use std::fs;

use lisp::parser::SExpression;

use lisp::vm::compiler::Compiler;
use lisp::vm::vm::Vm;
use lisp::lexer;
use lisp::parser;
use lisp::vm::list_functions;
use lisp::vm::math_functions;
use lisp::vm::misc_functions;

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut generate_asm = false;
    let mut debug_mode = false;
    let mut use_jit = true;
    let mut profile = false;
    let mut filename = None;
    let mut repetitions = 1;

    let mut args_iter = args.iter().skip(1);
    while let Some(a) = args_iter.next() {
        if a == "--asm" {
            generate_asm = true;
        } else if a == "--debug" {
            debug_mode = true;
        } else if a == "--no-jit" {
            use_jit = false;
        } else if a == "--profile" {
            profile = true;
        } else if a == "--repeat" {
            if let Some(n) = args_iter.next() {
                repetitions = n.parse().unwrap_or(1);
            }
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
    list_functions::register_functions(&mut compiler);
    math_functions::register_functions(&mut compiler);
    misc_functions::register_functions(&mut compiler);
    let Ok(mut prog) = compiler.compile(&list.0, &list.1) else {
        if let Err(e) = compiler.compile(&list.0, &list.1) {
            eprintln!("Compilation failed: {}", e);
        }
        return;
    };

    if generate_asm {
        let listing = prog.get_listing();
        print!("{}", listing);
    }

    let mut vm = Vm::new(use_jit);
    
    let profiler = if profile {
        Some(lisp::vm::profiler::Profiler::new(vm.jit.function_map.clone()))
    } else {
        None
    };

    let start = std::time::Instant::now();
    let mut res = None;
    for _ in 0..repetitions {
        prog.cursor.set_position(0);
        res = vm.run(&mut prog);
    }
    let duration = start.elapsed();
    
    if let Some(mut p) = profiler {
        p.stop();
    }

    if let Some(res) = res {
        if let Some(sexpr) = lisp::vm::vm::value_to_sexpr(&res, &vm.heap) {
            println!("VM result: {}", sexpr);
        } else {
            println!("VM result: <internal value>");
        }
    } else {
        println!("VM result: None");
    }
    println!("Execution time: {:?}", duration);
}

fn start_dap_server() {
    eprintln!("DAP server not implemented yet.");
}
