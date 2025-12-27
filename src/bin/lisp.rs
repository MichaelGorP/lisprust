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
    let mut filename = None;

    for a in args.iter().skip(1) {
        if a == "--asm" {
            generate_asm = true;
        } else {
            filename = Some(a);
        }
    }

    let source = if let Some(f) = filename {
        fs::read_to_string(f).expect("Could not read file")
    } else {
        eprintln!("Usage: {} <filename> [--asm]", args[0]);
        return;
    };

    let tokens = lexer::tokenize(&source).unwrap_or(vec![]);

    let parser = parser::Parser::new();
    let list = parser.parse(&tokens).unwrap_or((SExpression::Atom(parser::Atom::Boolean(false)), 0));

    let mut compiler = Compiler::new(generate_asm);
    let Ok(mut prog) = compiler.compile(&list.0) else {
        return;
    };

    if generate_asm {
        let listing = prog.get_listing();
        print!("{}", listing);
    }

    let mut vm = Vm::new();
    let res = vm.run(&mut prog);
    if let Some(SExpression::Atom(lit)) = res {
        println!("VM result: {}", lit)
    }
}
