use std::env;

use lisp::parser::SExpression;

use lisp::vm::compiler::Compiler;
use lisp::vm::vm::Vm;
use lisp::lexer;
use lisp::parser;

fn main() {
    let tokens = lexer::tokenize("(define tak (lambda (x y z)
    (if (not (< y x))
      z
    (tak
     (tak (- x 1) y z)
     (tak (- y 1) z x)
     (tak (- z 1) x y)))))

    (tak 30 12 6)").unwrap_or(vec![]);

    let parser = parser::Parser::new();
    let list = parser.parse(&tokens).unwrap_or((SExpression::Atom(parser::Atom::Boolean(false)), 0));

    /*
    let interpreter = Interpreter::new();
    let res = interpreter.execute(&list.0);
    if let Ok(SExpression::Atom(lit)) = res {
        println!("Result: {}", lit);
    }
    */

    let args: Vec<String> = env::args().collect();
    let mut generate_asm = false;
    for a in args.iter().skip(1) {
        if a == "--asm" {
            generate_asm = true;
        }
    }

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
