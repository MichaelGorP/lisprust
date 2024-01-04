use crate::{parser::SExpression, expr_interpreter::Interpreter};

mod lexer;
mod parser;
mod instructions;
mod expr_interpreter;
mod vm;

use crate::vm::compiler::*;

use crate::vm::compiler::Compiler;
use crate::vm::vm::Vm;

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
    let tokens = lexer::tokenize("(define tak (lambda (x y z)
    (if (not (< y x))
      z
    (tak
     (tak (- x 1) y z)
     (tak (- y 1) z x)
     (tak (- z 1) x y)))))

    (tak 30 12 6)").unwrap_or(vec![]);
    println!("{}", tokens.len());

    let parser = parser::Parser::new();
    let list = parser.parse(&tokens).unwrap_or((SExpression::Atom(parser::Atom::Boolean(false)), 0));
    println!("{}", list.1);

    let interpreter = Interpreter::new();
    let res = interpreter.execute(&list.0);
    if let Ok(SExpression::Atom(lit)) = res {
        println!("Result: {}", lit);
    }

    //to get rid of unused warnings for now
    let mut compiler = Compiler::new();
    let Ok(mut prog) = compiler.compile(&list.0) else {
        return;
    };
    let mut vm = Vm::new();
    let res = vm.run(&mut prog);
    if let Some(SExpression::Atom(lit)) = res {
        println!("VM result: {}", lit)
    }
}


#[cfg(test)]
mod test {
    use crate::parser::{SExpression, Atom, Parser};
    use crate::lexer;
    use crate::Interpreter;
    use crate::vm::compiler::Compiler;
    use crate::vm::vm::Vm;

    fn parse_and_eval(prog: &str) -> SExpression {
        let tokens = lexer::tokenize(prog).unwrap_or(vec![]);
        let parser = Parser::new();
        let list = parser.parse(&tokens).unwrap_or((SExpression::Atom(Atom::Boolean(false)), 0));
        let interpreter = Interpreter::new();
        let res = interpreter.execute(&list.0);
        res.expect("Failed to execute")
    }

    fn parse_and_exec(prog: &str) -> SExpression {
        let tokens = lexer::tokenize(prog).unwrap_or(vec![]);
        let parser = Parser::new();
        let list = parser.parse(&tokens).unwrap_or((SExpression::Atom(Atom::Boolean(false)), 0));
        let interpreter = Interpreter::new();
        let res = interpreter.execute(&list.0).expect("Failed to execute");

        let mut compiler = Compiler::new();
        let mut prog = compiler.compile(&list.0).unwrap();
        let mut vm = Vm::new();
        let res2 = vm.run(&mut prog).expect("Failed to execute");
        assert!(res == res2);
        res
    }

    fn parse_might_fail(prog: &str) -> Option<SExpression> {
        let tokens = lexer::tokenize(prog).unwrap_or(vec![]);
        let parser = Parser::new();
        let list = parser.parse(&tokens).unwrap_or((SExpression::Atom(Atom::Boolean(false)), 0));
        let interpreter = Interpreter::new();
        let res = interpreter.execute(&list.0);
        res.ok()
    }

    fn compile_and_run(prog: &str) -> Option<SExpression> {
        let mut compiler = Compiler::new();
        let tokens = lexer::tokenize(prog).unwrap_or(vec![]);
        let parser = Parser::new();
        let list = parser.parse(&tokens).unwrap_or((SExpression::Atom(Atom::Boolean(false)), 0));
        let mut prog = compiler.compile(&list.0).unwrap();
        let mut vm = Vm::new();
        vm.run(&mut prog)
    }

    #[test]
    fn test_binary_operations() {
        let res = parse_and_exec("(+ 1 2 2.5)");
        assert!(matches!(res, SExpression::Atom(Atom::Float(5.5))));
        let res = parse_and_exec("(- 10 3)");
        assert!(matches!(res, SExpression::Atom(Atom::Integer(7))));
        let res = parse_and_exec("(* 2 2 3)");
        assert!(matches!(res, SExpression::Atom(Atom::Integer(12))));
        let res = parse_and_exec("(/ 8 2)");
        assert!(matches!(res, SExpression::Atom(Atom::Integer(4))));
    }

    #[test]
    fn test_comparisons() {
        let res = parse_and_exec("(= 2 2");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));
        let res = parse_and_exec("(< 1 2");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));
        let res = parse_and_exec("(> 1 2");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(false))));
        let res = parse_and_exec("(>= 2 2");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));
        let res = parse_and_exec("(<= 2 2");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));

        let res = parse_and_exec("(=)");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));

        let res = parse_and_exec("(> 5)");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));

        let res = parse_might_fail("> \"a\")");
        assert!(matches!(res, None));

        let res = parse_and_exec("(= 2 2 2");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));

        let res = parse_and_exec("(< 2 3 4");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));

        let res = parse_and_exec("(> 2 3 1");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(false))));
    }

    #[test]
    fn test_lambda() {
        let res = parse_and_eval("(define square (lambda (x)
        (* x x)))
        (define five (lambda () 5))
        (+ 2 (square 4) (five))");
        assert!(matches!(res, SExpression::Atom(Atom::Integer(23))));
    }

    #[test]
    fn test_and() {
        let res = parse_and_exec("(and");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));
        let res = parse_and_exec("(and 1");
        assert!(matches!(res, SExpression::Atom(Atom::Integer(1))));
        let res = parse_and_exec("(and 1 2");
        assert!(matches!(res, SExpression::Atom(Atom::Integer(2))));
        let res = parse_and_exec("(and (> 2 1) (> 3 2) (> 3 4)");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(false))));
    }

    #[test]
    fn test_or() {
        let res = parse_and_exec("(or");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(false))));
        let res = parse_and_exec("(or 1");
        assert!(matches!(res, SExpression::Atom(Atom::Integer(1))));
        let res = parse_and_exec("(or false 2");
        assert!(matches!(res, SExpression::Atom(Atom::Integer(2))));
        let res = parse_and_exec("(or false false");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(false))));
        let res = parse_and_exec("(or (> 2 1) (> 3 2) (> 3 4)");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));
    }

    #[test]
    fn test_not() {
        let res = parse_and_exec("(not 1)");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(false))));

        let res = parse_and_exec("(not false)");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));
    }

    #[test]
    fn test_if() {
        let res = parse_and_exec("(if 10 20 30");
        assert!(matches!(res, SExpression::Atom(Atom::Integer(20))));
    }

    #[test]
    fn test_compiler_comparisons() {
        let res = compile_and_run("(> 10 (+ 2 3) (* 2 2)))");
        assert!(matches!(res, Some(SExpression::Atom(Atom::Boolean(true)))));

        let res = compile_and_run("(< 4 (+ 2 3) (* 2 6)))");
        assert!(matches!(res, Some(SExpression::Atom(Atom::Boolean(true)))));
    }
}