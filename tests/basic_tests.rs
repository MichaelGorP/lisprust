
use lisp::parser::{SExpression, Atom, Parser};
use lisp::lexer;
use lisp::expr_interpreter::Interpreter;
use lisp::vm::compiler::Compiler;
use lisp::vm::vm::Vm;

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

    let mut compiler = Compiler::new(false);
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
    let mut compiler = Compiler::new(false);
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
    let expected: SExpression = 5.5.into();
    assert!(matches!(res, expected));
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
    let res = parse_and_exec("(define square (lambda (x)
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
