use lisp::parser::{SExpression, Atom, Parser, SourceMap};
use lisp::lexer;
use lisp::vm::compiler::Compiler;
use lisp::vm::math_functions;
use lisp::vm::list_functions;
use lisp::vm::vm::Vm;

#[allow(dead_code)]
pub fn parse_and_exec(prog: &str) -> SExpression {
    parse_compile_and_exec(prog, true)
}

#[allow(dead_code)]
pub fn parse_and_exec_opt(prog: &str) -> Option<SExpression> {
    let tokens = lexer::tokenize(prog).unwrap_or(vec![]);
    let parser = Parser::new();
    let (expr, map, _) = parser.parse(&tokens).unwrap_or((SExpression::Atom(Atom::Boolean(false)), SourceMap::Leaf(0..0), 0));

    let mut compiler = Compiler::new(false);
    math_functions::register_functions(&mut compiler);
    list_functions::register_functions(&mut compiler);
    let mut prog = compiler.compile(&expr, &map).unwrap();
    let mut vm = Vm::new(false);
    let res = vm.run(&mut prog);
    res.and_then(|v| lisp::vm::vm::value_to_sexpr(&v, &vm.heap))
}

pub fn parse_compile_and_exec(prog: &str, use_jit: bool) -> SExpression {
    let tokens = lexer::tokenize(prog).unwrap_or(vec![]);
    let parser = Parser::new();
    let (expr, map, _) = parser.parse(&tokens).unwrap_or((SExpression::Atom(Atom::Boolean(false)), SourceMap::Leaf(0..0), 0));

    let mut compiler = Compiler::new(false);
    math_functions::register_functions(&mut compiler);
    list_functions::register_functions(&mut compiler);
    let mut prog = compiler.compile(&expr, &map).unwrap();
    let mut prog_copy = prog.clone();
    let mut vm = Vm::new(false);
    let val = match vm.run(&mut prog) {
        Some(r) => r,
        None => panic!("VM failed to execute")
    };
    let res = lisp::vm::vm::value_to_sexpr(&val, &vm.heap).unwrap();

    if use_jit {
        let mut vm_jit = Vm::new(true);
        let val_jit = match vm_jit.run(&mut prog_copy) {
            Some(r) => r,
            None => panic!("VM failed to execute")
        };
        let res_jit = lisp::vm::vm::value_to_sexpr(&val_jit, &vm_jit.heap).unwrap();
        assert_eq!(res, res_jit);
    }
    
    res
}

pub fn compare_expr<T>(expr: SExpression, value: T) -> bool where T: Into<Atom> {
    expr == <SExpression>::from(value)
}
