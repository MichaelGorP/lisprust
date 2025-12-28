use lisp::parser::{SExpression, Atom, Parser, SourceMap};
use lisp::lexer;
use lisp::vm::compiler::Compiler;
use lisp::vm::list_functions;
use lisp::vm::vm::Vm;

fn compile_and_run(prog: &str) -> Option<SExpression> {
    let mut compiler = Compiler::new(false);
    list_functions::register_functions(&mut compiler);
    
    let tokens = lexer::tokenize(prog).unwrap_or(vec![]);
    let parser = Parser::new();
    let (expr, map, _) = parser.parse(&tokens).unwrap_or((SExpression::Atom(Atom::Boolean(false)), SourceMap::Leaf(0..0), 0));
    let mut prog = compiler.compile(&expr, &map).unwrap();
    let mut vm = Vm::new();
    vm.run(&mut prog)
}

#[test]
fn test_list_creation() {
    let res = compile_and_run("(list 1 2 2.5))");
    assert!(res.is_some());
    let sexpr = res.unwrap();
    match sexpr {
        SExpression::List(l) => {
            assert!(l.len() == 3)
        }
        _ => panic!("Not a list")
    }
}