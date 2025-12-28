use lisp::parser::{SExpression, Atom, Parser, SourceMap};
use lisp::lexer;
use lisp::vm::compiler::Compiler;
use lisp::vm::math_functions;
use lisp::vm::vm::Vm;

fn compare_expr<T>(expr: SExpression, value: T) -> bool where T: Into<Atom> {
    expr == <SExpression>::from(value)
}

fn parse_and_exec(prog: &str) -> SExpression {
    let tokens = lexer::tokenize(prog).unwrap_or(vec![]);
    let parser = Parser::new();
    let (expr, map, _) = parser.parse(&tokens).unwrap_or((SExpression::Atom(Atom::Boolean(false)), SourceMap::Leaf(0..0), 0));

    let mut compiler = Compiler::new(false);
    math_functions::register_functions(&mut compiler);
    let mut prog = compiler.compile(&expr, &map).unwrap();
    let mut vm = Vm::new();
    let res = match vm.run(&mut prog) {
        Some(r) => r,
        None => panic!("VM failed to execute")
    };
    res
}

#[test]
fn test_closure_as_argument() {
    // (define apply (lambda (f x) (f x)))
    // (let ((y 10)) (apply (lambda (z) (+ z y)) 5))
    // Expected: 15
    let prog = "
    (let ((apply (lambda (f x) (f x))))
        (let ((y 10)) 
            (apply (lambda (z) (+ z y)) 5)))
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 15));
}

#[test]
fn test_closure_returned() {
    // (define make-adder (lambda (x) (lambda (y) (+ x y))))
    // (let ((add5 (make-adder 5))) (add5 10))
    // Expected: 15
    let prog = "
    (let ((make-adder (lambda (x) (lambda (y) (+ x y)))))
        (let ((add5 (make-adder 5)))
            (add5 10)))
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 15));
}

#[test]
fn test_closure_shadowing() {
    // (let ((x 10))
    //   (let ((f (lambda (y) (+ x y))))
    //     (let ((x 20))
    //        (f 5))))
    // Expected: 15 (inner x=20 should not affect closure capturing outer x=10)
    let prog = "
    (let ((x 10))
      (let ((f (lambda (y) (+ x y))))
        (let ((x 20))
           (f 5))))
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 15));
}

#[test]
fn test_deep_nesting() {
    // (let ((x 1))
    //   (let ((y 2))
    //     (let ((z 3))
    //       ((lambda (w) (+ x (+ y (+ z w)))) 4))))
    // Expected: 10
    let prog = "
    (let ((x 1))
      (let ((y 2))
        (let ((z 3))
          ((lambda (w) (+ x (+ y (+ z w)))) 4))))
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 10));
}

#[test]
fn test_multiple_closures_sharing_scope() {
    // (let ((x 10))
    //    (let ((inc (lambda (y) (+ y x)))
    //          (dec (lambda (y) (- y x))))
    //       (+ (inc 5) (dec 5))))
    // Expected: 10
    let prog = "
    (let ((x 10))
       (let ((inc (lambda (y) (+ y x)))
             (dec (lambda (y) (- y x))))
          (+ (inc 5) (dec 5))))
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 10));
}

#[test]
fn test_let_star_closure_capture() {
    // (let* ((x 10) (f (lambda (y) (+ x y))) (z (f 5))) z)
    // Expected: 15
    let prog = "
    (let* ((x 10)
           (f (lambda (y) (+ x y)))
           (z (f 5)))
      z)
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 15));
}
