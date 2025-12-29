use lisp::parser::{SExpression, Atom};

mod common;
use common::{parse_and_exec, parse_compile_and_exec};

fn compare_expr<T>(expr: SExpression, value: T) -> bool where T: Into<Atom> {
    expr == <SExpression>::from(value)
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
    let res = parse_compile_and_exec(prog, true);
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
