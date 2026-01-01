use lisp::parser::{SExpression, Atom};

mod common;
use common::{parse_and_exec, parse_compile_and_exec, compare_expr};

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

#[test]
fn test_recursion_shadowing() {
    // (define f (lambda (x)
    //   (let ((f (lambda (y) (* y 2))))
    //     (f x))))
    // (f 10)
    // Expected: 20
    let prog = "
    (define f (lambda (x)
      (let ((f (lambda (y) (* y 2))))
        (f x))))
    (f 10)
    ";
    let res = parse_compile_and_exec(prog, true);
    assert!(compare_expr(res, 20));
}

#[test]
fn test_shadowing_param_and_inner_let() {
    // Case 1: Parameter shadows global name
    // (define g (lambda (g) (g 5)))
    // (g (lambda (x) (* x 2))) -> 10
    let prog1 = "
    (define g (lambda (g) (g 5)))
    (g (lambda (x) (* x 2)))
    ";
    let res1 = parse_compile_and_exec(prog1, true);
    assert!(compare_expr(res1, 10));

    // Case 2: Let binding shadows recursive name (The user's specific request)
    // (define f (lambda (n)
    //   (if (= n 0) 0
    //       (let ((f (lambda (x) (+ x 1))))
    //         (f n)))))
    // (f 5) -> 6. 
    // If shadowing failed, it would recurse infinitely or crash.
    let prog2 = "
    (define f (lambda (n)
      (if (= n 0) 0
          (let ((f (lambda (x) (+ x 1))))
            (f n)))))
    (f 5)
    ";
    let res2 = parse_compile_and_exec(prog2, true);
    assert!(compare_expr(res2, 6));

    // Case 3: Nested letrec
    // (letrec ((f (lambda (n)
    //               (letrec ((f (lambda (m) (* m 2))))
    //                  (f n)))))
    //   (f 5))
    // Expected: 10
    let prog3 = "
    (letrec ((f (lambda (n)
                  (letrec ((f (lambda (m) (* m 2))))
                     (f n)))))
      (f 5))
    ";
    let res3 = parse_compile_and_exec(prog3, true);
    assert!(compare_expr(res3, 10));
}
