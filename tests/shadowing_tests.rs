
mod common;
use common::{parse_and_exec, compare_expr};

#[test]
fn test_let_shadowing() {
    let prog = "
    (let ((x 1))
      (let ((x 2))
        x))
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 2));
}

#[test]
fn test_let_shadowing_outer_access() {
    let prog = "
    (let ((x 1))
      (let ((y x))
        (let ((x 2))
          y)))
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 1));
}

#[test]
fn test_let_star_shadowing() {
    let prog = "
    (let* ((x 1) (x 2))
      x)
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 2));
}

#[test]
fn test_let_star_shadowing_reference() {
    let prog = "
    (let* ((x 1) (y x) (x 2))
      y)
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 1));
}

#[test]
fn test_lambda_shadowing() {
    let prog = "
    ((lambda (x)
       ((lambda (x) x) 2))
     1)
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 2));
}

#[test]
fn test_internal_define_shadowing() {
    let prog = "
    (define f (lambda (x)
      (define x 2)
      x))
    (f 1)
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 2));
}

#[test]
fn test_mixed_shadowing() {
    let prog = "
    (let ((x 1))
      (define f (lambda (x)
        (let ((x 3))
          x)))
      (f 2))
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 3));
}

#[test]
fn test_recursion_shadowing_param() {
    // Ensure that a parameter shadowing the function name doesn't break recursion
    // (This was the original bug)
    let prog = "
    (define g (lambda (g) g))
    (g 10)
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 10));
}

#[test]
fn test_recursion_shadowing_let() {
    let prog = "
    (define f (lambda (n)
      (let ((f 10))
        f)))
    (f 5)
    ";
    let res = parse_and_exec(prog);
    assert!(compare_expr(res, 10));
}

#[test]
    fn test_internal_define_mutual_recursion() {
        // Scheme semantics require internal defines to be mutually recursive (letrec).
        // (define (f n)
        //   (define (even? n) (if (= n 0) #t (odd? (- n 1))))
        //   (define (odd? n) (if (= n 0) #f (even? (- n 1))))
        //   (even? n))
        let prog = "
        (define f (lambda (n)
          (define even? (lambda (n) (if (= n 0) #t (odd? (- n 1)))))
          (define odd? (lambda (n) (if (= n 0) #f (even? (- n 1)))))
          (even? n)))
        (f 4)
        ";
        // If this fails, it means we have let* semantics (sequential), not letrec.
        let res = parse_and_exec(prog);
        assert!(compare_expr(res, true));
    }