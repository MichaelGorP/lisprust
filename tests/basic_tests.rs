
use lisp::parser::{SExpression, Atom};

mod common;
use common::{parse_and_exec, parse_and_exec_opt, compare_expr};

#[test]
fn test_binary_operations() {
    let res = parse_and_exec("(+ 1 2 2.5)");
    assert!(compare_expr(res, 5.5));
    let res = parse_and_exec("(- 10 3)");
    assert!(compare_expr(res, 7));
    let res = parse_and_exec("(* 2 2 3)");
    assert!(compare_expr(res, 12));
    let res = parse_and_exec("(/ 8 2)");
    assert!(compare_expr(res, 4));
}

#[test]
fn test_comparisons() {
    let res = parse_and_exec("(= 2 2");
    assert!(compare_expr(res, true));
    let res = parse_and_exec("(< 1 2");
    assert!(compare_expr(res, true));
    let res = parse_and_exec("(> 1 2");
    assert!(compare_expr(res, false));
    let res = parse_and_exec("(>= 2 2");
    assert!(compare_expr(res, true));
    let res = parse_and_exec("(<= 2 2");
    assert!(compare_expr(res, true));

    let res = parse_and_exec("(=)");
    assert!(compare_expr(res, true));

    let res = parse_and_exec("(> 5)");
    assert!(compare_expr(res, true));

    let res = parse_and_exec("(= 2 2 2");
    assert!(compare_expr(res, true));

    let res = parse_and_exec("(< 2 3 4");
    assert!(compare_expr(res, true));

    let res = parse_and_exec("(> 2 3 1");
    assert!(compare_expr(res, false));
}

#[test]
fn test_lambda() {
    let res = parse_and_exec("(define square (lambda (x)
    (* x x)))
    (define five (lambda () 5))
    (+ 2 (square 4) (five))");
    assert!(compare_expr(res, 23));
}

#[test]
fn test_and() {
    let res = parse_and_exec("(and");
    assert!(compare_expr(res, true));
    let res = parse_and_exec("(and 1");
    assert!(compare_expr(res, 1));
    let res = parse_and_exec("(and 1 2");
    assert!(compare_expr(res, 2));
    let res = parse_and_exec("(and (> 2 1) (> 3 2) (> 3 4)");
    assert!(compare_expr(res, false));
}

#[test]
fn test_or() {
    let res = parse_and_exec("(or");
    assert!(compare_expr(res, false));
    let res = parse_and_exec("(or 1");
    assert!(compare_expr(res, 1));
    let res = parse_and_exec("(or false 2");
    assert!(compare_expr(res, 2));
    let res = parse_and_exec("(or false false");
    assert!(compare_expr(res, false));
    let res = parse_and_exec("(or (> 2 1) (> 3 2) (> 3 4)");
    assert!(compare_expr(res, true));
}

#[test]
fn test_not() {
    let res = parse_and_exec("(not 1)");
    assert!(compare_expr(res, false));

    let res = parse_and_exec("(not false)");
    assert!(compare_expr(res, true));
}

#[test]
fn test_if() {
    let res = parse_and_exec("(if 10 20 30");
    assert!(compare_expr(res, 20));
}

#[test]
fn test_let() {
    let res = parse_and_exec("(let ((x 1)) (let ((y 2)) (+ x y)))");
    assert!(compare_expr(res, 3));

    let res = parse_and_exec("(let ((x 1) (y 2)) (+ x y)))");
    assert!(compare_expr(res, 3));
}

#[test]
fn test_compiler_comparisons() {
    let res = parse_and_exec_opt("(> 10 (+ 2 3) (* 2 2)))");
    assert!(matches!(res, Some(SExpression::Atom(Atom::Boolean(true)))));

    let res = parse_and_exec_opt("(< 4 (+ 2 3) (* 2 6)))");
    assert!(matches!(res, Some(SExpression::Atom(Atom::Boolean(true)))));
}

#[test]
fn test_let_star() {
    let res = parse_and_exec("(let* ((x 1) (y (+ x 2))) (+ x y))");
    assert!(compare_expr(res, 4));
}

#[test]
fn test_letrec_factorial() {
    let res = parse_and_exec("(letrec ((fact (lambda (n) (if (= n 0) 1 (* n (fact (- n 1))))))) (fact 5))");
    assert!(compare_expr(res, 120));
}

#[test]
fn test_let_negative_unbound() {
    let res = parse_and_exec_opt("(let ((f (lambda () (g))) (g (lambda () (f)))) (f))");
    assert!(matches!(res, None));
}

#[test]
fn test_letrec_even_odd() {
    let res = parse_and_exec("(letrec ((even (lambda (n) (if (= n 0) true (odd (- n 1))))) (odd (lambda (n) (if (= n 0) false (even (- n 1)))))) (even 4))");
    assert!(compare_expr(res, true));
}

#[test]
fn test_variadic_arithmetic() {
    let res = parse_and_exec("(+ 1 2 3 4)");
    assert!(compare_expr(res, 10));

    let res = parse_and_exec("(* 2 3 4)");
    assert!(compare_expr(res, 24));

    let res = parse_and_exec("(- 10 2 1)");
    assert!(compare_expr(res, 7));

    let res = parse_and_exec("(/ 20 2 2)");
    assert!(compare_expr(res, 5));
}

#[test]
fn test_variadic_comparisons() {
    let res = parse_and_exec("(< 1 2 3 4)");
    assert!(compare_expr(res, true));

    let res = parse_and_exec("(< 1 2 5 4)");
    assert!(compare_expr(res, false));

    let res = parse_and_exec("(= 2 2 2)");
    assert!(compare_expr(res, true));

    let res = parse_and_exec("(= 2 2 3)");
    assert!(compare_expr(res, false));
}

#[test]
fn test_short_circuit_logic() {
    let res = parse_and_exec("(and true true false true)");
    assert!(compare_expr(res, false));

    let res = parse_and_exec("(or false false true false)");
    assert!(compare_expr(res, true));
}
