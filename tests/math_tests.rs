use lisp::parser::{SExpression, Atom};

mod common;
use common::{parse_and_exec, compare_expr};

#[test]
fn test_trig() {
    // sin
    let res = parse_and_exec("(sin 0)");
    assert!(compare_expr(res, 0.0));
    
    // cos
    let res = parse_and_exec("(cos 0)");
    assert!(compare_expr(res, 1.0));

    // tan
    let res = parse_and_exec("(tan 0)");
    assert!(compare_expr(res, 0.0));
}

#[test]
fn test_exp_log() {
    let res = parse_and_exec("(exp 0)");
    assert!(compare_expr(res, 1.0));

    let res = parse_and_exec("(log 1)");
    assert!(compare_expr(res, 0.0));
    
    let res = parse_and_exec("(expt 2 3)");
    assert!(compare_expr(res, 8.0));
}

#[test]
fn test_rounding() {
    let res = parse_and_exec("(floor 1.5)");
    assert!(compare_expr(res, 1.0));
    
    let res = parse_and_exec("(ceiling 1.5)");
    assert!(compare_expr(res, 2.0));
    
    let res = parse_and_exec("(truncate 1.5)");
    assert!(compare_expr(res, 1.0));
    
    let res = parse_and_exec("(round 1.5)");
    assert!(compare_expr(res, 2.0));
}

#[test]
fn test_integer_math() {
    let res = parse_and_exec("(quotient 10 3)");
    assert!(compare_expr(res, 3));
    
    let res = parse_and_exec("(remainder 10 3)");
    assert!(compare_expr(res, 1));
    
    let res = parse_and_exec("(modulo 10 3)");
    assert!(compare_expr(res, 1));
    
    let res = parse_and_exec("(gcd 12 15)");
    assert!(compare_expr(res, 3));
    
    let res = parse_and_exec("(lcm 12 15)");
    assert!(compare_expr(res, 60));
}

#[test]
fn test_abs() {
    let res = parse_and_exec("(abs -5)");
    assert!(compare_expr(res, 5));
    
    let res = parse_and_exec("(abs -5.5)");
    assert!(compare_expr(res, 5.5));
}

#[test]
fn test_min_max() {
    let res = parse_and_exec("(max 1 2 3)");
    assert!(compare_expr(res, 3));
    
    let res = parse_and_exec("(max 1 2.5 3)");
    assert!(compare_expr(res, 3)); // 3 > 2.5
    
    let res = parse_and_exec("(min 1 2 3)");
    assert!(compare_expr(res, 1));
    
    let res = parse_and_exec("(min 1 0.5 3)");
    assert!(compare_expr(res, 0.5));
}
