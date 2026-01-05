use lisp::parser::{SExpression, Atom};

mod common;
use common::{parse_and_exec, compare_expr, parse_compile_and_exec};

#[test]
fn test_list_creation() {
    let sexpr = parse_and_exec("(list 1 2 2.5)");
    match sexpr {
        SExpression::List(l) => {
            assert!(l.len() == 3)
        }
        _ => panic!("Not a list")
    }
}

#[test]
fn test_cons_car_cdr() {
    let res = parse_and_exec("(car (cons 1 2))");
    assert!(compare_expr(res, 1));
    
    let res = parse_and_exec("(cdr (cons 1 2))");
    assert!(compare_expr(res, 2));
}

#[test]
fn test_pair_null() {
    let res = parse_and_exec("(pair? (cons 1 2))");
    assert!(compare_expr(res, true));
    
    let res = parse_and_exec("(pair? 1)");
    assert!(compare_expr(res, false));
    
    let res = parse_and_exec("(null? (list))");
    assert!(compare_expr(res, true));
    
    let res = parse_and_exec("(null? (cons 1 2))");
    assert!(compare_expr(res, false));
}

#[test]
fn test_list_functions() {
    let res = parse_and_exec("(length (list 1 2 3))");
    assert!(compare_expr(res, 3));
    
    let res = parse_and_exec("(reverse (list 1 2 3))");
    // (3 2 1)
    match res {
        SExpression::List(l) => {
            assert_eq!(l.len(), 3);
            assert_eq!(l[0], SExpression::Atom(Atom::Integer(3)));
            assert_eq!(l[1], SExpression::Atom(Atom::Integer(2)));
            assert_eq!(l[2], SExpression::Atom(Atom::Integer(1)));
        },
        _ => panic!("Expected list")
    }
    
    let res = parse_and_exec("(append (list 1 2) (list 3 4))");
    // (1 2 3 4)
    match res {
        SExpression::List(l) => {
            assert_eq!(l.len(), 4);
            assert_eq!(l[0], SExpression::Atom(Atom::Integer(1)));
            assert_eq!(l[3], SExpression::Atom(Atom::Integer(4)));
        },
        _ => panic!("Expected list")
    }
}

#[test]
fn test_list_ref_tail() {
    let res = parse_and_exec("(list-ref (list 10 20 30) 1)");
    assert!(compare_expr(res, 20));
    
    let res = parse_and_exec("(list-tail (list 10 20 30) 1)");
    // (20 30)
    match res {
        SExpression::List(l) => {
            assert_eq!(l.len(), 2);
            assert_eq!(l[0], SExpression::Atom(Atom::Integer(20)));
        },
        _ => panic!("Expected list")
    }
}

#[test]
fn test_cxxr() {
    let res = parse_and_exec("(cadr (list 1 2 3))");
    assert!(compare_expr(res, 2));
    
    let res = parse_and_exec("(caddr (list 1 2 3))");
    assert!(compare_expr(res, 3));
}

#[test]
fn test_mutation() {
    let res = parse_and_exec("((lambda (x) (set-car! x 3) (car x)) (cons 1 2))");
    assert!(compare_expr(res, 3));
    
    let res = parse_and_exec("((lambda (x) (set-cdr! x 3) (cdr x)) (cons 1 2))");
    assert!(compare_expr(res, 3));
}

#[test]
fn test_memq_assoc() {
    let res = parse_and_exec("(memq 2 (list 1 2 3))");
    // (2 3)
    match res {
        SExpression::List(l) => {
            assert_eq!(l.len(), 2);
            assert_eq!(l[0], SExpression::Atom(Atom::Integer(2)));
        },
        _ => panic!("Expected list")
    }
    
    let res = parse_and_exec("(memq 4 (list 1 2 3))");
    assert!(compare_expr(res, false));
    
    let res = parse_and_exec("(assoc 2 (list (list 1 10) (list 2 20)))");
    match res {
        SExpression::List(l) => {
            assert_eq!(l.len(), 2);
            assert_eq!(l[1], SExpression::Atom(Atom::Integer(20)));
        },
        _ => panic!("Expected list")
    }
}

#[test]
fn test_higher_order_functions() {
    // JIT for map/filter/fold is not fully implemented/stable yet
    let res = parse_compile_and_exec("(map (lambda (x) (* x x)) (list 1 2 3 4))", false);
    let expected = parse_compile_and_exec("(list 1 4 9 16)", false);
    assert_eq!(res, expected);

    let res = parse_compile_and_exec("(filter (lambda (x) (> x 2)) (list 1 2 3 4))", false);
    let expected = parse_compile_and_exec("(list 3 4)", false);
    assert_eq!(res, expected);

    let res = parse_compile_and_exec("(fold (lambda (acc x) (+ acc x)) 0 (list 1 2 3 4))", false);
    assert!(compare_expr(res, 10));
}

#[test]
fn test_for_each() {
    let code = "
    (define l (list 0))
    (for-each (lambda (x) (set-car! l (+ (car l) x))) (list 1 2 3 4))
    (car l)
    ";
    let res = parse_compile_and_exec(code, false);
    assert!(compare_expr(res, 10));
}

