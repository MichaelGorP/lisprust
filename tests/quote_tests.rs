mod common;
use common::{parse_and_exec, compare_expr};
use lisp::parser::SExpression;

#[test]
fn test_quote_symbol() {
    let res = parse_and_exec("'x");
    // Should be a symbol "x"
    if let SExpression::Symbol(s) = res {
        assert_eq!(s, "x");
    } else {
        panic!("Expected symbol, got {:?}", res);
    }
}

#[test]
fn test_quote_list() {
    let res = parse_and_exec("'(1 2 3)");
    // Should be a list (1 2 3)
    if let SExpression::List(l) = res {
        assert_eq!(l.len(), 3);
        assert!(compare_expr(l[0].clone(), 1));
        assert!(compare_expr(l[1].clone(), 2));
        assert!(compare_expr(l[2].clone(), 3));
    } else {
        panic!("Expected list, got {:?}", res);
    }
}

#[test]
fn test_quote_nested_list() {
    let res = parse_and_exec("'(1 (2 3))");
    // Should be (1 (2 3))
    if let SExpression::List(l) = res {
        assert_eq!(l.len(), 2);
        assert!(compare_expr(l[0].clone(), 1));
        if let SExpression::List(l2) = &l[1] {
            assert_eq!(l2.len(), 2);
            assert!(compare_expr(l2[0].clone(), 2));
            assert!(compare_expr(l2[1].clone(), 3));
        } else {
            panic!("Expected nested list");
        }
    } else {
        panic!("Expected list, got {:?}", res);
    }
}

#[test]
fn test_quote_empty_list() {
    let res = parse_and_exec("'()");
    if let SExpression::List(l) = res {
        assert!(l.is_empty());
    } else {
        panic!("Expected empty list, got {:?}", res);
    }
}

#[test]
fn test_quote_full_form() {
    let res = parse_and_exec("(quote x)");
    if let SExpression::Symbol(s) = res {
        assert_eq!(s, "x");
    } else {
        panic!("Expected symbol, got {:?}", res);
    }
}

#[test]
fn test_quote_complex_structure() {
    let res = parse_and_exec("'(define x 10)");
    if let SExpression::List(l) = res {
        assert_eq!(l.len(), 3);
        if let SExpression::Symbol(s) = &l[0] {
            assert_eq!(s, "define");
        } else {
            panic!("Expected symbol define");
        }
        if let SExpression::Symbol(s) = &l[1] {
            assert_eq!(s, "x");
        } else {
            panic!("Expected symbol x");
        }
        assert!(compare_expr(l[2].clone(), 10));
    } else {
        panic!("Expected list, got {:?}", res);
    }
}

#[test]
fn test_quote_lambda() {
    let res = parse_and_exec("(quote (lambda (x) x))");
    if let SExpression::List(l) = res {
        assert_eq!(l.len(), 3);
        if let SExpression::Symbol(s) = &l[0] {
            assert_eq!(s, "lambda");
        } else {
            panic!("Expected symbol lambda");
        }
        // Check params list (x)
        if let SExpression::List(params) = &l[1] {
            assert_eq!(params.len(), 1);
            if let SExpression::Symbol(p) = &params[0] {
                assert_eq!(p, "x");
            } else {
                panic!("Expected symbol x in params");
            }
        } else {
            panic!("Expected params list");
        }
        // Check body x
        if let SExpression::Symbol(b) = &l[2] {
            assert_eq!(b, "x");
        } else {
            panic!("Expected symbol x in body");
        }
    } else {
        panic!("Expected list, got {:?}", res);
    }
}

