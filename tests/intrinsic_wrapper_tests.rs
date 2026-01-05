mod common;
use common::{compare_expr, parse_compile_and_exec};

#[test]
fn test_map_intrinsics() {
    // Test map with car
    let code = "(map car (list (list 1 2) (list 3 4)))";
    let res = parse_compile_and_exec(code, false);
    let expected = parse_compile_and_exec("(list 1 3)", false);
    assert_eq!(res, expected);

    // Test map with cdr
    let code = "(map cdr (list (list 1 2) (list 3 4)))";
    let res = parse_compile_and_exec(code, false);
    let expected = parse_compile_and_exec("(list (list 2) (list 4))", false);
    assert_eq!(res, expected);

    // Test map with pair?
    let code = "(map pair? (list (list 1 2) 3 (list 4 5)))";
    let res = parse_compile_and_exec(code, false);
    let expected = parse_compile_and_exec("(list #t #f #t)", false);
    assert_eq!(res, expected);

    // Test map with null?
    let code = "(map null? (list (list) (list 1) (list)))";
    let res = parse_compile_and_exec(code, false);
    let expected = parse_compile_and_exec("(list #t #f #t)", false);
    assert_eq!(res, expected);
}

#[test]
fn test_filter_intrinsics() {
    // Test filter with pair?
    let code = "(filter pair? (list (list 1 2) 3 (list 4 5) 6))";
    let res = parse_compile_and_exec(code, false);
    let expected = parse_compile_and_exec("(list (list 1 2) (list 4 5))", false);
    assert_eq!(res, expected);

    // Test filter with null?
    let code = "(filter null? (list (list) (list 1) (list) 2))";
    let res = parse_compile_and_exec(code, false);
    let expected = parse_compile_and_exec("(list (list) (list))", false);
    assert_eq!(res, expected);
}

#[test]
fn test_fold_intrinsics() {
    // Test fold with cons (reverse list)
    let code = "(fold cons (list) (list 1 2 3))";
    let res = parse_compile_and_exec(code, false);
    let expected = parse_compile_and_exec("(list 3 2 1)", false);
    assert_eq!(res, expected);
}

#[test]
fn test_intrinsic_as_argument() {
    // Define a function that takes a function and applies it
    let code = "
    (define (apply-func f x) (f x))
    (apply-func car (list 10 20))
    ";
    let res = parse_compile_and_exec(code, false);
    assert!(compare_expr(res, 10));

    let code = "
    (define (apply-func f x) (f x))
    (apply-func cdr (list 10 20))
    ";
    let res = parse_compile_and_exec(code, false);
    let expected = parse_compile_and_exec("(list 20)", false);
    assert_eq!(res, expected);
    
    let code = "
    (define (apply-func-2 f x y) (f x y))
    (apply-func-2 cons 1 2)
    ";
    let res = parse_compile_and_exec(code, false);
    let expected = parse_compile_and_exec("(cons 1 2)", false);
    assert_eq!(res, expected);
}

#[test]
fn test_intrinsic_in_let() {
    let code = "
    (let ((f car))
      (f (list 1 2)))
    ";
    let res = parse_compile_and_exec(code, false);
    assert!(compare_expr(res, 1));
}

#[test]
fn test_for_each_intrinsics() {
    let code = "
    (for-each (lambda (x) x) (list 1 2 3))
    ";
    let res = parse_compile_and_exec(code, false);
    let expected = parse_compile_and_exec("(list)", false);
    assert_eq!(res, expected);
}
