mod common;
use common::{parse_and_exec, compare_expr};

#[test]
fn test_cyclic_list() {
    let code = "
    (define x (list 1 2 3))
    (set-cdr! (cddr x) x)
    (car (cdr (cdr (cdr x))))
    ";
    
    let res = parse_and_exec(code);
    assert!(compare_expr(res, 1));
}
