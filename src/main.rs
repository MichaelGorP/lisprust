use crate::{parser::SExpression, expr_interpreter::Interpreter};

mod lexer;
mod parser;
mod instructions;
mod expr_interpreter;

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
    let tokens = lexer::tokenize("(define tak (lambda (x y z)
    (if (not (< y x))
      z
    (tak
     (tak (- x 1) y z)
     (tak (- y 1) z x)
     (tak (- z 1) x y)))))

    (tak 30 12 6)").unwrap_or(vec![]);
    println!("{}", tokens.len());

    let parser = parser::Parser::new();
    let list = parser.parse(&tokens).unwrap_or((SExpression::Atom(parser::Atom::Boolean(false)), 0));
    println!("{}", list.1);

    let interpreter = Interpreter::new();
    let res = interpreter.execute(&list.0);
    if let Ok(SExpression::Atom(lit)) = res {
        println!("Result: {}", lit);
    }
}


#[cfg(test)]
mod test {
    use crate::parser::{SExpression, Atom, Parser};
    use crate::lexer;
    use crate::Interpreter;

    fn parse_and_eval(prog: &str) -> SExpression {
        let tokens = lexer::tokenize(prog).unwrap_or(vec![]);
        let parser = Parser::new();
        let list = parser.parse(&tokens).unwrap_or((SExpression::Atom(Atom::Boolean(false)), 0));
        let interpreter = Interpreter::new();
        let res = interpreter.execute(&list.0);
        res.expect("Failed to execute")
    }

    fn parse_might_fail(prog: &str) -> Option<SExpression> {
        let tokens = lexer::tokenize(prog).unwrap_or(vec![]);
        let parser = Parser::new();
        let list = parser.parse(&tokens).unwrap_or((SExpression::Atom(Atom::Boolean(false)), 0));
        let interpreter = Interpreter::new();
        let res = interpreter.execute(&list.0);
        res.ok()
    }

    #[test]
    fn test_binary_operations() {
        let res = parse_and_eval("(+ 1 2 2.5)");
        assert!(matches!(res, SExpression::Atom(Atom::Float(5.5))));
        let res = parse_and_eval("(- 10 3)");
        assert!(matches!(res, SExpression::Atom(Atom::Integer(7))));
        let res = parse_and_eval("(* 2 2 3)");
        assert!(matches!(res, SExpression::Atom(Atom::Integer(12))));
        let res = parse_and_eval("(/ 8 2)");
        assert!(matches!(res, SExpression::Atom(Atom::Integer(4))));
    }

    #[test]
    fn test_comparisons() {
        let res = parse_and_eval("(= 2 2");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));
        let res = parse_and_eval("(< 1 2");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));
        let res = parse_and_eval("(> 1 2");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(false))));
        let res = parse_and_eval("(>= 2 2");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));
        let res = parse_and_eval("(<= 2 2");
        assert!(matches!(res, SExpression::Atom(Atom::Boolean(true))));

        //test error case
        let res = parse_might_fail("(= 2 2 2");
        assert!(matches!(res, None));
    }

    #[test]
    fn test_lambda() {
        let res = parse_and_eval("(define square (lambda (x)
        (* x x)))
        (define five (lambda () 5))
        (+ 2 (square 4) (five))");
        assert!(matches!(res, SExpression::Atom(Atom::Integer(23))));
    }
}