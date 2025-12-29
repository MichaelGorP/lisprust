use lisp::parser::{SExpression, Atom, Parser, SourceMap};
use lisp::lexer;
use lisp::vm::compiler::Compiler;
use lisp::vm::math_functions;
use lisp::vm::vm::{Vm, Debugger};
use lisp::vm::vp::VirtualProgram;

struct StepCounter {
    steps: usize,
}

impl Debugger for StepCounter {
    fn on_step(&mut self, _vm: &Vm, _prog: &VirtualProgram) {
        self.steps += 1;
    }
}

#[test]
fn test_debugger_steps() {
    let prog_str = "(+ 1 2)";
    let tokens = lexer::tokenize(prog_str).unwrap_or(vec![]);
    let parser = Parser::new();
    let (expr, map, _) = parser.parse(&tokens).unwrap_or((SExpression::Atom(Atom::Boolean(false)), SourceMap::Leaf(0..0), 0));
    
    let mut compiler = Compiler::new(false);
    math_functions::register_functions(&mut compiler);
    let mut prog = compiler.compile(&expr, &map).unwrap();
    
    let mut vm = Vm::new(false);
    let mut debugger = StepCounter { steps: 0 };
    
    vm.run_debug(&mut prog, Some(&mut debugger));
    
    assert!(debugger.steps > 0);
    println!("Executed {} steps", debugger.steps);
}

#[test]
fn test_debugger_source_mapping() {
    let prog_str = "(+ 1 2)";
    let tokens = lexer::tokenize(prog_str).unwrap_or(vec![]);
    let parser = Parser::new();
    let (expr, map, _) = parser.parse(&tokens).unwrap_or((SExpression::Atom(Atom::Boolean(false)), SourceMap::Leaf(0..0), 0));
    
    let mut compiler = Compiler::new(false);
    math_functions::register_functions(&mut compiler);
    let mut prog = compiler.compile(&expr, &map).unwrap();
    
    struct SourceChecker {
        found_spans: Vec<std::ops::Range<usize>>,
    }
    
    impl Debugger for SourceChecker {
        fn on_step(&mut self, _vm: &Vm, prog: &VirtualProgram) {
            let addr = prog.current_address() as usize;
            
            let mut best_span = None;
            for (map_addr, span) in &prog.source_map {
                if *map_addr <= addr {
                    best_span = Some(span.clone());
                }
            }
            
            if let Some(span) = best_span {
                self.found_spans.push(span);
            }
        }
    }
    
    let mut vm = Vm::new(false);
    let mut debugger = SourceChecker { found_spans: Vec::new() };
    
    vm.run_debug(&mut prog, Some(&mut debugger));
    
    assert!(!debugger.found_spans.is_empty());
    println!("Found spans: {:?}", debugger.found_spans);
}
