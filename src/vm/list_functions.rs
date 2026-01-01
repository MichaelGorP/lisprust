use std::rc::Rc;
use std::cell::RefCell;
use super::{compiler::Compiler, vp::Value, vp::Pair, vp::HeapValue};

pub fn register_functions(compiler: &mut Compiler) {
    compiler.register_function("car", car);
    compiler.register_function("cdr", cdr);
    compiler.register_function("cons", cons);
    compiler.register_function("pair?", is_pair);
    compiler.register_function("null?", is_null);
    compiler.register_function("list", list);
    // compiler.register_function("map", map); // Requires VM callback
    compiler.register_function("append", append);
    compiler.register_function("reverse", reverse);
    compiler.register_function("member", member);
    compiler.register_function("memq", memq);
    compiler.register_function("assoc", assoc);
    compiler.register_function("assq", assq);
    compiler.register_function("cadr", cadr);
    compiler.register_function("caddr", caddr);
    compiler.register_function("cddr", cddr);
    compiler.register_function("set-car!", set_car);
    compiler.register_function("set-cdr!", set_cdr);
    compiler.register_function("length", length);
    // compiler.register_function("for-each", for_each); // Requires VM callback
    compiler.register_function("list-ref", list_ref);
    compiler.register_function("list-tail", list_tail);
    // compiler.register_function("filter", filter); // Requires VM callback
    // compiler.register_function("fold", fold); // Requires VM callback
}

fn cons(args: &[Value]) -> Value {
    if args.len() != 2 {
        panic!("cons expects 2 arguments");
    }
    Value::Object(Rc::new(HeapValue::Pair(Pair {
        car: RefCell::new(args[0].clone()),
        cdr: RefCell::new(args[1].clone()),
    })))
}

fn car(args: &[Value]) -> Value {
    if args.len() != 1 {
        panic!("car expects 1 argument");
    }
    match &args[0] {
        Value::Object(o) => match &**o {
            HeapValue::Pair(p) => p.car.borrow().clone(),
            _ => panic!("car expects a pair"),
        },
        _ => panic!("car expects a pair"),
    }
}

fn cdr(args: &[Value]) -> Value {
    if args.len() != 1 {
        panic!("cdr expects 1 argument");
    }
    match &args[0] {
        Value::Object(o) => match &**o {
            HeapValue::Pair(p) => p.cdr.borrow().clone(),
            _ => panic!("cdr expects a pair"),
        },
        _ => panic!("cdr expects a pair"),
    }
}

fn is_pair(args: &[Value]) -> Value {
    if args.len() != 1 {
        panic!("pair? expects 1 argument");
    }
    match &args[0] {
        Value::Object(o) => match &**o {
            HeapValue::Pair(_) => Value::Boolean(true),
            _ => Value::Boolean(false),
        },
        _ => Value::Boolean(false),
    }
}

fn is_null(args: &[Value]) -> Value {
    if args.len() != 1 {
        panic!("null? expects 1 argument");
    }
    match &args[0] {
        Value::Empty => Value::Boolean(true),
        _ => Value::Boolean(false),
    }
}

fn list(args: &[Value]) -> Value {
    let mut result = Value::Empty;
    for val in args.iter().rev() {
        result = Value::Object(Rc::new(HeapValue::Pair(Pair {
            car: RefCell::new(val.clone()),
            cdr: RefCell::new(result),
        })));
    }
    result
}

fn length(args: &[Value]) -> Value {
    if args.len() != 1 {
        panic!("length expects 1 argument");
    }
    let mut count = 0;
    let mut current = args[0].clone();
    loop {
        match current {
            Value::Empty => break,
            Value::Object(o) => match &*o {
                HeapValue::Pair(p) => {
                    count += 1;
                    current = p.cdr.borrow().clone();
                },
                _ => panic!("length expects a proper list"),
            },
            _ => panic!("length expects a proper list"),
        }
    }
    Value::Integer(count)
}

fn append(args: &[Value]) -> Value {
    if args.is_empty() {
        return Value::Empty;
    }
    
    let mut result = args[args.len() - 1].clone();
    
    for i in (0..args.len() - 1).rev() {
        let mut list = args[i].clone();
        let mut elements = Vec::new();
        
        // Collect elements of the current list
        loop {
            match list {
                Value::Empty => break,
                Value::Object(o) => match &*o {
                    HeapValue::Pair(p) => {
                        elements.push(p.car.borrow().clone());
                        list = p.cdr.borrow().clone();
                    },
                    _ => panic!("append expects proper lists (except last argument)"),
                },
                _ => panic!("append expects proper lists (except last argument)"),
            }
        }
        
        // Rebuild list with result as tail
        for val in elements.iter().rev() {
            result = Value::Object(Rc::new(HeapValue::Pair(Pair {
                car: RefCell::new(val.clone()),
                cdr: RefCell::new(result),
            })));
        }
    }
    result
}

fn reverse(args: &[Value]) -> Value {
    if args.len() != 1 {
        panic!("reverse expects 1 argument");
    }
    let mut result = Value::Empty;
    let mut current = args[0].clone();
    loop {
        match current {
            Value::Empty => break,
            Value::Object(o) => match &*o {
                HeapValue::Pair(p) => {
                    result = Value::Object(Rc::new(HeapValue::Pair(Pair {
                        car: RefCell::new(p.car.borrow().clone()),
                        cdr: RefCell::new(result),
                    })));
                    current = p.cdr.borrow().clone();
                },
                _ => panic!("reverse expects a proper list"),
            },
            _ => panic!("reverse expects a proper list"),
        }
    }
    result
}

fn list_ref(args: &[Value]) -> Value {
    if args.len() != 2 {
        panic!("list-ref expects 2 arguments");
    }
    let mut list = args[0].clone();
    let index = match args[1] {
        Value::Integer(i) => i,
        _ => panic!("list-ref index must be an integer"),
    };
    
    if index < 0 {
        panic!("list-ref index must be non-negative");
    }
    
    let mut current_index = 0;
    loop {
        match list {
            Value::Empty => panic!("list-ref index out of bounds"),
            Value::Object(o) => match &*o {
                HeapValue::Pair(p) => {
                    if current_index == index {
                        return p.car.borrow().clone();
                    }
                    list = p.cdr.borrow().clone();
                    current_index += 1;
                },
                _ => panic!("list-ref expects a proper list"),
            },
            _ => panic!("list-ref expects a proper list"),
        }
    }
}

fn list_tail(args: &[Value]) -> Value {
    if args.len() != 2 {
        panic!("list-tail expects 2 arguments");
    }
    let mut list = args[0].clone();
    let index = match args[1] {
        Value::Integer(i) => i,
        _ => panic!("list-tail index must be an integer"),
    };
    
    if index < 0 {
        panic!("list-tail index must be non-negative");
    }
    
    let mut current_index = 0;
    loop {
        if current_index == index {
            return list;
        }
        match list {
            Value::Empty => panic!("list-tail index out of bounds"),
            Value::Object(o) => match &*o {
                HeapValue::Pair(p) => {
                    list = p.cdr.borrow().clone();
                    current_index += 1;
                },
                _ => panic!("list-tail expects a proper list"),
            },
            _ => panic!("list-tail expects a proper list"),
        }
    }
}

fn cadr(args: &[Value]) -> Value {
    if args.len() != 1 { panic!("cadr expects 1 argument"); }
    let l = args[0].clone();
    // (car (cdr l))
    match l {
        Value::Object(o) => match &*o {
            HeapValue::Pair(p) => {
                let cdr = p.cdr.borrow().clone();
                match cdr {
                    Value::Object(o2) => match &*o2 {
                        HeapValue::Pair(p2) => p2.car.borrow().clone(),
                        _ => panic!("cadr expects a list of at least length 2"),
                    },
                    _ => panic!("cadr expects a list of at least length 2"),
                }
            },
            _ => panic!("cadr expects a pair"),
        },
        _ => panic!("cadr expects a pair"),
    }
}

fn caddr(args: &[Value]) -> Value {
    if args.len() != 1 { panic!("caddr expects 1 argument"); }
    // (car (cdr (cdr l)))
    let l = args[0].clone();
    match l {
        Value::Object(o) => match &*o {
            HeapValue::Pair(p) => {
                let cdr = p.cdr.borrow().clone();
                match cdr {
                    Value::Object(o2) => match &*o2 {
                        HeapValue::Pair(p2) => {
                            let cddr = p2.cdr.borrow().clone();
                            match cddr {
                                Value::Object(o3) => match &*o3 {
                                    HeapValue::Pair(p3) => p3.car.borrow().clone(),
                                    _ => panic!("caddr expects a list of at least length 3"),
                                },
                                _ => panic!("caddr expects a list of at least length 3"),
                            }
                        },
                        _ => panic!("caddr expects a list of at least length 3"),
                    },
                    _ => panic!("caddr expects a list of at least length 3"),
                }
            },
            _ => panic!("caddr expects a pair"),
        },
        _ => panic!("caddr expects a pair"),
    }
}

fn cddr(args: &[Value]) -> Value {
    if args.len() != 1 { panic!("cddr expects 1 argument"); }
    // (cdr (cdr l))
    let l = args[0].clone();
    match l {
        Value::Object(o) => match &*o {
            HeapValue::Pair(p) => {
                let cdr = p.cdr.borrow().clone();
                match cdr {
                    Value::Object(o2) => match &*o2 {
                        HeapValue::Pair(p2) => p2.cdr.borrow().clone(),
                        _ => panic!("cddr expects a list of at least length 2"),
                    },
                    _ => panic!("cddr expects a list of at least length 2"),
                }
            },
            _ => panic!("cddr expects a pair"),
        },
        _ => panic!("cddr expects a pair"),
    }
}

fn set_car(args: &[Value]) -> Value {
    if args.len() != 2 { panic!("set-car! expects 2 arguments"); }
    match &args[0] {
        Value::Object(o) => match &**o {
            HeapValue::Pair(p) => {
                *p.car.borrow_mut() = args[1].clone();
                Value::Empty // or undefined
            },
            _ => panic!("set-car! expects a pair"),
        },
        _ => panic!("set-car! expects a pair"),
    }
}

fn set_cdr(args: &[Value]) -> Value {
    if args.len() != 2 { panic!("set-cdr! expects 2 arguments"); }
    match &args[0] {
        Value::Object(o) => match &**o {
            HeapValue::Pair(p) => {
                *p.cdr.borrow_mut() = args[1].clone();
                Value::Empty
            },
            _ => panic!("set-cdr! expects a pair"),
        },
        _ => panic!("set-cdr! expects a pair"),
    }
}

fn memq(args: &[Value]) -> Value {
    if args.len() != 2 { panic!("memq expects 2 arguments"); }
    let obj = &args[0];
    let mut list = args[1].clone();
    
    loop {
        let next_val = match &list {
            Value::Empty => return Value::Boolean(false),
            Value::Object(o) => match &**o {
                HeapValue::Pair(p) => {
                    let car = p.car.borrow();
                    if *car == *obj {
                         drop(car);
                         return list.clone();
                    }
                    drop(car);
                    p.cdr.borrow().clone()
                },
                _ => panic!("memq expects a proper list"),
            },
            _ => panic!("memq expects a proper list"),
        };
        list = next_val;
    }
}

fn member(args: &[Value]) -> Value {
    memq(args)
}

fn assq(args: &[Value]) -> Value {
    if args.len() != 2 { panic!("assq expects 2 arguments"); }
    let obj = &args[0];
    let mut list = args[1].clone();
    
    loop {
        let next_val = match &list {
            Value::Empty => return Value::Boolean(false),
            Value::Object(o) => match &**o {
                HeapValue::Pair(p) => {
                    let entry = p.car.borrow().clone();
                    match &entry {
                        Value::Object(oe) => match &**oe {
                            HeapValue::Pair(pe) => {
                                let key = pe.car.borrow();
                                if *key == *obj {
                                    drop(key);
                                    return entry.clone();
                                }
                            },
                            _ => {}
                        },
                        _ => {}
                    }
                    p.cdr.borrow().clone()
                },
                _ => panic!("assq expects a proper list"),
            },
            _ => panic!("assq expects a proper list"),
        };
        list = next_val;
    }
}

fn assoc(args: &[Value]) -> Value {
    assq(args)
}