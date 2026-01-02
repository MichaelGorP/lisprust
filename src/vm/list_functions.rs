use gc::{Gc, GcCell};
use super::{compiler::Compiler, vp::Value, vp::Pair, vp::HeapValue, vp::VmContext};

pub fn register_functions(compiler: &mut Compiler) {
    compiler.register_function("car", car, Some(1));
    compiler.register_function("cdr", cdr, Some(1));
    compiler.register_function("cons", cons, Some(2));
    compiler.register_function("pair?", is_pair, Some(1));
    compiler.register_function("null?", is_null, Some(1));
    compiler.register_function("list", list, None);
    // compiler.register_function("map", map, None); // Requires VM callback
    compiler.register_function("append", append, None);
    compiler.register_function("reverse", reverse, Some(1));
    compiler.register_function("member", member, Some(2));
    compiler.register_function("memq", memq, Some(2));
    compiler.register_function("assoc", assoc, Some(2));
    compiler.register_function("assq", assq, Some(2));
    compiler.register_function("cadr", cadr, Some(1));
    compiler.register_function("caddr", caddr, Some(1));
    compiler.register_function("cddr", cddr, Some(1));
    compiler.register_function("set-car!", set_car, Some(2));
    compiler.register_function("set-cdr!", set_cdr, Some(2));
    compiler.register_function("length", length, Some(1));
    // compiler.register_function("for-each", for_each, None); // Requires VM callback
    compiler.register_function("list-ref", list_ref, Some(2));
    compiler.register_function("list-tail", list_tail, Some(2));
    // compiler.register_function("filter", filter, None); // Requires VM callback
    // compiler.register_function("fold", fold, None); // Requires VM callback
}

fn cons(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 2 {
        return Err("cons expects 2 arguments".to_string());
    }
    Ok(Value::Object(Gc::new(HeapValue::Pair(Pair {
        car: GcCell::new(args[0].clone()),
        cdr: GcCell::new(args[1].clone()),
    }))))
}

fn car(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 {
        return Err("car expects 1 argument".to_string());
    }
    match &args[0] {
        Value::Object(o) => match &**o {
            HeapValue::Pair(p) => Ok(p.get_car()),
            _ => Err("car expects a pair".to_string()),
        },
        _ => Err("car expects a pair".to_string()),
    }
}

fn cdr(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 {
        return Err("cdr expects 1 argument".to_string());
    }
    match &args[0] {
        Value::Object(o) => match &**o {
            HeapValue::Pair(p) => Ok(p.get_cdr()),
            _ => Err("cdr expects a pair".to_string()),
        },
        _ => Err("cdr expects a pair".to_string()),
    }
}

fn is_pair(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 {
        return Err("pair? expects 1 argument".to_string());
    }
    match &args[0] {
        Value::Object(o) => match &**o {
            HeapValue::Pair(_) => Ok(Value::Boolean(true)),
            _ => Ok(Value::Boolean(false)),
        },
        _ => Ok(Value::Boolean(false)),
    }
}

fn is_null(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 {
        return Err("null? expects 1 argument".to_string());
    }
    match &args[0] {
        Value::Empty => Ok(Value::Boolean(true)),
        _ => Ok(Value::Boolean(false)),
    }
}

fn list(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    let mut result = Value::Empty;
    for val in args.iter().rev() {
        result = Value::Object(Gc::new(HeapValue::Pair(Pair {
            car: GcCell::new(val.clone()),
            cdr: GcCell::new(result),
        })));
    }
    Ok(result)
}

fn length(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 {
        return Err("length expects 1 argument".to_string());
    }
    let mut count = 0;
    let mut current = args[0].clone();
    loop {
        match current {
            Value::Empty => break,
            Value::Object(o) => match &*o {
                HeapValue::Pair(p) => {
                    count += 1;
                    current = p.get_cdr();
                },
                _ => return Err("length expects a proper list".to_string()),
            },
            _ => return Err("length expects a proper list".to_string()),
        }
    }
    Ok(Value::Integer(count))
}

fn append(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.is_empty() {
        return Ok(Value::Empty);
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
                        elements.push(p.get_car());
                        list = p.get_cdr();
                    },
                    _ => return Err("append expects proper lists (except last argument)".to_string()),
                },
                _ => return Err("append expects proper lists (except last argument)".to_string()),
            }
        }
        
        // Rebuild list with result as tail
        for val in elements.iter().rev() {
            result = Value::Object(Gc::new(HeapValue::Pair(Pair {
                car: GcCell::new(val.clone()),
                cdr: GcCell::new(result),
            })));
        }
    }
    Ok(result)
}

fn reverse(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 {
        return Err("reverse expects 1 argument".to_string());
    }
    let mut result = Value::Empty;
    let mut current = args[0].clone();
    loop {
        match current {
            Value::Empty => break,
            Value::Object(o) => match &*o {
                HeapValue::Pair(p) => {
                    result = Value::Object(Gc::new(HeapValue::Pair(Pair {
                        car: GcCell::new(p.get_car()),
                        cdr: GcCell::new(result),
                    })));
                    current = p.get_cdr();
                },
                _ => return Err("reverse expects a proper list".to_string()),
            },
            _ => return Err("reverse expects a proper list".to_string()),
        }
    }
    Ok(result)
}

fn list_ref(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 2 {
        return Err("list-ref expects 2 arguments".to_string());
    }
    let mut list = args[0].clone();
    let index = match args[1] {
        Value::Integer(i) => i,
        _ => return Err("list-ref index must be an integer".to_string()),
    };
    
    if index < 0 {
        return Err("list-ref index must be non-negative".to_string());
    }
    
    let mut current_index = 0;
    loop {
        match list {
            Value::Empty => return Err("list-ref index out of bounds".to_string()),
            Value::Object(o) => match &*o {
                HeapValue::Pair(p) => {
                    if current_index == index {
                        return Ok(p.get_car());
                    }
                    list = p.get_cdr();
                    current_index += 1;
                },
                _ => return Err("list-ref expects a proper list".to_string()),
            },
            _ => return Err("list-ref expects a proper list".to_string()),
        }
    }
}

fn list_tail(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 2 {
        return Err("list-tail expects 2 arguments".to_string());
    }
    let mut list = args[0].clone();
    let index = match args[1] {
        Value::Integer(i) => i,
        _ => return Err("list-tail index must be an integer".to_string()),
    };
    
    if index < 0 {
        return Err("list-tail index must be non-negative".to_string());
    }
    
    let mut current_index = 0;
    loop {
        if current_index == index {
            return Ok(list);
        }
        match list {
            Value::Empty => return Err("list-tail index out of bounds".to_string()),
            Value::Object(o) => match &*o {
                HeapValue::Pair(p) => {
                    list = p.get_cdr();
                    current_index += 1;
                },
                _ => return Err("list-tail expects a proper list".to_string()),
            },
            _ => return Err("list-tail expects a proper list".to_string()),
        }
    }
}

fn cadr(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 { return Err("cadr expects 1 argument".to_string()); }
    let l = args[0].clone();
    // (car (cdr l))
    match l {
        Value::Object(o) => match &*o {
            HeapValue::Pair(p) => {
                let cdr = p.get_cdr();
                match cdr {
                    Value::Object(o2) => match &*o2 {
                        HeapValue::Pair(p2) => Ok(p2.get_car()),
                        _ => Err("cadr expects a list of at least length 2".to_string()),
                    },
                    _ => Err("cadr expects a list of at least length 2".to_string()),
                }
            },
            _ => Err("cadr expects a pair".to_string()),
        },
        _ => Err("cadr expects a pair".to_string()),
    }
}

fn caddr(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 { return Err("caddr expects 1 argument".to_string()); }
    // (car (cdr (cdr l)))
    let l = args[0].clone();
    match l {
        Value::Object(o) => match &*o {
            HeapValue::Pair(p) => {
                let cdr = p.get_cdr();
                match cdr {
                    Value::Object(o2) => match &*o2 {
                        HeapValue::Pair(p2) => {
                            let cddr = p2.get_cdr();
                            match cddr {
                                Value::Object(o3) => match &*o3 {
                                    HeapValue::Pair(p3) => Ok(p3.get_car()),
                                    _ => Err("caddr expects a list of at least length 3".to_string()),
                                },
                                _ => Err("caddr expects a list of at least length 3".to_string()),
                            }
                        },
                        _ => Err("caddr expects a list of at least length 3".to_string()),
                    },
                    _ => Err("caddr expects a list of at least length 3".to_string()),
                }
            },
            _ => Err("caddr expects a pair".to_string()),
        },
        _ => Err("caddr expects a pair".to_string()),
    }
}

fn cddr(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 { return Err("cddr expects 1 argument".to_string()); }
    // (cdr (cdr l))
    let l = args[0].clone();
    match l {
        Value::Object(o) => match &*o {
            HeapValue::Pair(p) => {
                let cdr = p.get_cdr();
                match cdr {
                    Value::Object(o2) => match &*o2 {
                        HeapValue::Pair(p2) => Ok(p2.get_cdr()),
                        _ => Err("cddr expects a list of at least length 2".to_string()),
                    },
                    _ => Err("cddr expects a list of at least length 2".to_string()),
                }
            },
            _ => Err("cddr expects a pair".to_string()),
        },
        _ => Err("cddr expects a pair".to_string()),
    }
}

fn set_car(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 2 { return Err("set-car! expects 2 arguments".to_string()); }
    match &args[0] {
        Value::Object(o) => match &**o {
            HeapValue::Pair(p) => {
                *p.car.borrow_mut() = args[1].clone();
                Ok(Value::Empty)
            },
            _ => Err("set-car! expects a pair".to_string()),
        },
        _ => Err("set-car! expects a pair".to_string()),
    }
}

fn set_cdr(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 2 { return Err("set-cdr! expects 2 arguments".to_string()); }
    match &args[0] {
        Value::Object(o) => match &**o {
            HeapValue::Pair(p) => {
                *p.cdr.borrow_mut() = args[1].clone();
                Ok(Value::Empty)
            },
            _ => Err("set-cdr! expects a pair".to_string()),
        },
        _ => Err("set-cdr! expects a pair".to_string()),
    }
}

fn memq(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 2 { return Err("memq expects 2 arguments".to_string()); }
    let obj = &args[0];
    let mut list = args[1].clone();
    
    loop {
        let next_val = match &list {
            Value::Empty => return Ok(Value::Boolean(false)),
            Value::Object(o) => match &**o {
                HeapValue::Pair(p) => {
                    let car = p.get_car();
                    if car == *obj {
                         return Ok(list.clone());
                    }
                    p.get_cdr()
                },
                _ => return Err("memq expects a proper list".to_string()),
            },
            _ => return Err("memq expects a proper list".to_string()),
        };
        list = next_val;
    }
}

fn member(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    memq(ctx, args)
}

fn assq(_ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 2 { return Err("assq expects 2 arguments".to_string()); }
    let obj = &args[0];
    let mut list = args[1].clone();
    
    loop {
        let next_val = match &list {
            Value::Empty => return Ok(Value::Boolean(false)),
            Value::Object(o) => match &**o {
                HeapValue::Pair(p) => {
                    let entry = p.get_car();
                    match &entry {
                        Value::Object(oe) => match &**oe {
                            HeapValue::Pair(pe) => {
                                let key = pe.get_car();
                                if key == *obj {
                                    return Ok(entry.clone());
                                }
                            },
                            _ => {}
                        },
                        _ => {}
                    }
                    p.get_cdr()
                },
                _ => return Err("assq expects a proper list".to_string()),
            },
            _ => return Err("assq expects a proper list".to_string()),
        };
        list = next_val;
    }
}

fn assoc(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    assq(ctx, args)
}