use super::{compiler::Compiler, vp::Value, vp::ValueKind, vp::Pair, vp::HeapValue, vp::VmContext};

pub fn register_functions(compiler: &mut Compiler) {
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

fn list(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    let len = args.len();
    if len == 0 {
        return Ok(Value::nil());
    }

    let heap = ctx.heap();
    
    if len == 1 {
        let p = Pair{ car: args[0], cdr: Value::nil() };
        return Ok(Value::object(heap.alloc(HeapValue::Pair(p))));
    }
    
    if len == 2 {
        let p2 = Pair{ car: args[1], cdr: Value::nil() };
        let h2 = heap.alloc(HeapValue::Pair(p2));
        let p1 = Pair{ car: args[0], cdr: Value::object(h2) };
        return Ok(Value::object(heap.alloc(HeapValue::Pair(p1)))); 
    }

    if len == 3 {
        let p3 = Pair{ car: args[2], cdr: Value::nil() };
        let h3 = heap.alloc(HeapValue::Pair(p3));
        let p2 = Pair{ car: args[1], cdr: Value::object(h3) };
        let h2 = heap.alloc(HeapValue::Pair(p2));
        let p1 = Pair{ car: args[0], cdr: Value::object(h2) };
        return Ok(Value::object(heap.alloc(HeapValue::Pair(p1))));
    }

    let mut result = Value::nil();
    for val in args.iter().rev() {
        let pair = Pair {
            car: *val,
            cdr: result,
        };
        result = Value::object(heap.alloc(HeapValue::Pair(pair)));
    }
    Ok(result)
}

fn length(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 {
        return Err("length expects 1 argument".to_string());
    }
    let mut count = 0;
    let mut current = args[0].clone();
    loop {
        match current.kind() {
            ValueKind::Nil => break,
            ValueKind::Object(o) => match ctx.heap().get(o) {
                Some(HeapValue::Pair(p)) => {
                    count += 1;
                    current = p.cdr;
                },
                _ => return Err("length expects a proper list".to_string()),
            },
            _ => return Err("length expects a proper list".to_string()),
        }
    }
    Ok(Value::integer(count))
}

fn append(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.is_empty() {
        return Ok(Value::nil());
    }
    
    let mut result = args[args.len() - 1].clone();
    ctx.push_scratch(result);
    
    for i in (0..args.len() - 1).rev() {
        let mut list = args[i].clone();
        let mut elements = Vec::new();
        
        // Collect elements of the current list
        loop {
            match list.kind() {
                ValueKind::Nil => break,
                ValueKind::Object(o) => match ctx.heap().get(o) {
                    Some(HeapValue::Pair(p)) => {
                        elements.push(p.car);
                        list = p.cdr;
                    },
                    _ => return Err("append expects proper lists (except last argument)".to_string()),
                },
                _ => return Err("append expects proper lists (except last argument)".to_string()),
            }
        }
        
        // Rebuild list with result as tail
        for val in elements.iter().rev() {
            ctx.pop_scratch();
            ctx.push_scratch(result);
            
            ctx.collect();
            let pair = Pair {
                car: *val,
                cdr: result,
            };
            result = Value::object(ctx.heap().alloc(HeapValue::Pair(pair)));
        }
    }
    ctx.pop_scratch();
    Ok(result)
}

fn reverse(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 {
        return Err("reverse expects 1 argument".to_string());
    }
    let mut result = Value::nil();
    let mut current = args[0].clone();
    loop {
        match current.kind() {
            ValueKind::Nil => break,
            ValueKind::Object(handle) => {
                let (car, cdr) = match ctx.heap().get(handle) {
                    Some(HeapValue::Pair(p)) => (p.car, p.cdr),
                    _ => return Err("reverse expects a proper list".to_string()),
                };
                let pair = Pair {
                    car,
                    cdr: result,
                };
                result = Value::object(ctx.heap().alloc(HeapValue::Pair(pair)));
                current = cdr;
            },
            _ => return Err("reverse expects a proper list".to_string()),
        }
    }
    Ok(result)
}

fn list_ref(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 2 {
        return Err("list-ref expects 2 arguments".to_string());
    }
    let mut list = args[0].clone();
    let index = match args[1].kind() {
        ValueKind::Integer(i) => i,
        _ => return Err("list-ref index must be an integer".to_string()),
    };
    
    if index < 0 {
        return Err("list-ref index must be non-negative".to_string());
    }
    
    let mut current_index = 0;
    loop {
        match list.kind() {
            ValueKind::Nil => return Err("list-ref index out of bounds".to_string()),
            ValueKind::Object(o) => match ctx.heap().get(o) {
                Some(HeapValue::Pair(p)) => {
                    if current_index == index {
                        return Ok(p.car);
                    }
                    list = p.cdr;
                    current_index += 1;
                },
                _ => return Err("list-ref expects a proper list".to_string()),
            },
            _ => return Err("list-ref expects a proper list".to_string()),
        }
    }
}

fn list_tail(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 2 {
        return Err("list-tail expects 2 arguments".to_string());
    }
    let mut list = args[0].clone();
    let index = match args[1].kind() {
        ValueKind::Integer(i) => i,
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
        match list.kind() {
            ValueKind::Nil => return Err("list-tail index out of bounds".to_string()),
            ValueKind::Object(o) => match ctx.heap().get(o) {
                Some(HeapValue::Pair(p)) => {
                    list = p.cdr;
                    current_index += 1;
                },
                _ => return Err("list-tail expects a proper list".to_string()),
            },
            _ => return Err("list-tail expects a proper list".to_string()),
        }
    }
}

fn cadr(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 { return Err("cadr expects 1 argument".to_string()); }
    let l = args[0].clone();
    // (car (cdr l))
    match l.kind() {
        ValueKind::Object(o) => match ctx.heap().get(o) {
            Some(HeapValue::Pair(p)) => {
                let cdr = p.cdr;
                match cdr.kind() {
                    ValueKind::Object(o2) => match ctx.heap().get(o2) {
                        Some(HeapValue::Pair(p2)) => Ok(p2.car),
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

fn caddr(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 { return Err("caddr expects 1 argument".to_string()); }
    // (car (cdr (cdr l)))
    let l = args[0].clone();
    match l.kind() {
        ValueKind::Object(o) => match ctx.heap().get(o) {
            Some(HeapValue::Pair(p)) => {
                let cdr = p.cdr;
                match cdr.kind() {
                    ValueKind::Object(o2) => match ctx.heap().get(o2) {
                        Some(HeapValue::Pair(p2)) => {
                            let cddr = p2.cdr;
                            match cddr.kind() {
                                ValueKind::Object(o3) => match ctx.heap().get(o3) {
                                    Some(HeapValue::Pair(p3)) => Ok(p3.car),
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

fn cddr(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 1 { return Err("cddr expects 1 argument".to_string()); }
    // (cdr (cdr l))
    let l = args[0].clone();
    match l.kind() {
        ValueKind::Object(o) => match ctx.heap().get(o) {
            Some(HeapValue::Pair(p)) => {
                let cdr = p.cdr;
                match cdr.kind() {
                    ValueKind::Object(o2) => match ctx.heap().get(o2) {
                        Some(HeapValue::Pair(p2)) => Ok(p2.cdr),
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

fn set_car(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 2 { return Err("set-car! expects 2 arguments".to_string()); }
    match args[0].kind() {
        ValueKind::Object(handle) => match ctx.heap().get_mut(handle) {
            Some(HeapValue::Pair(p)) => {
                p.car = args[1];
                Ok(Value::nil())
            },
            _ => Err("set-car! expects a pair".to_string()),
        },
        _ => Err("set-car! expects a pair".to_string()),
    }
}

fn set_cdr(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 2 { return Err("set-cdr! expects 2 arguments".to_string()); }
    match args[0].kind() {
        ValueKind::Object(handle) => match ctx.heap().get_mut(handle) {
            Some(HeapValue::Pair(p)) => {
                p.cdr = args[1];
                Ok(Value::nil())
            },
            _ => Err("set-cdr! expects a pair".to_string()),
        },
        _ => Err("set-cdr! expects a pair".to_string()),
    }
}

fn memq(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 2 { return Err("memq expects 2 arguments".to_string()); }
    let obj = &args[0];
    let mut list = args[1].clone();
    
    loop {
        let next_val = match list.kind() {
            ValueKind::Nil => return Ok(Value::boolean(false)),
            ValueKind::Object(o) => match ctx.heap().get(o) {
                Some(HeapValue::Pair(p)) => {
                    let car = p.car;
                    if car == *obj {
                         return Ok(list.clone());
                    }
                    p.cdr
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

fn assq(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    if args.len() != 2 { return Err("assq expects 2 arguments".to_string()); }
    let obj = &args[0];
    let mut list = args[1].clone();
    
    loop {
        let (entry, cdr) = match list.kind() {
            ValueKind::Nil => return Ok(Value::boolean(false)),
            ValueKind::Object(o) => match ctx.heap().get(o) {
                Some(HeapValue::Pair(p)) => (p.car, p.cdr),
                _ => return Err("assq expects a proper list".to_string()),
            },
            _ => return Err("assq expects a proper list".to_string()),
        };

        match entry.kind() {
            ValueKind::Object(oe) => match ctx.heap().get(oe) {
                Some(HeapValue::Pair(pe)) => {
                    let key = pe.car;
                    if key == *obj {
                        return Ok(entry.clone());
                    }
                },
                _ => {}
            },
            _ => {}
        }
        list = cdr;
    }
}

fn assoc(ctx: &mut dyn VmContext, args: &[Value]) -> Result<Value, String> {
    assq(ctx, args)
}