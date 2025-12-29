use super::{compiler::Compiler, vp::Value};

pub fn register_functions(compiler: &mut Compiler) {
    compiler.register_function("sin", sin_impl);
    compiler.register_function("cos", cos_impl);
    compiler.register_function("tan", tan_impl);
    compiler.register_function("asin", asin_impl);
    compiler.register_function("acos", acos_impl);
    compiler.register_function("atan", atan_impl);
    compiler.register_function("sqrt", sqrt_impl);
    compiler.register_function("exp", exp_impl);
    compiler.register_function("log", log_impl);
    compiler.register_function("expt", expt_impl);
    compiler.register_function("abs", abs_impl);
    compiler.register_function("floor", floor_impl);
    compiler.register_function("ceiling", ceiling_impl);
    compiler.register_function("truncate", truncate_impl);
    compiler.register_function("round", round_impl);
    compiler.register_function("quotient", quotient_impl);
    compiler.register_function("remainder", remainder_impl);
    compiler.register_function("modulo", modulo_impl);
    compiler.register_function("gcd", gcd_impl);
    compiler.register_function("lcm", lcm_impl);
    compiler.register_function("max", max_impl);
    compiler.register_function("min", min_impl);
}

fn get_float(v: &Value) -> Option<f64> {
    match v {
        Value::Float(f) => Some(*f),
        Value::Integer(i) => Some(*i as f64),
        _ => None
    }
}

fn sin_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Value::Float(f.sin())
        }
    }
    Value::Empty
}

fn cos_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Value::Float(f.cos())
        }
    }
    Value::Empty
}

fn tan_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Value::Float(f.tan())
        }
    }
    Value::Empty
}

fn asin_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Value::Float(f.asin())
        }
    }
    Value::Empty
}

fn acos_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Value::Float(f.acos())
        }
    }
    Value::Empty
}

fn atan_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Value::Float(f.atan())
        }
    } else if input.len() == 2 {
        if let (Some(y), Some(x)) = (get_float(&input[0]), get_float(&input[1])) {
            return Value::Float(y.atan2(x))
        }
    }
    Value::Empty
}

fn sqrt_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Value::Float(f.sqrt())
        }
    }
    Value::Empty
}

fn exp_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Value::Float(f.exp())
        }
    }
    Value::Empty
}

fn log_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Value::Float(f.ln())
        }
    }
    Value::Empty
}

fn expt_impl(input: &[Value]) -> Value {
    if input.len() == 2 {
        if let (Some(b), Some(e)) = (get_float(&input[0]), get_float(&input[1])) {
            return Value::Float(b.powf(e))
        }
    }
    Value::Empty
}

fn abs_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        match input[0] {
            Value::Float(f) => Value::Float(f.abs()),
            Value::Integer(i) => Value::Integer(i.abs()),
            _ => Value::Empty
        }
    } else {
        Value::Empty
    }
}

fn floor_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        match input[0] {
            Value::Float(f) => Value::Float(f.floor()),
            Value::Integer(i) => Value::Integer(i),
            _ => Value::Empty
        }
    } else {
        Value::Empty
    }
}

fn ceiling_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        match input[0] {
            Value::Float(f) => Value::Float(f.ceil()),
            Value::Integer(i) => Value::Integer(i),
            _ => Value::Empty
        }
    } else {
        Value::Empty
    }
}

fn truncate_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        match input[0] {
            Value::Float(f) => Value::Float(f.trunc()),
            Value::Integer(i) => Value::Integer(i),
            _ => Value::Empty
        }
    } else {
        Value::Empty
    }
}

fn round_impl(input: &[Value]) -> Value {
    if input.len() == 1 {
        match input[0] {
            Value::Float(f) => Value::Float(f.round()),
            Value::Integer(i) => Value::Integer(i),
            _ => Value::Empty
        }
    } else {
        Value::Empty
    }
}

fn quotient_impl(input: &[Value]) -> Value {
    if input.len() == 2 {
        if let (Value::Integer(n1), Value::Integer(n2)) = (&input[0], &input[1]) {
            if *n2 == 0 { return Value::Empty; }
            return Value::Integer(n1 / n2);
        }
    }
    Value::Empty
}

fn remainder_impl(input: &[Value]) -> Value {
    if input.len() == 2 {
        if let (Value::Integer(n1), Value::Integer(n2)) = (&input[0], &input[1]) {
            if *n2 == 0 { return Value::Empty; }
            return Value::Integer(n1 % n2);
        }
    }
    Value::Empty
}

fn modulo_impl(input: &[Value]) -> Value {
    if input.len() == 2 {
        if let (Value::Integer(n1), Value::Integer(n2)) = (&input[0], &input[1]) {
            if *n2 == 0 { return Value::Empty; }
            let rem = n1 % n2;
            if (rem < 0 && *n2 > 0) || (rem > 0 && *n2 < 0) {
                return Value::Integer(rem + n2);
            }
            return Value::Integer(rem);
        }
    }
    Value::Empty
}

fn gcd_impl(input: &[Value]) -> Value {
    if input.is_empty() {
        return Value::Integer(0);
    }
    let mut result = match input[0] {
        Value::Integer(i) => i.abs(),
        _ => return Value::Empty
    };
    for i in 1..input.len() {
        match input[i] {
            Value::Integer(val) => {
                result = gcd(result, val.abs());
            },
            _ => return Value::Empty
        }
    }
    Value::Integer(result)
}

fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

fn lcm_impl(input: &[Value]) -> Value {
    if input.is_empty() {
        return Value::Integer(1);
    }
    let mut result = match input[0] {
        Value::Integer(i) => i.abs(),
        _ => return Value::Empty
    };
    for i in 1..input.len() {
        match input[i] {
            Value::Integer(val) => {
                let val = val.abs();
                if result == 0 || val == 0 {
                    result = 0;
                } else {
                    result = (result / gcd(result, val)) * val;
                }
            },
            _ => return Value::Empty
        }
    }
    Value::Integer(result)
}

fn compare(v1: &Value, v2: &Value) -> Option<std::cmp::Ordering> {
    match (v1, v2) {
        (Value::Integer(i1), Value::Integer(i2)) => Some(i1.cmp(i2)),
        (Value::Float(f1), Value::Float(f2)) => f1.partial_cmp(f2),
        (Value::Integer(i), Value::Float(f)) => (*i as f64).partial_cmp(f),
        (Value::Float(f), Value::Integer(i)) => f.partial_cmp(&(*i as f64)),
        _ => None
    }
}

fn max_impl(input: &[Value]) -> Value {
    if input.is_empty() { return Value::Empty; }
    let mut max_val = input[0].clone();
    for i in 1..input.len() {
        if let Some(ord) = compare(&input[i], &max_val) {
            if ord == std::cmp::Ordering::Greater {
                max_val = input[i].clone();
            }
        } else {
            return Value::Empty;
        }
    }
    max_val
}

fn min_impl(input: &[Value]) -> Value {
    if input.is_empty() { return Value::Empty; }
    let mut min_val = input[0].clone();
    for i in 1..input.len() {
        if let Some(ord) = compare(&input[i], &min_val) {
            if ord == std::cmp::Ordering::Less {
                min_val = input[i].clone();
            }
        } else {
            return Value::Empty;
        }
    }
    min_val
}
