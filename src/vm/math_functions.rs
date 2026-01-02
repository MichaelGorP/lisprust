use super::{compiler::Compiler, vp::Value, vp::VmContext};

pub fn register_functions(compiler: &mut Compiler) {
    compiler.register_function("sin", sin_impl, Some(1));
    compiler.register_function("cos", cos_impl, Some(1));
    compiler.register_function("tan", tan_impl, Some(1));
    compiler.register_function("asin", asin_impl, Some(1));
    compiler.register_function("acos", acos_impl, Some(1));
    compiler.register_function("atan", atan_impl, Some(1));
    compiler.register_function("sqrt", sqrt_impl, Some(1));
    compiler.register_function("exp", exp_impl, Some(1));
    compiler.register_function("log", log_impl, Some(1));
    compiler.register_function("expt", expt_impl, Some(2));
    compiler.register_function("abs", abs_impl, Some(1));
    compiler.register_function("floor", floor_impl, Some(1));
    compiler.register_function("ceiling", ceiling_impl, Some(1));
    compiler.register_function("truncate", truncate_impl, Some(1));
    compiler.register_function("round", round_impl, Some(1));
    compiler.register_function("quotient", quotient_impl, Some(2));
    compiler.register_function("remainder", remainder_impl, Some(2));
    compiler.register_function("modulo", modulo_impl, Some(2));
    compiler.register_function("gcd", gcd_impl, None);
    compiler.register_function("lcm", lcm_impl, None);
    compiler.register_function("max", max_impl, None);
    compiler.register_function("min", min_impl, None);
}

fn get_float(v: &Value) -> Option<f64> {
    match v {
        Value::Float(f) => Some(*f),
        Value::Integer(i) => Some(*i as f64),
        _ => None
    }
}

fn sin_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::Float(f.sin()));
        }
    }
    Err("sin expects 1 number argument".to_string())
}

fn cos_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::Float(f.cos()));
        }
    }
    Err("cos expects 1 number argument".to_string())
}

fn tan_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::Float(f.tan()));
        }
    }
    Err("tan expects 1 number argument".to_string())
}

fn asin_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::Float(f.asin()));
        }
    }
    Err("asin expects 1 number argument".to_string())
}

fn acos_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::Float(f.acos()));
        }
    }
    Err("acos expects 1 number argument".to_string())
}

fn atan_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::Float(f.atan()));
        }
    } else if input.len() == 2 {
        if let (Some(y), Some(x)) = (get_float(&input[0]), get_float(&input[1])) {
            return Ok(Value::Float(y.atan2(x)));
        }
    }
    Err("atan expects 1 or 2 number arguments".to_string())
}

fn sqrt_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            if f < 0.0 { return Err("sqrt expects non-negative argument".to_string()); }
            return Ok(Value::Float(f.sqrt()));
        }
    }
    Err("sqrt expects 1 number argument".to_string())
}

fn exp_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::Float(f.exp()));
        }
    }
    Err("exp expects 1 number argument".to_string())
}

fn log_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            if f <= 0.0 { return Err("log expects positive argument".to_string()); }
            return Ok(Value::Float(f.ln()));
        }
    }
    Err("log expects 1 number argument".to_string())
}

fn expt_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 2 {
        if let (Some(b), Some(e)) = (get_float(&input[0]), get_float(&input[1])) {
            return Ok(Value::Float(b.powf(e)));
        }
    }
    Err("expt expects 2 number arguments".to_string())
}

fn abs_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        match input[0] {
            Value::Float(f) => Ok(Value::Float(f.abs())),
            Value::Integer(i) => Ok(Value::Integer(i.abs())),
            _ => Err("abs expects a number".to_string())
        }
    } else {
        Err("abs expects 1 argument".to_string())
    }
}

fn floor_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        match input[0] {
            Value::Float(f) => Ok(Value::Float(f.floor())),
            Value::Integer(i) => Ok(Value::Integer(i)),
            _ => Err("floor expects a number".to_string())
        }
    } else {
        Err("floor expects 1 argument".to_string())
    }
}

fn ceiling_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        match input[0] {
            Value::Float(f) => Ok(Value::Float(f.ceil())),
            Value::Integer(i) => Ok(Value::Integer(i)),
            _ => Err("ceiling expects a number".to_string())
        }
    } else {
        Err("ceiling expects 1 argument".to_string())
    }
}

fn truncate_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        match input[0] {
            Value::Float(f) => Ok(Value::Float(f.trunc())),
            Value::Integer(i) => Ok(Value::Integer(i)),
            _ => Err("truncate expects a number".to_string())
        }
    } else {
        Err("truncate expects 1 argument".to_string())
    }
}

fn round_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        match input[0] {
            Value::Float(f) => Ok(Value::Float(f.round())),
            Value::Integer(i) => Ok(Value::Integer(i)),
            _ => Err("round expects a number".to_string())
        }
    } else {
        Err("round expects 1 argument".to_string())
    }
}

fn quotient_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 2 {
        if let (Value::Integer(n1), Value::Integer(n2)) = (&input[0], &input[1]) {
            if *n2 == 0 { return Err("division by zero".to_string()); }
            return Ok(Value::Integer(n1 / n2));
        }
    }
    Err("quotient expects 2 integers".to_string())
}

fn remainder_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 2 {
        if let (Value::Integer(n1), Value::Integer(n2)) = (&input[0], &input[1]) {
            if *n2 == 0 { return Err("division by zero".to_string()); }
            return Ok(Value::Integer(n1 % n2));
        }
    }
    Err("remainder expects 2 integers".to_string())
}

fn modulo_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 2 {
        if let (Value::Integer(n1), Value::Integer(n2)) = (&input[0], &input[1]) {
            if *n2 == 0 { return Err("division by zero".to_string()); }
            let rem = n1 % n2;
            if (rem < 0 && *n2 > 0) || (rem > 0 && *n2 < 0) {
                return Ok(Value::Integer(rem + n2));
            }
            return Ok(Value::Integer(rem));
        }
    }
    Err("modulo expects 2 integers".to_string())
}

fn gcd_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.is_empty() {
        return Ok(Value::Integer(0));
    }
    let mut result = match input[0] {
        Value::Integer(i) => i.abs(),
        _ => return Err("gcd expects integers".to_string())
    };
    for i in 1..input.len() {
        match input[i] {
            Value::Integer(val) => {
                result = gcd(result, val.abs());
            },
            _ => return Err("gcd expects integers".to_string())
        }
    }
    Ok(Value::Integer(result))
}

fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

fn lcm_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.is_empty() {
        return Ok(Value::Integer(1));
    }
    let mut result = match input[0] {
        Value::Integer(i) => i.abs(),
        _ => return Err("lcm expects integers".to_string())
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
            _ => return Err("lcm expects integers".to_string())
        }
    }
    Ok(Value::Integer(result))
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

fn max_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.is_empty() { return Err("max expects at least 1 argument".to_string()); }
    let mut max_val = input[0].clone();
    for i in 1..input.len() {
        if let Some(ord) = compare(&input[i], &max_val) {
            if ord == std::cmp::Ordering::Greater {
                max_val = input[i].clone();
            }
        } else {
            return Err("max expects numbers".to_string());
        }
    }
    Ok(max_val)
}

fn min_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.is_empty() { return Err("min expects at least 1 argument".to_string()); }
    let mut min_val = input[0].clone();
    for i in 1..input.len() {
        if let Some(ord) = compare(&input[i], &min_val) {
            if ord == std::cmp::Ordering::Less {
                min_val = input[i].clone();
            }
        } else {
            return Err("min expects numbers".to_string());
        }
    }
    Ok(min_val)
}
