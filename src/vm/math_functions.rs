use super::{compiler::Compiler, vp::Value, vp::ValueKind, vp::VmContext};

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

fn get_float(v: &Value) -> Option<f32> {
    match v.kind() {
        ValueKind::Float(f) => Some(f),
        ValueKind::Integer(i) => Some(i as f32),
        _ => None
    }
}

fn sin_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::float(f.sin()));
        }
    }
    Err("sin expects 1 number argument".to_string())
}

fn cos_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::float(f.cos()));
        }
    }
    Err("cos expects 1 number argument".to_string())
}

fn tan_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::float(f.tan()));
        }
    }
    Err("tan expects 1 number argument".to_string())
}

fn asin_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::float(f.asin()));
        }
    }
    Err("asin expects 1 number argument".to_string())
}

fn acos_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::float(f.acos()));
        }
    }
    Err("acos expects 1 number argument".to_string())
}

fn atan_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::float(f.atan()));
        }
    } else if input.len() == 2 {
        if let (Some(y), Some(x)) = (get_float(&input[0]), get_float(&input[1])) {
            return Ok(Value::float(y.atan2(x)));
        }
    }
    Err("atan expects 1 or 2 number arguments".to_string())
}

fn sqrt_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            if f < 0.0 { return Err("sqrt expects non-negative argument".to_string()); }
            return Ok(Value::float(f.sqrt()));
        }
    }
    Err("sqrt expects 1 number argument".to_string())
}

fn exp_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            return Ok(Value::float(f.exp()));
        }
    }
    Err("exp expects 1 number argument".to_string())
}

fn log_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        if let Some(f) = get_float(&input[0]) {
            if f <= 0.0 { return Err("log expects positive argument".to_string()); }
            return Ok(Value::float(f.ln()));
        }
    }
    Err("log expects 1 number argument".to_string())
}

fn expt_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 2 {
        if let (Some(b), Some(e)) = (get_float(&input[0]), get_float(&input[1])) {
            return Ok(Value::float(b.powf(e)));
        }
    }
    Err("expt expects 2 number arguments".to_string())
}

fn abs_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        match input[0].kind() {
            ValueKind::Float(f) => Ok(Value::float(f.abs())),
            ValueKind::Integer(i) => Ok(Value::integer(i.abs())),
            _ => Err("abs expects a number".to_string())
        }
    } else {
        Err("abs expects 1 argument".to_string())
    }
}

fn floor_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        match input[0].kind() {
            ValueKind::Float(f) => Ok(Value::float(f.floor())),
            ValueKind::Integer(i) => Ok(Value::integer(i)),
            _ => Err("floor expects a number".to_string())
        }
    } else {
        Err("floor expects 1 argument".to_string())
    }
}

fn ceiling_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        match input[0].kind() {
            ValueKind::Float(f) => Ok(Value::float(f.ceil())),
            ValueKind::Integer(i) => Ok(Value::integer(i)),
            _ => Err("ceiling expects a number".to_string())
        }
    } else {
        Err("ceiling expects 1 argument".to_string())
    }
}

fn truncate_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        match input[0].kind() {
            ValueKind::Float(f) => Ok(Value::float(f.trunc())),
            ValueKind::Integer(i) => Ok(Value::integer(i)),
            _ => Err("truncate expects a number".to_string())
        }
    } else {
        Err("truncate expects 1 argument".to_string())
    }
}

fn round_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 1 {
        match input[0].kind() {
            ValueKind::Float(f) => Ok(Value::float(f.round())),
            ValueKind::Integer(i) => Ok(Value::integer(i)),
            _ => Err("round expects a number".to_string())
        }
    } else {
        Err("round expects 1 argument".to_string())
    }
}

fn quotient_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 2 {
        if let (ValueKind::Integer(n1), ValueKind::Integer(n2)) = (input[0].kind(), input[1].kind()) {
            if n2 == 0 { return Err("division by zero".to_string()); }
            return Ok(Value::integer(n1 / n2));
        }
    }
    Err("quotient expects 2 integers".to_string())
}

fn remainder_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 2 {
        if let (ValueKind::Integer(n1), ValueKind::Integer(n2)) = (input[0].kind(), input[1].kind()) {
            if n2 == 0 { return Err("division by zero".to_string()); }
            return Ok(Value::integer(n1 % n2));
        }
    }
    Err("remainder expects 2 integers".to_string())
}

fn modulo_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.len() == 2 {
        if let (ValueKind::Integer(n1), ValueKind::Integer(n2)) = (input[0].kind(), input[1].kind()) {
            if n2 == 0 { return Err("division by zero".to_string()); }
            let rem = n1 % n2;
            if (rem < 0 && n2 > 0) || (rem > 0 && n2 < 0) {
                return Ok(Value::integer(rem + n2));
            }
            return Ok(Value::integer(rem));
        }
    }
    Err("modulo expects 2 integers".to_string())
}

fn gcd_impl(_ctx: &mut dyn VmContext, input: &[Value]) -> Result<Value, String> {
    if input.is_empty() {
        return Ok(Value::integer(0));
    }
    let mut result = match input[0].kind() {
        ValueKind::Integer(i) => i.abs(),
        _ => return Err("gcd expects integers".to_string())
    };
    for i in 1..input.len() {
        match input[i].kind() {
            ValueKind::Integer(val) => {
                result = gcd(result, val.abs());
            },
            _ => return Err("gcd expects integers".to_string())
        }
    }
    Ok(Value::integer(result))
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
        return Ok(Value::integer(1));
    }
    let mut result = match input[0].kind() {
        ValueKind::Integer(i) => i.abs(),
        _ => return Err("lcm expects integers".to_string())
    };
    for i in 1..input.len() {
        match input[i].kind() {
            ValueKind::Integer(val) => {
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
    Ok(Value::integer(result))
}

fn compare(v1: &Value, v2: &Value) -> Option<std::cmp::Ordering> {
    match (v1.kind(), v2.kind()) {
        (ValueKind::Integer(i1), ValueKind::Integer(i2)) => Some(i1.cmp(&i2)),
        (ValueKind::Float(f1), ValueKind::Float(f2)) => f1.partial_cmp(&f2),
        (ValueKind::Integer(i), ValueKind::Float(f)) => (i as f32).partial_cmp(&f),
        (ValueKind::Float(f), ValueKind::Integer(i)) => f.partial_cmp(&(i as f32)),
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
