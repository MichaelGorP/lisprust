use std::fmt;
use std::fmt::Write;
use std::error::Error;
use case_insensitive_hashmap::CaseInsensitiveHashMap;

use crate::{parser::SExpression, parser::{Atom, Lambda}, instructions};

macro_rules! binary_op {
    ($remainder:ident, $self:ident, $env:ident, $op:tt) => {
        {
            let mut ires: i64 = 0;
            let mut fres: f64 = 0.0;
            let mut eval_float = false;
            
            let first = $self.execute_to_numeric(&$remainder[0], $env);
            if first.is_none() {
                return Err(ExecutionError::from("Unexpected type"));
            }
            let first_lit = first.unwrap();
            if let Numeric::Integer(lit) = first_lit {
                ires = lit;
            }
            else if let Numeric::Float(lit) = first_lit {
                fres = lit;
                eval_float = true;
            }
            else {
                return Err(ExecutionError::from("Unexpected type"));
            }
            let mut i = 1;
            while i < $remainder.len() {
                let arg = &$remainder[i];
                let value = $self.execute_to_numeric(arg, $env);
                if value.is_none() {
                    return Err(ExecutionError::from("Unexpected type"));
                }
                else {
                    match value.unwrap() {
                        Numeric::Integer(n) => {
                            if eval_float {
                                fres $op n as f64;
                            }
                            else {
                                ires $op n;
                            }
                        },
                        Numeric::Float(n) => {
                            if eval_float {
                                fres $op n;
                            }
                            else {
                                fres = ires as f64;
                                fres $op n;
                                eval_float = true;
                            }
                        }
                    }
                }
                i += 1;
            }
            if eval_float {
                Ok(SExpression::Atom(Atom::Float(fres)))
            }
            else {
                Ok(SExpression::Atom(Atom::Integer(ires)))
            }
        }
    }
}

macro_rules! comparison_op {
    ($self: ident, $remainder: ident, $env: ident, $op: tt) => {
        {
            if $remainder.len() != 2 {
                return Err(ExecutionError::from("Expected 2 arguments"));
            }
            let op1 = $self.execute_to_numeric(&$remainder[0], $env);
            if op1.is_none() {
                let mut err = String::new();
                write!(&mut err, "Expected a number, got {}", $remainder[0])?;
                return Err(ExecutionError::from(err.as_str()));
            }
            let op2 = $self.execute_to_numeric(&$remainder[1], $env);
            if op2.is_none() {
                let mut err = String::new();
                write!(&mut err, "Expected a number, got {}", $remainder[1])?;
                return Err(ExecutionError::from(err.as_str()));
            }
            match (op1.unwrap(), op2.unwrap()) {
                (Numeric::Integer(lhs), Numeric::Integer(rhs)) => Ok(SExpression::Atom(Atom::Boolean(lhs $op rhs))),
                (Numeric::Integer(lhs), Numeric::Float(rhs)) => Ok(SExpression::Atom(Atom::Boolean((lhs as f64) $op rhs))),
                (Numeric::Float(lhs), Numeric::Integer(rhs)) => Ok(SExpression::Atom(Atom::Boolean(lhs $op rhs as f64))),
                (Numeric::Float(lhs), Numeric::Float(rhs)) => Ok(SExpression::Atom(Atom::Boolean(lhs $op rhs))),
            }
        }
    };
}

enum Numeric {
    Integer(i64),
    Float(f64)
}

#[derive(Debug)]
pub struct ExecutionError {
    err: String
}

impl ExecutionError {
    fn from(msg: &str) -> ExecutionError {
        ExecutionError{err: msg.to_string()}
    }
}

impl fmt::Display for ExecutionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.err)
    }
}

impl Error for ExecutionError {
    fn description(&self) -> &str {
        &self.err
    }
}

impl From<fmt::Error> for ExecutionError {
    fn from(value: fmt::Error) -> ExecutionError {
        ExecutionError{err: value.to_string()}
    }
}


struct Env<'a> {
    parent: Option<&'a Env<'a>>,
    symbols: CaseInsensitiveHashMap<SExpression>
}

impl<'a> Env<'a> {
    fn lookup(&self, symbol: &str) -> Option<&SExpression> {
        let value = self.symbols.get(symbol);
        value.or_else(|| if let Some(par) = self.parent {
                return par.lookup(symbol);
            }
            else {
                return None;
            }
        )
    }

    fn put(&mut self, symbol: String, expr: SExpression) {
        self.symbols.insert(symbol, expr);
    }
}

pub struct Interpreter {

}

impl Interpreter {
    pub fn new() -> Interpreter {
        let interpreter = Interpreter{};
        interpreter
    }

    pub fn execute(&self, root: &SExpression) -> Result<SExpression, ExecutionError> {
        let mut env = Env{symbols: CaseInsensitiveHashMap::new(), parent: None};
        self.execute_expr(root, &[], &mut env)
    }

    fn execute_expr(&self, root: &SExpression, args: &[SExpression], env: &mut Env) -> Result<SExpression, ExecutionError> {
        match root {
            SExpression::Atom(l) => Ok(SExpression::Atom(l.clone())),
            SExpression::BuiltIn(b) => todo!(),
            SExpression::Symbol(s) => {
                let value = env.lookup(s);
                if value.is_none() {
                    return Err(ExecutionError{err: "Undefined indentifier: ".to_string() + s});
                }
                else {
                    return self.execute_expr(&value.unwrap().clone(), &[], env);
                }
            },
            SExpression::List(l) => self.execute_list(l, env),
            SExpression::Lambda(lambda) => {
                if lambda.args.len() != args.len() {
                    Err(ExecutionError::from("Argument count mismatch"))
                }
                else {
                    let mut local_symbols = CaseInsensitiveHashMap::new();
                    for (expr, s) in std::iter::zip(args, &lambda.args){
                        let val = self.execute_expr(expr, &[], env)?;
                        local_symbols.insert(s.clone(), val);
                    }
                    let mut local_env = Env{symbols: local_symbols, parent: Some(env)};
                    self.execute_expr(&lambda.body, &[], &mut local_env)
                }
            },
        }
    }

    fn execute_to_numeric(&self, expr: &SExpression, env: &mut Env) -> Option<Numeric> {
        match expr {
            SExpression::Atom(lit) => {
                match lit {
                    Atom::Integer(i) => Some(Numeric::Integer(*i)),
                    Atom::Float(f) => Some(Numeric::Float(*f)),
                    _ => None
                }
            },
            SExpression::Symbol(sym) => {
                let value = env.lookup(sym);
                if let Some(val) = value {
                    self.execute_to_numeric(&val.clone(), env)
                }
                else {
                    None
                }
            },
            SExpression::List(l) => {
                let ret = self.execute_list(l, env);
                if let Ok(expr) = ret {
                    self.execute_to_numeric(&expr, env)
                }
                else {
                    None
                }
            }
            _ => None
        }
    }

    fn execute_list(&self, list: &[SExpression], env: &mut Env) -> Result<SExpression, ExecutionError> {
        if !list.is_empty() {
            let expr = &list[0];
            match expr {
                SExpression::Atom(l) => {return Ok(SExpression::Atom(l.clone()))},
                SExpression::BuiltIn(instr) => {
                    return self.execute_builtin(instr, &list[1..], env);
                },
                SExpression::Symbol(s) => {
                    let sym_val = env.lookup(s);
                    if sym_val.is_none() {
                        Err(ExecutionError{err: "Unknown identifier: ".to_string() + s})
                    }
                    else {
                        self.execute_expr(&sym_val.unwrap().clone(), &list[1..], env)
                    }
                },
                SExpression::List(l) => {
                     let ret = self.execute_list(l, env);
                     if list.len() == 1 {
                        return ret;
                     }
                     else {
                        return self.execute_list(&list[1..], env);
                     }
                },
                SExpression::Lambda(_) => todo!()
            }
        }
        else {
            Err(ExecutionError::from("Empty list"))
        }
    }

    fn execute_builtin(&self, instr: &instructions::Instruction, remainder: &[SExpression], env: &mut Env) -> Result<SExpression, ExecutionError> {
        if remainder.is_empty() {
            return Err(ExecutionError::from("Empty list"));
        }
        match instr {
            instructions::Instruction::Define => {
                if remainder.len() != 2 {
                    return Err(ExecutionError::from("Expected 2 arguments"));
                }
                if let SExpression::Symbol(ref sym) = remainder[0] {
                    let value = self.execute_expr(&remainder[1], &[], env)?;
                    env.put(sym.clone(), value);
                    return Ok(SExpression::List(vec![]));
                }
                return Err(ExecutionError::from("Expected a symbol name"));
            },
            &instructions::Instruction::Lambda => {
                //expect two lists for now
                if remainder.len() != 2 {
                    return Err(ExecutionError::from("Expected 2 arguments"));
                }
                let mut args;
                if let SExpression::List(arg_list) = &remainder[0] {
                    args = Vec::new();
                    for name in arg_list {
                        if let SExpression::Symbol(name_sym) = name {
                            args.push(name_sym.clone());
                        }
                    }
                }
                else {
                    return Err(ExecutionError::from("Expected parameter list"));
                }

                let lambda = Lambda{args: args, body : remainder[1].clone()};
                return Ok(SExpression::Lambda(Box::new(lambda)));
            },
            instructions::Instruction::If => {
                if remainder.len() != 3 {
                    return Err(ExecutionError::from("Expected 3 arguments"));
                }
                let cond_result = self.execute_expr(&remainder[0], &[], env)?;
                if let SExpression::Atom(Atom::Boolean(b)) = cond_result {
                    if b {
                        return self.execute_expr(&remainder[1], &[], env);
                    }
                    else {
                        return self.execute_expr(&remainder[2], &[], env);
                    }
                }
                else {
                    return Err(ExecutionError::from("Expected a boolean"));
                }
            },
            instructions::Instruction::Not => {
                if remainder.len() != 1 {
                    return Err(ExecutionError::from("Expected 1 argument"));
                }
                let value = self.execute_expr(&remainder[0], &[], env)?;
                if let SExpression::Atom(Atom::Boolean(b)) = value {
                    return Ok(SExpression::Atom(Atom::Boolean(!b)));
                }
                else {
                    return Err(ExecutionError::from("Expected a boolean"));
                }
            },
            instructions::Instruction::And => todo!(),
            instructions::Instruction::Or => todo!(),
            instructions::Instruction::Plus => binary_op!(remainder, self, env, +=),
            instructions::Instruction::Minus => binary_op!(remainder, self, env, -=),
            instructions::Instruction::Multiply => binary_op!(remainder, self, env, *=),
            instructions::Instruction::Divide => binary_op!(remainder, self, env, /=),
            instructions::Instruction::Eq => comparison_op!(self, remainder, env, ==),
            instructions::Instruction::Lt => comparison_op!(self, remainder, env, <),
            instructions::Instruction::Gt => comparison_op!(self, remainder, env, >),
            instructions::Instruction::Leq => comparison_op!(self, remainder, env, <=),
            instructions::Instruction::Geq => comparison_op!(self, remainder, env, >=),
        }
    }
}