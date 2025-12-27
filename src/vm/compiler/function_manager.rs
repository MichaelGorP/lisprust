use std::collections::HashMap;
use crate::vm::vp::VmCallableFunction;

pub struct FunctionRegistry {
    pub registered_functions: HashMap<String, VmCallableFunction>,
    pub used_functions: Vec<VmCallableFunction>,
    pub function_lookup: HashMap<String, usize>,
}

impl FunctionRegistry {
    pub fn new() -> FunctionRegistry {
        FunctionRegistry {
            registered_functions: HashMap::new(),
            used_functions: Vec::new(),
            function_lookup: HashMap::new(),
        }
    }

    pub fn register_function(&mut self, name: &str, func: VmCallableFunction) {
        self.registered_functions.insert(name.into(), func);
    }

    pub fn get_registered_function(&self, name: &str) -> Option<VmCallableFunction> {
        self.registered_functions.get(name).copied()
    }

    pub fn get_or_insert_used_function(&mut self, name: &str, func: VmCallableFunction) -> usize {
        *self.function_lookup.entry(name.to_string()).or_insert_with(|| {
            self.used_functions.push(func);
            self.used_functions.len()
        })
    }

    pub fn take_used_functions(&mut self) -> Vec<VmCallableFunction> {
        let mut new_functions = Vec::new();
        std::mem::swap(&mut self.used_functions, &mut new_functions);
        self.function_lookup.clear();
        new_functions
    }
}
