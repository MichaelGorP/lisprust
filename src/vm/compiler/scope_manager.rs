use std::collections::HashMap;
use case_insensitive_hashmap::CaseInsensitiveHashMap;
use super::CompilationError;

pub struct CompilationScope {
    pub last_used_reg: u8,
    pub max_used_registers: u8,
    pub fixed_registers: u8,
    pub symbols: CaseInsensitiveHashMap<u8>,
    pub aliases: HashMap<u8, u8>
}

struct SymbolInterner {
    lookup: CaseInsensitiveHashMap<i64>,
    last_id: i64
}

impl SymbolInterner {
    fn new() -> SymbolInterner {
        SymbolInterner{lookup: CaseInsensitiveHashMap::new(), last_id: 0}
    }

    fn get_or_intern(&mut self, symbol: &str) -> i64 {
        *self.lookup.entry(symbol).or_insert_with(|| { self.last_id += 1; self.last_id })
    }
}

pub struct ScopeManager {
    pub last_used_reg: u8,
    pub fixed_registers: u8,
    pub max_used_registers: u8,
    pub symbols: CaseInsensitiveHashMap<u8>,
    pub aliases: HashMap<u8, u8>,
    interner: SymbolInterner,
    pub scope_stack: Vec<CompilationScope>
}

impl ScopeManager {
    const MAX_REG: u8 = 255;

    pub fn new() -> ScopeManager {
        ScopeManager {
            last_used_reg: 0,
            fixed_registers: 0,
            max_used_registers: 0,
            symbols: CaseInsensitiveHashMap::new(),
            aliases: HashMap::new(),
            interner: SymbolInterner::new(),
            scope_stack: Vec::new()
        }
    }

    pub fn begin_scope(&mut self) {
        let mut new_symbols = CaseInsensitiveHashMap::new();
        std::mem::swap(&mut self.symbols, &mut new_symbols);
        let mut new_aliases = HashMap::new();
        std::mem::swap(&mut self.aliases, &mut new_aliases);
        let current_scope = CompilationScope{last_used_reg: self.last_used_reg, max_used_registers: self.max_used_registers, fixed_registers: self.fixed_registers, symbols: new_symbols, aliases: new_aliases};
        self.scope_stack.push(current_scope);
        self.last_used_reg = 0;
        self.max_used_registers = 0;
    }

    pub fn end_scope(&mut self) {
        if let Some(last_scope) = self.scope_stack.pop() {
            self.last_used_reg = last_scope.last_used_reg;
            self.fixed_registers = last_scope.fixed_registers;
            self.max_used_registers = last_scope.max_used_registers;
            self.symbols = last_scope.symbols;
            self.aliases = last_scope.aliases;
        }
    }

    pub fn find_or_alloc(&mut self, symbol: &str) -> Result<u8, CompilationError> {
        if let Some(reg) = self.find_symbol(symbol) {
            return Ok(reg);
        }
        let reg = self.allocate_reg()?;
        self.symbols.insert(symbol, reg);
        Ok(reg)
    }

    pub fn find_symbol(&self, symbol: &str) -> Option<u8> {
        if let Some(reg) = self.symbols.get(symbol) {
            return Some(*reg);
        }
        for scope in self.scope_stack.iter().rev() {
            if let Some(reg) = scope.symbols.get(symbol) {
                return Some(*reg);
            }
        }
        None
    }

    pub fn allocate_reg(&mut self) -> Result<u8, CompilationError> {
        if self.last_used_reg < ScopeManager::MAX_REG {
            let reg = self.last_used_reg;
            self.last_used_reg += 1;
            self.max_used_registers = std::cmp::max(self.max_used_registers, self.last_used_reg);
            Ok(reg)
        }
        else {
            Err(CompilationError::from("Maximum number of registers exceeded"))
        }
    }

    pub fn reset_reg(&mut self, reg: u8) {
        if reg >= self.fixed_registers {
            self.last_used_reg = reg;
        }
    }

    pub fn get_or_intern_symbol(&mut self, symbol: &str) -> i64 {
        self.interner.get_or_intern(symbol)
    }
}
