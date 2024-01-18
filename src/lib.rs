pub mod lexer;
pub mod parser;
pub mod instructions;
pub mod expr_interpreter;
pub mod vm;

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;