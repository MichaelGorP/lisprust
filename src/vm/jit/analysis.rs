use std::collections::{HashMap, HashSet};
use crate::vm::vp::{Instr, JumpCondition, VirtualProgram};
use super::jit_types::JitType;

pub fn analyze_function(prog: &mut VirtualProgram, start_addr: u64, end_addr: u64, param_count: u8) -> Option<(Vec<JitType>, JitType, HashMap<usize, JitType>)> {
    let original_pos = prog.cursor.position();
    let mut has_float = false;
    let mut defined_regs = HashSet::new();
    let mut used_regs = HashSet::new();
    
    for i in 0..param_count {
        defined_regs.insert(i as usize);
    }
    
    let mut worklist = vec![start_addr];
    let mut visited = HashSet::new();
    
    while let Some(addr) = worklist.pop() {
        if visited.contains(&addr) { continue; }
        visited.insert(addr);
        
        prog.cursor.set_position(addr);
        
        loop {
            if prog.cursor.position() >= end_addr { break; }
            let opcode = match prog.read_opcode() {
                Some(o) => o,
                None => break,
            };
            let instr: Instr = match opcode[0].try_into() {
                Ok(i) => i,
                Err(_) => break,
            };
            
            match instr {
                Instr::LoadFloat => {
                    has_float = true;
                    prog.read_float();
                    defined_regs.insert(opcode[1] as usize);
                },
                Instr::LoadString | Instr::LoadSymbol => { 
                    prog.read_string(); 
                    defined_regs.insert(opcode[1] as usize);
                },
                Instr::LoadInt | Instr::LoadGlobal | Instr::Define => { 
                    prog.read_int(); 
                    defined_regs.insert(opcode[1] as usize);
                },
                Instr::LoadBool | Instr::LoadNil => {
                    defined_regs.insert(opcode[1] as usize);
                },
                Instr::CopyReg => {
                    used_regs.insert(opcode[2] as usize);
                    defined_regs.insert(opcode[1] as usize);
                },
                Instr::Add | Instr::Sub | Instr::Mul | Instr::Div | Instr::Eq | Instr::Neq | Instr::Lt | Instr::Gt | Instr::Leq | Instr::Geq => {
                    used_regs.insert(opcode[2] as usize);
                    used_regs.insert(opcode[3] as usize);
                    defined_regs.insert(opcode[1] as usize);
                },
                Instr::Not => {
                    used_regs.insert(opcode[2] as usize);
                    defined_regs.insert(opcode[1] as usize);
                        // Check for fused jump
                        let pos = prog.cursor.position();
                        if let Some(next_op) = prog.read_opcode() {
                            if let Ok(Instr::Jump) = next_op[0].try_into() {
                                let dist = prog.read_int().unwrap_or(0);
                                let target = (prog.cursor.position() as i64 + dist) as u64;
                                worklist.push(target);
                                // Jump is conditional (fused with Not), so we also fall through
                            } else {
                                prog.cursor.set_position(pos);
                            }
                        }
                },
                Instr::Jump => { 
                    let dist = prog.read_int().unwrap_or(0);
                    let target = (prog.cursor.position() as i64 + dist) as u64;
                    worklist.push(target);
                    
                    if opcode[2] == JumpCondition::Jump as u8 { // Unconditional
                        break; // Stop scanning this block
                    } else {
                        // Conditional
                        used_regs.insert(opcode[1] as usize);
                    }
                },
                Instr::LoadFuncRef => { return None; },
                Instr::MakeClosure => { return None; },
                Instr::TailCallSymbol => {
                    used_regs.insert(opcode[1] as usize);
                    break; // Tail call ends block
                },
                Instr::CallSymbol => {
                    used_regs.insert(opcode[1] as usize);
                    defined_regs.insert(opcode[3] as usize);
                },
                Instr::CallFunction => {
                    return None;
                },
                Instr::Ret => {
                    // Ret uses result_reg from header, but we don't have header here.
                    // Assuming result_reg is defined.
                    break;
                },
                _ => {}
            }
        }
    }
    
    prog.cursor.set_position(original_pos);
    
    // Check for captures
    for reg in used_regs {
        if !defined_regs.contains(&reg) {
            // println!("Capture check failed for reg {}", reg);
            return None;
        }
    }
    
    let main_type = if has_float { JitType::Float } else { JitType::Int };
    let reg_types = HashMap::new();
    let mut params = Vec::new();
    
    for _ in 0..param_count {
        params.push(main_type);
    }
    
    Some((params, main_type, reg_types))
}

pub fn scan_function_end(prog: &mut VirtualProgram, start_addr: u64) -> u64 {
    let original = prog.cursor.position();
    prog.cursor.set_position(start_addr);
    loop {
        let opcode = match prog.read_opcode() {
            Some(o) => o,
            None => break,
        };
        let instr: Result<Instr, _> = opcode[0].try_into();
        if let Ok(Instr::Ret) = instr {
            // Ret marks the end of the function in this simple JIT.
        }
    }
    
    // Perform a basic block traversal to find the maximum reachable address.
    let mut max_addr = start_addr;
    let mut worklist = vec![start_addr];
    let mut visited = HashSet::new();
    
    while let Some(addr) = worklist.pop() {
        if visited.contains(&addr) { continue; }
        visited.insert(addr);
        if addr > max_addr { max_addr = addr; }
        
        prog.cursor.set_position(addr);
        loop {
            let pos = prog.cursor.position();
            if pos > max_addr { max_addr = pos; }
            
            let opcode = match prog.read_opcode() {
                Some(o) => o,
                None => break,
            };
            let instr: Instr = match opcode[0].try_into() {
                Ok(i) => i,
                Err(_) => break,
            };
            
            match instr {
                Instr::Jump => {
                    let dist = prog.read_int().unwrap_or(0);
                    let target = (prog.cursor.position() as i64 + dist) as u64;
                    worklist.push(target);
                    if opcode[2] == JumpCondition::Jump as u8 { break; }
                },
                Instr::Not => {
                        if let Some(next) = prog.read_opcode() {
                            if let Ok(Instr::Jump) = next[0].try_into() {
                                let dist = prog.read_int().unwrap_or(0);
                                let target = (prog.cursor.position() as i64 + dist) as u64;
                                worklist.push(target);
                            } else {
                                prog.cursor.set_position(pos + 1 + 8); // Skip Not opcode + args
                            }
                        }
                },
                Instr::Ret => break,
                _ => {
                    // Advance cursor
                    match instr {
                        Instr::LoadInt | Instr::LoadFloat | Instr::LoadGlobal | Instr::Define | Instr::LoadFuncRef => { prog.read_int(); },
                        Instr::LoadString | Instr::LoadSymbol => { prog.read_string(); },
                        _ => {}
                    }
                }
            }
        }
    }
    prog.cursor.set_position(original);
    max_addr + 1 // Approximate
}
