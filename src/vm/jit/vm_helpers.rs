use std::cell::Cell;
use crate::vm::vm::{Vm, CallState};
use crate::vm::vp::{VirtualProgram, Value as LispValue, ValueKind, FunctionHeader, FunctionData, HeapValue, ClosureData, Instr, Pair};

pub unsafe extern "C" fn helper_check_self_recursion(vm: *mut Vm, func_reg: usize, start_addr: u64) -> i32 {
    let vm = &mut *vm;
    let func = vm.registers[vm.window_start + func_reg];
    
    let address = if let ValueKind::Object(handle) = func.kind() {
        match vm.heap.get(handle) {
            Some(HeapValue::FuncRef(f)) => f.address,
            Some(HeapValue::Closure(c)) => c.function.address,
            Some(HeapValue::Ref(inner)) => {
                if let ValueKind::Object(inner_handle) = inner.kind() {
                    match vm.heap.get(inner_handle) {
                        Some(HeapValue::FuncRef(f)) => f.address,
                        Some(HeapValue::Closure(c)) => c.function.address,
                        _ => return 0
                    }
                } else {
                    return 0;
                }
            },
            _ => return 0
        }
    } else {
        return 0;
    };
    
    if address == start_addr { 1 } else { 0 }
}

pub unsafe extern "C" fn helper_op(vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut LispValue, opcode_val: u32) {
    let opcode = opcode_val.to_le_bytes();
    let vm = &mut *vm;

    macro_rules! jit_binary_op {
        ($op:tt) => {
            {
                 let v1 = resolve_value(vm, registers, opcode[2]);
                 let v2 = resolve_value(vm, registers, opcode[3]);
                 let res_reg = opcode[1] as usize;
                 
                 match (v1.kind(), v2.kind()) {
                    (ValueKind::Integer(lhs), ValueKind::Integer(rhs)) => *registers.add(res_reg) = LispValue::integer(lhs $op rhs),
                    (ValueKind::Integer(lhs), ValueKind::Float(rhs)) => *registers.add(res_reg) = LispValue::float(lhs as f32 $op rhs),
                    (ValueKind::Float(lhs), ValueKind::Float(rhs)) => *registers.add(res_reg) = LispValue::float(lhs $op rhs),
                    (ValueKind::Float(lhs), ValueKind::Integer(rhs)) => *registers.add(res_reg) = LispValue::float(lhs $op rhs as f32),
                    (_v1, _v2) => {
                    } 
                 }
            }
        }
    }

    macro_rules! jit_comparison_op {
        ($op:tt) => {
            {
                 let v1 = resolve_value(vm, registers, opcode[2]);
                 let v2 = resolve_value(vm, registers, opcode[3]);
                 let res_reg = opcode[1] as usize;
                 
                 let matches = match (v1.kind(), v2.kind()) {
                    (ValueKind::Integer(lhs), ValueKind::Integer(rhs)) => lhs $op rhs,
                    (ValueKind::Integer(lhs), ValueKind::Float(rhs)) => (lhs as f32) $op rhs,
                    (ValueKind::Float(lhs), ValueKind::Float(rhs)) => lhs $op rhs,
                    (ValueKind::Float(lhs), ValueKind::Integer(rhs)) => lhs $op rhs as f32,
                    _ => false,
                 };
                 *registers.add(res_reg) = LispValue::boolean(matches);
            }
        }
    }
    
    match opcode[0].try_into() {
        Ok(Instr::Add) => jit_binary_op!(+),
        Ok(Instr::Sub) => jit_binary_op!(-),
        Ok(Instr::Mul) => jit_binary_op!(*),
        Ok(Instr::Div) => jit_binary_op!(/),
        Ok(Instr::Eq) => {
             let v1 = resolve_value(vm, registers, opcode[2]);
             let v2 = resolve_value(vm, registers, opcode[3]);
             let res_reg = opcode[1] as usize;
             *registers.add(res_reg) = LispValue::boolean(v1 == v2);
        },
        Ok(Instr::Neq) => {
             let v1 = resolve_value(vm, registers, opcode[2]);
             let v2 = resolve_value(vm, registers, opcode[3]);
             let res_reg = opcode[1] as usize;
             *registers.add(res_reg) = LispValue::boolean(v1 != v2);
        },
        Ok(Instr::Lt) => jit_comparison_op!(<),
        Ok(Instr::Gt) => jit_comparison_op!(>),
        Ok(Instr::Leq) => jit_comparison_op!(<=),
        Ok(Instr::Geq) => jit_comparison_op!(>=),
        Ok(Instr::Not) => {
             let v = resolve_value(vm, registers, opcode[2]);
             let res_reg = opcode[1] as usize;
             match v.kind() {
                 ValueKind::Boolean(b) => *registers.add(res_reg) = LispValue::boolean(!b),
                 _ => *registers.add(res_reg) = LispValue::boolean(false),
             }
        },
        Ok(Instr::CopyReg) => {
             let dest_reg = opcode[1] as usize;
             let src_reg = opcode[2] as usize;
             let val = (*registers.add(src_reg)).clone();

             *registers.add(dest_reg) = val;
        },
        Ok(Instr::LoadString) => {
             let prog = &mut *prog;
             if let Some(s) = prog.read_string() {
                 let dest_reg = opcode[1] as usize;
                 *registers.add(dest_reg) = LispValue::object(vm.heap.alloc(HeapValue::String(s)));
             }
        },
        Ok(Instr::LoadSymbol) => {
             let prog = &mut *prog;
             if let Some(s) = prog.read_string() {
                 let dest_reg = opcode[1] as usize;
                 *registers.add(dest_reg) = LispValue::object(vm.heap.alloc(HeapValue::Symbol(s)));
             }
        },
        Ok(Instr::LoadNil) => {
             let dest_reg = opcode[1] as usize;
             *registers.add(dest_reg) = LispValue::nil();
        },
        _ => {
        }
    }
}

pub unsafe extern "C" fn helper_check_condition(_vm: *mut Vm, registers: *mut LispValue, reg_idx: usize) -> i32 {
    let val = &*registers.add(reg_idx);
    if val.is_true() { 1 } else { 0 }
}

unsafe fn resolve_value(vm: &Vm, registers: *mut LispValue, reg_idx: u8) -> LispValue {
    let val = *registers.add(reg_idx as usize);
    if let ValueKind::Object(handle) = val.kind() {
        if let Some(HeapValue::Ref(inner)) = vm.heap.get(handle) {
            return *inner;
        }
    }
    val
}

pub unsafe extern "C" fn helper_load_global(vm: *mut Vm, registers: *mut LispValue, dest_reg: usize, sym_id: i64) {
    let vm = &mut *vm;
    
    if (sym_id as usize) < vm.global_vars.len() {
        let v = &mut vm.global_vars[sym_id as usize];
        *registers.add(dest_reg) = v.clone();
    } else {
        *registers.add(dest_reg) = LispValue::nil();
    }
}

pub unsafe extern "C" fn helper_define(vm: *mut Vm, registers: *mut LispValue, src_reg: usize, sym_id: i64) {
    let vm = &mut *vm;
    let val = (*registers.add(src_reg)).clone();
    if sym_id as usize >= vm.global_vars.len() {
        vm.global_vars.resize(sym_id as usize + 1, LispValue::nil());
    }
    vm.global_vars[sym_id as usize] = val;
}

pub unsafe extern "C" fn helper_load_func_ref(vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut LispValue, dest_reg: usize, header_addr: i64) {
    let vm = &mut *vm;
    let prog = &mut *prog;
    let header = prog.read_function_header(header_addr as u64).unwrap();
    let func_addr = header_addr as usize + std::mem::size_of::<FunctionHeader>();
    
    let jit_code = vm.jit.cache.get(&(func_addr as u64)).map(|&ptr| ptr as u64).unwrap_or(0);
    vm.collect_garbage();
    *registers.add(dest_reg) = LispValue::object(vm.heap.alloc(HeapValue::FuncRef(FunctionData{header, address: func_addr as u64, jit_code: Cell::new(jit_code), fast_jit_code: Cell::new(0)})));
}

pub unsafe extern "C" fn helper_call_function(vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut LispValue, dest_reg: usize, start_reg: usize, reg_count: usize, func_id: i64) {
    let vm = &mut *vm;
    let prog = &mut *prog;
    
    let Some(function) = prog.get_function(func_id) else { return };
    
    let args_slice = std::slice::from_raw_parts(registers.add(start_reg), reg_count);
    let args = args_slice.to_vec();
    
    match function(vm, &args) {
        Ok(val) => *registers.add(dest_reg) = val,
        Err(e) => panic!("Runtime error: {}", e),
    }
}

pub unsafe extern "C" fn helper_call_symbol(vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut LispValue, func_reg: usize, param_start: usize, target_reg: usize) {
    let vm = &mut *vm;
    let prog = &mut *prog;
    
    // println!("helper_call_symbol func_reg={} param_start={} target_reg={}", func_reg, param_start, target_reg);

    let resolved_func = resolve_value(vm, registers, func_reg as u8);
    
    let (header, address, captures, jit_code_cell, fast_jit_code_cell) = if let ValueKind::Object(handle) = resolved_func.kind() {
        match vm.heap.get(handle) {
            Some(HeapValue::FuncRef(f)) => (f.header, f.address, None, Some(&f.jit_code), Some(&f.fast_jit_code)),
            Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone()), Some(&c.function.jit_code), Some(&c.function.fast_jit_code)),
            Some(HeapValue::Ref(inner)) => {
                 if let ValueKind::Object(inner_handle) = inner.kind() {
                     match vm.heap.get(inner_handle) {
                        Some(HeapValue::FuncRef(f)) => (f.header, f.address, None, None, None),
                        Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone()), None, None),
                        _ => return
                     }
                 } else {
                     return
                 }
            },
            _ => return
        }
    } else {
        return
    };

    let size = param_start + header.register_count as usize + vm.window_start;
    if size >= vm.registers.len() {
        vm.registers.resize(size, LispValue::nil());
    }
    let old_ws = vm.window_start;
    let ret_addr = 0; 
    
    let state = CallState{window_start: old_ws, result_reg: header.result_reg, target_reg: target_reg as u8, return_addr: ret_addr};
    vm.call_states.push(state);
    
    vm.window_start += param_start;
    
    if let Some(caps) = captures {
        let start_reg = header.param_count as usize;
        for (i, val) in caps.into_iter().enumerate() {
            vm.registers[vm.window_start + start_reg + i] = val;
        }
    }
    
    let jit_code = jit_code_cell.map(|c| c.get()).unwrap_or(0);
    if jit_code != 0 {
         vm.tail_call_pending = true;
         vm.next_jit_code = jit_code;
    } else {
         let end_addr = super::analysis::scan_function_end(prog, address);
         match vm.jit.compile(&vm.global_vars, &vm.heap, prog, address, end_addr) {
             Ok(func) => {
                 if let Some(cell) = jit_code_cell {
                     if let Some(&code) = vm.jit.cache.get(&address) {
                         cell.set(code as u64);
                     }
                 }
                 if let Some(cell) = fast_jit_code_cell {
                     if let Some(&code) = vm.jit.fast_cache.get(&address) {
                         cell.set(code as u64);
                     }
                 }
                 
                 vm.tail_call_pending = true;
                 vm.next_jit_code = func as usize as u64;
             },
             Err(e) => {
                 println!("JIT compilation failed in call: {}", e);
                 
                 let eof = prog.get_bytecode().len() as u64;
                 if let Some(last) = vm.call_states.last_mut() {
                     last.return_addr = eof;
                 }
                 
                 prog.jump_to(address);
                 vm.run_debug(prog, None);
                 
                 let res_val = resolve_value(vm, registers, target_reg as u8);
                 println!("helper_call_symbol fallback done: target_reg={} val={:?}", target_reg, res_val);

                 vm.tail_call_pending = false;
                 return;
             }
         }
    }

    while vm.tail_call_pending {
        vm.tail_call_pending = false;
        let code = vm.next_jit_code;
        if code != 0 {
             let func: unsafe extern "C" fn(*mut Vm, *mut VirtualProgram, *mut LispValue) = std::mem::transmute(code as *const u8);
             func(vm, prog, vm.registers.as_mut_ptr().add(vm.window_start));
        }
    }
    
    let state = vm.call_states.pop().unwrap();
    let source_reg = vm.window_start + state.result_reg as usize;
    let target_reg = state.window_start + state.target_reg as usize;
    vm.registers.swap(source_reg, target_reg);
    
    vm.window_start = old_ws;
}


pub unsafe extern "C" fn helper_tail_call_symbol(vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut LispValue, func_reg: usize, param_start: usize) {
    let vm = &mut *vm;
    let prog = &mut *prog;

    // println!("helper_tail_call_symbol func_reg={} param_start={}", func_reg, param_start);
    // panic!("helper_tail_call_symbol called");

    let func = *registers.add(func_reg);
    
    let (header, address, captures, jit_code_cell) = match func.kind() {
        ValueKind::Object(handle) => match vm.heap.get(handle) {
            Some(HeapValue::FuncRef(f)) => (f.header, f.address, None, Some(&f.jit_code)),
            Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone()), Some(&c.function.jit_code)),
            Some(HeapValue::Ref(inner)) => {
                 if let ValueKind::Object(inner_handle) = inner.kind() {
                     match vm.heap.get(inner_handle) {
                        Some(HeapValue::FuncRef(f)) => (f.header, f.address, None, None),
                        Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone()), None),
                        _ => return
                     }
                 } else {
                     return
                 }
            },
            _ => return
        },
        _ => return
    };

    let size = vm.window_start + header.register_count as usize;
    if size >= vm.registers.len() {
        vm.registers.resize(size, LispValue::nil());
    }

    let param_count = header.param_count as usize;
    
    if param_start >= param_count {
        // Safe to copy directly
        for i in 0..param_count {
            let src_idx = vm.window_start + param_start + i;
            let dest_idx = vm.window_start + i;
            vm.registers[dest_idx] = vm.registers[src_idx].clone();
        }
    } else {
        vm.scratch_buffer.clear();
        for i in 0..param_count {
            let idx = vm.window_start + param_start + i;
            vm.scratch_buffer.push(vm.registers[idx].clone());
        }
        for (i, param) in vm.scratch_buffer.drain(..).enumerate() {
            let target_reg = vm.window_start + i;
            vm.registers[target_reg] = param;
        }
    }

    if let Some(last_frame) = vm.call_states.last_mut() {
        last_frame.result_reg = header.result_reg;
    }
    
    if let Some(caps) = captures {
        let start_reg = header.param_count as usize;
        for (i, val) in caps.into_iter().enumerate() {
            let target = vm.window_start + start_reg + i;
            vm.registers[target] = val;
        }
    }

    let jit_code = jit_code_cell.map(|c| c.get()).unwrap_or(0);
    if jit_code != 0 {
         vm.tail_call_pending = true;
         vm.next_jit_code = jit_code;
    } else {
         println!("Compiling tail call target at {}", address);
         let end_addr = super::analysis::scan_function_end(prog, address);
         if let Ok(func) = vm.jit.compile(&vm.global_vars, &vm.heap, prog, address, end_addr) {
             if let Some(cell) = jit_code_cell {
                 if let Some(&code) = vm.jit.cache.get(&address) {
                     cell.set(code as u64);
                 }
             }
             
             vm.tail_call_pending = true;
             vm.next_jit_code = func as usize as u64;
         } else {
             println!("JIT compilation failed in tail call");
         }
    }
}

pub unsafe extern "C" fn helper_make_closure(vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut LispValue, dest_reg: usize, func_reg: usize, count: usize, instr_addr: u64) {
    let vm = &mut *vm;
    let prog = &mut *prog;
    
    let old_pos = prog.current_address();
    prog.jump_to(instr_addr + 4); // Skip opcode (4)
    
    let mut captures = Vec::with_capacity(count);
    for _ in 0..count {
        let reg_idx = prog.read_byte().unwrap();
        // Cloning values for capture is necessary as they escape the current scope
        let val = *registers.add(reg_idx as usize);
        captures.push(val);
    }
    
    prog.jump_to(old_pos);
    
    let func_val = *registers.add(func_reg);
    
    if let ValueKind::Object(handle) = func_val.kind() {
        if let Some(HeapValue::FuncRef(fd)) = vm.heap.get(handle) {
            let fd_clone = fd.clone();
            for c in &captures {
                vm.scratch_buffer.push(*c);
            }
            vm.collect_garbage();
            for _ in &captures {
                vm.scratch_buffer.pop();
            }
            *registers.add(dest_reg) = LispValue::object(vm.heap.alloc(HeapValue::Closure(ClosureData{function: fd_clone, captures})));
        } else {
            *registers.add(dest_reg) = LispValue::nil();
        }
    } else {
        *registers.add(dest_reg) = LispValue::nil();
    }
}

pub unsafe extern "C" fn helper_make_ref(vm: *mut Vm, registers: *mut LispValue, dest_reg: usize) {
    let vm = &mut *vm;
    let val = *registers.add(dest_reg);
    vm.collect_garbage();
    *registers.add(dest_reg) = LispValue::object(vm.heap.alloc(HeapValue::Ref(val)));
}

pub unsafe extern "C" fn helper_set_ref(vm: *mut Vm, registers: *mut LispValue, dest_reg: usize, src_reg: usize) {
    let vm = &mut *vm;
    let dest = *registers.add(dest_reg);
    let src = *registers.add(src_reg);
    
    if let ValueKind::Object(handle) = dest.kind() {
        if let Some(HeapValue::Ref(r)) = vm.heap.get_mut(handle) {
            *r = src;
        }
    }
}

pub unsafe extern "C" fn helper_deref(vm: *mut Vm, registers: *mut LispValue, dest_reg: usize, src_reg: usize) {
    let vm = &mut *vm;
    let src = *registers.add(src_reg);
    
    let val = if let ValueKind::Object(handle) = src.kind() {
        if let Some(HeapValue::Ref(r)) = vm.heap.get(handle) {
            Some(*r)
        } else {
            None
        }
    } else {
        None
    };
    
    if let Some(v) = val {
        *registers.add(dest_reg) = v;
    } else {
        *registers.add(dest_reg) = src;
    }
}

pub unsafe extern "C" fn helper_get_registers_ptr(vm: *mut Vm) -> *mut LispValue {
    let vm = &mut *vm;
    vm.registers.as_mut_ptr().add(vm.window_start)
}

pub unsafe extern "C" fn helper_load_string(vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut LispValue, dest_reg: usize, offset: u64) {
    let vm = &mut *vm;
    let prog = &mut *prog;
    let bytecode = prog.get_bytecode();
    let offset = offset as usize;
    
    if offset + 8 <= bytecode.len() {
        let len_bytes = &bytecode[offset..offset+8];
        let len = i64::from_le_bytes(len_bytes.try_into().unwrap()) as usize;
        
        if offset + 8 + len <= bytecode.len() {
            let str_bytes = &bytecode[offset+8..offset+8+len];
            if let Ok(s) = std::str::from_utf8(str_bytes) {
                vm.collect_garbage();
                *registers.add(dest_reg) = LispValue::object(vm.heap.alloc(HeapValue::String(s.to_string())));
            }
        }
    }
}

pub unsafe extern "C" fn helper_load_symbol(vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut LispValue, dest_reg: usize, offset: u64) {
    let vm = &mut *vm;
    let prog = &mut *prog;
    let bytecode = prog.get_bytecode();
    let offset = offset as usize;
    
    if offset + 8 <= bytecode.len() {
        let len_bytes = &bytecode[offset..offset+8];
        let len = i64::from_le_bytes(len_bytes.try_into().unwrap()) as usize;
        
        if offset + 8 + len <= bytecode.len() {
            let str_bytes = &bytecode[offset+8..offset+8+len];
            if let Ok(s) = std::str::from_utf8(str_bytes) {
                vm.collect_garbage();
                let handle = if let Some(&h) = vm.symbol_table.get(s) {
                    h
                } else {
                    let h = vm.heap.alloc(HeapValue::Symbol(s.to_string()));
                    vm.symbol_table.insert(s.to_string(), h);
                    h
                };
                *registers.add(dest_reg) = LispValue::object(handle);
            }
        }
    }
}

pub unsafe extern "C" fn helper_car(vm: *mut Vm, registers: *mut LispValue, dest_reg: usize, arg_reg: usize) {
    let vm = &mut *vm;
    let arg = *registers.add(arg_reg);
    if let ValueKind::Object(handle) = arg.kind() {
        if let Some(HeapValue::Pair(p)) = vm.heap.get(handle) {
            *registers.add(dest_reg) = p.car;
        } else {
            panic!("Runtime error: car expects a pair");
        }
    } else {
        panic!("Runtime error: car expects a pair");
    }
}

pub unsafe extern "C" fn helper_cdr(vm: *mut Vm, registers: *mut LispValue, dest_reg: usize, arg_reg: usize) {
    let vm = &mut *vm;
    let arg = *registers.add(arg_reg);
    if let ValueKind::Object(handle) = arg.kind() {
        if let Some(HeapValue::Pair(p)) = vm.heap.get(handle) {
            *registers.add(dest_reg) = p.cdr;
        } else {
            panic!("Runtime error: cdr expects a pair");
        }
    } else {
        panic!("Runtime error: cdr expects a pair");
    }
}

pub unsafe extern "C" fn helper_cons(vm: *mut Vm, registers: *mut LispValue, dest_reg: usize, car_reg: usize, cdr_reg: usize) {
    let vm = &mut *vm;
    let car = *registers.add(car_reg);
    let cdr = *registers.add(cdr_reg);
    
    vm.scratch_buffer.push(car);
    vm.scratch_buffer.push(cdr);
    vm.collect_garbage();
    vm.scratch_buffer.pop();
    vm.scratch_buffer.pop();
    
    let handle = vm.heap.alloc(HeapValue::Pair(Pair { car, cdr }));
    *registers.add(dest_reg) = LispValue::object(handle);
}

pub unsafe extern "C" fn helper_is_pair(vm: *mut Vm, registers: *mut LispValue, dest_reg: usize, arg_reg: usize) {
    let vm = &mut *vm;
    let arg = *registers.add(arg_reg);
    let is_pair = if let ValueKind::Object(handle) = arg.kind() {
        matches!(vm.heap.get(handle), Some(HeapValue::Pair(_)))
    } else {
        false
    };
    *registers.add(dest_reg) = LispValue::boolean(is_pair);
}

pub unsafe extern "C" fn helper_is_null(registers: *mut LispValue, dest_reg: usize, arg_reg: usize) {
    let arg = *registers.add(arg_reg);
    *registers.add(dest_reg) = LispValue::boolean(arg.is_nil());
}

pub unsafe extern "C" fn helper_is_eq(registers: *mut LispValue, dest_reg: usize, arg1_reg: usize, arg2_reg: usize) {
    let arg1 = *registers.add(arg1_reg);
    let arg2 = *registers.add(arg2_reg);
    *registers.add(dest_reg) = LispValue::boolean(arg1 == arg2);
}

pub unsafe extern "C" fn helper_prepare_map(vm: *mut Vm, prog: *mut VirtualProgram, _registers: *mut LispValue, func_reg: usize, list_reg: usize, temp_reg: usize) -> u64 {
    let vm = &mut *vm;
    let prog = &mut *prog;
    
    let list_idx = vm.window_start + list_reg;
    if list_idx >= vm.registers.len() {
        return 0;
    }
    let list_val = vm.registers[list_idx];
    
    if list_val.is_nil() {
        return 0;
    }
    
    if let ValueKind::Object(handle) = list_val.kind() {
        if let Some(HeapValue::Pair(p)) = vm.heap.get(handle) {
            let car = p.car;
            let cdr = p.cdr;
            
            // Update list register with CDR
            vm.registers[list_idx] = cdr;
            
            let regs_ptr = vm.registers.as_mut_ptr().add(vm.window_start);
            let resolved_func = resolve_value(vm, regs_ptr, func_reg as u8);
            
            let (header, address, captures, jit_code_cell, fast_jit_code_cell) = if let ValueKind::Object(handle) = resolved_func.kind() {
                match vm.heap.get(handle) {
                    Some(HeapValue::FuncRef(f)) => (f.header, f.address, None, Some(&f.jit_code), Some(&f.fast_jit_code)),
                    Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone()), Some(&c.function.jit_code), Some(&c.function.fast_jit_code)),
                     Some(HeapValue::Ref(inner)) => {
                         if let ValueKind::Object(inner_handle) = inner.kind() {
                             match vm.heap.get(inner_handle) {
                                Some(HeapValue::FuncRef(f)) => (f.header, f.address, None, None, None),
                                Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone()), None, None),
                                _ => return 0
                             }
                         } else {
                             return 0
                         }
                     },
                    _ => return 0
                }
            } else {
                return 0
            };
            
            let param_start = temp_reg;
            let size = param_start + header.register_count as usize + vm.window_start;
            if size >= vm.registers.len() {
                vm.registers.resize(size, LispValue::nil());
            }
            let old_ws = vm.window_start;
            let ret_addr = 0;
            
            let state = CallState{window_start: old_ws, result_reg: header.result_reg, target_reg: temp_reg as u8, return_addr: ret_addr};
            vm.call_states.push(state);
            
            vm.window_start += param_start;
            
            if let Some(caps) = captures {
                let start_reg = header.param_count as usize;
                for (i, val) in caps.into_iter().enumerate() {
                    vm.registers[vm.window_start + start_reg + i] = val;
                }
            }
            
            vm.registers[vm.window_start] = car;
            
            let jit_code = jit_code_cell.map(|c| c.get()).unwrap_or(0);
            if jit_code != 0 {
                 return jit_code;
            } else {
                let end_addr = super::analysis::scan_function_end(prog, address);
                if let Ok(func) = vm.jit.compile(&vm.global_vars, &vm.heap, prog, address, end_addr) {
                     if let Some(cell) = jit_code_cell {
                         if let Some(&code) = vm.jit.cache.get(&address) {
                             cell.set(code as u64);
                         }
                     }
                     if let Some(cell) = fast_jit_code_cell {
                         if let Some(&code) = vm.jit.fast_cache.get(&address) {
                             cell.set(code as u64);
                         }
                     }
                     return func as usize as u64;
                }
                return 0;
            }
        }
    }
    0
}

pub unsafe extern "C" fn helper_ret(vm: *mut Vm) {
    let vm = &mut *vm;
    if let Some(state) = vm.call_states.pop() {
        let source_reg = vm.window_start + state.result_reg as usize;
        let target_reg = state.window_start + state.target_reg as usize;
        vm.registers.swap(source_reg, target_reg);
        vm.window_start = state.window_start;
    }
}


