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
                 let handle = if let Some(&h) = vm.symbol_table.get(&s) {
                     h
                 } else {
                     let h = vm.heap.alloc(HeapValue::Symbol(s.clone()));
                     vm.symbol_table.insert(s, h);
                     h
                 };
                 *registers.add(dest_reg) = LispValue::object(handle);
             }
        },
        Ok(Instr::LoadNil) => {
             let dest_reg = opcode[1] as usize;
             *registers.add(dest_reg) = LispValue::nil();
        },
        Ok(Instr::List) => {
             let dest_reg = opcode[1] as usize;
             let start_reg = opcode[2] as usize;
             let count = opcode[3] as usize;
             
             let mut last_node = LispValue::nil();
             for i in (0..count).rev() {
                 let val = *registers.add(start_reg + i);
                 let handle = vm.heap.alloc(HeapValue::Pair(Pair { car: val, cdr: last_node }));
                 last_node = LispValue::object(handle);
             }
             *registers.add(dest_reg) = last_node;
        },
        _ => {
        }
    }
}

pub unsafe extern "C" fn helper_list(vm: *mut Vm, registers: *mut LispValue, dest_reg: usize, start_reg: usize, count: usize) {
    let vm = &mut *vm;
    
    if count == 0 {
        *registers.add(dest_reg) = LispValue::nil();
        return;
    }

    let start_ptr = registers.add(start_reg);

    let first_handle = vm.heap.alloc_contiguous(count, |i, handle| {
        let val = *start_ptr.add(i);
        let next = if i == count - 1 {
            LispValue::nil()
        } else {
             LispValue::object(handle.offset(1))
        };
        HeapValue::Pair(Pair { car: val, cdr: next })
    });
    
    *registers.add(dest_reg) = LispValue::object(first_handle);
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
    
    let args = std::slice::from_raw_parts(registers.add(start_reg), reg_count);
    
    match function(vm, args) {
        Ok(val) => {
             let target_ptr = vm.registers.as_mut_ptr().add(vm.window_start + dest_reg);
             *target_ptr = val;
        },
        Err(e) => panic!("Runtime error: {}", e),
    }
}

pub unsafe extern "C" fn helper_call_symbol(vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut LispValue, func_reg: usize, param_start: usize, target_reg: usize) {
    let vm = &mut *vm;
    let prog = &mut *prog;
    
    // println!("helper_call_symbol func_reg={} param_start={} target_reg={}", func_reg, param_start, target_reg);

    let resolved_func = resolve_value(vm, registers, func_reg as u8);
    
    let (header, address, captures, jit_code_val) = if let ValueKind::Object(handle) = resolved_func.kind() {
        match vm.heap.get(handle) {
            Some(HeapValue::FuncRef(f)) => (f.header, f.address, None, f.jit_code.get()),
            Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone()), c.function.jit_code.get()),
            Some(HeapValue::Ref(inner)) => {
                 if let ValueKind::Object(inner_handle) = inner.kind() {
                     match vm.heap.get(inner_handle) {
                        Some(HeapValue::FuncRef(f)) => (f.header, f.address, None, 0),
                        Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone()), 0),
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
    
    let mut current_jit_code = jit_code_val;
    if current_jit_code == 0 {
         let end_addr = if vm.jit.is_compiled(address) { 0 } else { super::analysis::scan_function_end(prog, address) };
         match vm.jit.compile(&vm.global_vars, &mut vm.heap, &mut vm.jit_constants, &mut vm.symbol_table, prog, address, end_addr) {
             Ok(func) => {
                 if let ValueKind::Object(handle) = resolved_func.kind() {
                     let code_val = func as usize as u64;
                     let fast_code_val = vm.jit.fast_cache.get(&address).map(|&x| x as usize as u64).unwrap_or(0);
                     
                     match vm.heap.get(handle) {
                        Some(HeapValue::FuncRef(f)) => {
                            f.jit_code.set(code_val);
                            f.fast_jit_code.set(fast_code_val);
                        },
                        Some(HeapValue::Closure(c)) => {
                            c.function.jit_code.set(code_val);
                            c.function.fast_jit_code.set(fast_code_val);
                        },
                        _ => {}
                     }
                 }
                 
                 current_jit_code = func as usize as u64;
             },
             Err(e) => {
                 println!("JIT compilation failed in call: {}", e);
                 
                 let eof = prog.get_bytecode().len() as u64;
                 if let Some(last) = vm.call_states.last_mut() {
                     last.return_addr = eof;
                 }
                 
                 prog.jump_to(address);
                 vm.run_debug(prog, None);
                 
                 return;
             }
         }
    }

    // Synchronous Execution Loop (Trampoline)
    type JitFunction = unsafe extern "C" fn(*mut Vm, *mut VirtualProgram, *mut LispValue);
    loop {
        let func: JitFunction = std::mem::transmute(current_jit_code as *const u8);
        // Safety: vm.registers might have been resized by previous calls, so we always get a fresh pointer.
        // vm.window_start tracks the current frame.
        let regs_ptr = vm.registers.as_mut_ptr().add(vm.window_start);
        func(vm, prog, regs_ptr);
        
        if !vm.tail_call_pending {
            break;
        }
        vm.tail_call_pending = false;
        current_jit_code = vm.next_jit_code;
    }
    
    // Pop the call state and swap the result to the caller's target register.
    // The JIT-generated Instr::Ret just returns without popping, so we do it here.
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
    
    let (header, address, captures, jit_code_val) = match func.kind() {
        ValueKind::Object(handle) => match vm.heap.get(handle) {
            Some(HeapValue::FuncRef(f)) => (f.header, f.address, None, f.jit_code.get()),
            Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone()), c.function.jit_code.get()),
            Some(HeapValue::Ref(inner)) => {
                 if let ValueKind::Object(inner_handle) = inner.kind() {
                     match vm.heap.get(inner_handle) {
                        Some(HeapValue::FuncRef(f)) => (f.header, f.address, None, 0),
                        Some(HeapValue::Closure(c)) => (c.function.header, c.function.address, Some(c.captures.clone()), 0),
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

    let jit_code = jit_code_val;
    if jit_code != 0 {
         vm.tail_call_pending = true;
         vm.next_jit_code = jit_code;
    } else {
         // println!("Compiling tail call target at {}", address);
         let end_addr = if vm.jit.is_compiled(address) { 0 } else { super::analysis::scan_function_end(prog, address) };
         if let Ok(func_ptr) = vm.jit.compile(&vm.global_vars, &mut vm.heap, &mut vm.jit_constants, &mut vm.symbol_table, prog, address, end_addr) {
             let code = func_ptr as usize as u64;
             if let ValueKind::Object(handle) = func.kind() {
                 match vm.heap.get(handle) {
                     Some(HeapValue::FuncRef(f)) => { f.jit_code.set(code); }
                     Some(HeapValue::Closure(c)) => { c.function.jit_code.set(code); }
                     _ => {} // Handles Refs? Refs logic extracted 0 above. But Refs point to inner.
                     // The logic above unpacked Refs to inner header/address.
                     // So `func` is the original Ref?
                     // If `func` is Ref, we should update the INNER object's JIT code.
                     // But we don't have the inner handle easily here unless we unpack again.
                     // This is an edge case. For now simple support.
                 }
                 // If it was a Ref, we are not updating the cache. This means next time it recompiles or checks again.
                 // Ideally we should resolve Ref in `func` variable too?
                 // But `func` comes from register. 
             }
             
             vm.tail_call_pending = true;
             vm.next_jit_code = code;
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

    // Check cache first
    if let Some(&handle) = vm.symbol_opt_cache.get(&offset) {
        *registers.add(dest_reg) = LispValue::object(handle);
        return;
    }

    let prog = &mut *prog;
    let bytecode = prog.get_bytecode();
    let offset_idx = offset as usize;
    
    if offset_idx + 8 <= bytecode.len() {
        let len_bytes = &bytecode[offset_idx..offset_idx+8];
        let len = i64::from_le_bytes(len_bytes.try_into().unwrap()) as usize;
        
        if offset_idx + 8 + len <= bytecode.len() {
            let str_bytes = &bytecode[offset_idx+8..offset_idx+8+len];
            if let Ok(s) = std::str::from_utf8(str_bytes) {
                let handle = if let Some(&h) = vm.symbol_table.get(s) {
                    h
                } else {
                    vm.collect_garbage();
                    let h = vm.heap.alloc(HeapValue::Symbol(s.to_string()));
                    vm.symbol_table.insert(s.to_string(), h);
                    h
                };
                vm.symbol_opt_cache.insert(offset, handle);
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
    
    // vm.collect_garbage(); // alloc handles expansion.
    
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

            // Check cache
            let regs_ptr = vm.registers.as_mut_ptr().add(vm.window_start);
            let raw_func_val = *regs_ptr.add(func_reg);
            
            let use_cache = if let Some(cache) = &vm.map_cache {
                if let ValueKind::Object(h) = raw_func_val.kind() {
                     h == cache.handle
                } else {
                    false
                }
            } else {
                false
            };
            
            let mut captures_ptr: *const Vec<LispValue> = std::ptr::null();
            
            let (header, address, jit_code, _fast_jit_code) = if use_cache {
                 let cache = vm.map_cache.as_ref().unwrap();
                 if let Some(caps) = &cache.captures {
                     captures_ptr = caps;
                 }
                 (cache.header, cache.address, cache.jit_code, cache.fast_jit_code)
            } else {
                let resolved_func = resolve_value(vm, regs_ptr, func_reg as u8);
                
                let head: FunctionHeader;
                let addr: u64;
                let jc: u64;
                let fjc: u64;
                let mut caps_for_cache: Option<Vec<LispValue>> = None;
                
                if let ValueKind::Object(handle) = resolved_func.kind() {
                    match vm.heap.get(handle) {
                        Some(HeapValue::FuncRef(f)) => {
                            head = f.header; addr = f.address; jc = f.jit_code.get(); fjc = f.fast_jit_code.get();
                        },
                        Some(HeapValue::Closure(c)) => {
                            head = c.function.header; addr = c.function.address; jc = c.function.jit_code.get(); fjc = c.function.fast_jit_code.get();
                            captures_ptr = &c.captures;
                            caps_for_cache = Some(c.captures.clone());
                        },
                         Some(HeapValue::Ref(inner)) => {
                             if let ValueKind::Object(inner_handle) = inner.kind() {
                                 match vm.heap.get(inner_handle) {
                                    Some(HeapValue::FuncRef(f)) => {
                                        head = f.header; addr = f.address; jc = 0; fjc = 0;
                                    },
                                    Some(HeapValue::Closure(c)) => {
                                        head = c.function.header; addr = c.function.address; jc = 0; fjc = 0;
                                        captures_ptr = &c.captures;
                                        caps_for_cache = Some(c.captures.clone());
                                    },
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
                
                if let ValueKind::Object(orig_handle) = raw_func_val.kind() {
                      vm.map_cache = Some(crate::vm::vm::MapCache {
                          handle: orig_handle,
                          header: head,
                          address: addr,
                          captures: caps_for_cache,
                          jit_code: jc,
                          fast_jit_code: fjc
                      });
                }
                
                (head, addr, jc, fjc)
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
            
            if !captures_ptr.is_null() {
                let start_reg = header.param_count as usize;
                for (i, val) in (*captures_ptr).iter().enumerate() {
                    vm.registers[vm.window_start + start_reg + i] = *val;
                }
            }
            
            vm.registers[vm.window_start] = car;
            
            if jit_code != 0 {
                 return jit_code;
            }

            let end_addr = if vm.jit.is_compiled(address) { 0 } else { super::analysis::scan_function_end(prog, address) };
            if let Ok(func) = vm.jit.compile(&vm.global_vars, &mut vm.heap, &mut vm.jit_constants, &mut vm.symbol_table, prog, address, end_addr) {
                    let code = func as usize as u64;
                    if let Some(cache) = &mut vm.map_cache {
                        cache.jit_code = code;
                    }
                    return code;
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


