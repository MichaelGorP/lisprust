use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::cell::Cell;
use cranelift::prelude::*;
use cranelift::codegen::ir::BlockArg;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, Linkage, Module};
use super::vp::{Value as LispValue, Instr, JumpCondition, VirtualProgram, FunctionHeader, FunctionData, HeapValue};
use super::vm::Vm;

// Constants for Value layout
// Assumes #[repr(C, u8)] for Value enum
const TAG_OFFSET: i32 = 0;
// Data offset depends on alignment. For 64-bit types (i64, f64, ptr), alignment is 8.
// So tag (1 byte) + padding (7 bytes) = 8 bytes offset.
const DATA_OFFSET: i32 = 8;

pub struct Jit {
    builder_context: FunctionBuilderContext,
    ctx: codegen::Context,
    _data_ctx: DataDescription,
    module: JITModule,
    cache: HashMap<u64, *const u8>,
    pub function_map: Arc<Mutex<Vec<(usize, usize, String)>>>,
}

impl Jit {
    pub fn new() -> Self {
        let mut flag_builder = settings::builder();
        flag_builder.set("use_colocated_libcalls", "false").unwrap();
        flag_builder.set("is_pic", "false").unwrap();
        let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
            panic!("host machine is not supported: {}", msg);
        });
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .unwrap();
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

        // Register helper functions
        builder.symbol("helper_op", helper_op as *const u8);
        builder.symbol("helper_check_condition", helper_check_condition as *const u8);
        builder.symbol("helper_load_global", helper_load_global as *const u8);
        builder.symbol("helper_define", helper_define as *const u8);
        builder.symbol("helper_load_func_ref", helper_load_func_ref as *const u8);
        builder.symbol("helper_call_symbol", helper_call_symbol as *const u8);
        builder.symbol("helper_tail_call_symbol", helper_tail_call_symbol as *const u8);
        builder.symbol("helper_check_self_recursion", helper_check_self_recursion as *const u8);
        builder.symbol("helper_make_closure", helper_make_closure as *const u8);
        builder.symbol("helper_make_ref", helper_make_ref as *const u8);
        builder.symbol("helper_set_ref", helper_set_ref as *const u8);
        builder.symbol("helper_deref", helper_deref as *const u8);
        builder.symbol("helper_get_registers_ptr", helper_get_registers_ptr as *const u8);

        let module = JITModule::new(builder);
        
        Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            _data_ctx: DataDescription::new(),
            module,
            cache: HashMap::new(),
            function_map: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub fn compile(&mut self, prog: &mut VirtualProgram, start_addr: u64, end_addr: u64) -> Result<fn(*mut Vm, *mut VirtualProgram, *mut LispValue), String> {
        if let Some(&code) = self.cache.get(&start_addr) {
            return Ok(unsafe { std::mem::transmute(code) });
        }

        // Define signature: fn(*mut Vm, *mut VirtualProgram, *mut LispValue) -> ()
        let ptr_type = self.module.target_config().pointer_type();
        self.ctx.func.signature.params.push(AbiParam::new(ptr_type)); // vm
        self.ctx.func.signature.params.push(AbiParam::new(ptr_type)); // prog
        self.ctx.func.signature.params.push(AbiParam::new(ptr_type)); // registers
        // No return value

        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);
        
        // Save cursor to restore later (though we only compile once usually)
        let original_pos = prog.current_address();

        // --- PASS 1: Traversal to find Basic Blocks ---
        let mut block_starts = HashSet::new();
        block_starts.insert(start_addr);
        
        let mut queue = Vec::new();
        queue.push(start_addr);
        
        let mut visited_starts = HashSet::new();

        while let Some(current_start) = queue.pop() {
            if visited_starts.contains(&current_start) {
                continue;
            }
            visited_starts.insert(current_start);
            
            prog.jump_to(current_start);
            
            loop {
                if prog.current_address() >= end_addr {
                    break;
                }
                
                // Check if we ran into another block start (that is not the current one)
                if prog.current_address() != current_start && block_starts.contains(&prog.current_address()) {
                    break;
                }

                let opcode = match prog.read_opcode() {
                    Some(op) => op,
                    None => break
                };
                let instr: Instr = match opcode[0].try_into() {
                    Ok(i) => i,
                    Err(_) => break // Stop scanning if invalid opcode (likely data)
                };
                
                match instr {
                    Instr::Jump => {
                        let cond_byte = opcode[2];
                        let distance = match prog.read_int() {
                            Some(d) => d,
                            None => break
                        };
                        let after_read_pos = prog.current_address();
                        let target = (after_read_pos as i64 + distance) as u64;
                        
                        if !block_starts.contains(&target) {
                            block_starts.insert(target);
                            queue.push(target);
                        }
                        
                        if cond_byte != JumpCondition::Jump as u8 {
                            // Conditional jump, fallthrough is a block start
                            if !block_starts.contains(&after_read_pos) {
                                block_starts.insert(after_read_pos);
                                queue.push(after_read_pos);
                            }
                        }
                        break; // End of block
                    },
                    Instr::Ret | Instr::TailCallSymbol => {
                        break; // End of block
                    },
                    // Instructions with arguments
                    Instr::LoadInt | Instr::LoadFloat | Instr::Define | Instr::LoadGlobal | Instr::LoadFuncRef => {
                        let _ = prog.read_int();
                    },
                    Instr::LoadString => {
                        let _ = prog.read_string();
                    },
                    Instr::MakeClosure => {
                        let count = opcode[3];
                        for _ in 0..count {
                            let _ = prog.read_byte();
                        }
                    },
                    _ => {}
                }
            }
        }

        // Sort block starts
        let mut sorted_starts: Vec<u64> = block_starts.iter().cloned().collect();
        sorted_starts.sort();
        
        // Filter out blocks that are outside the range
        sorted_starts.retain(|&x| x < end_addr);

        let mut blocks = HashMap::new();
        let loop_header = builder.create_block();
        blocks.insert(start_addr, loop_header);
        
        for &start in &sorted_starts {
            if start != start_addr {
                 blocks.insert(start, builder.create_block());
            }
        }
        
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);

        let vm_ptr = builder.block_params(entry_block)[0];
        let prog_ptr = builder.block_params(entry_block)[1];
        let registers_ptr = builder.block_params(entry_block)[2];

        // Jump to loop header
        builder.ins().jump(loop_header, &[BlockArg::from(registers_ptr)]);
        builder.seal_block(entry_block);
        
        // We must switch to loop_header before declaring helpers? No, helpers are declared in the function.
        // But we should switch to loop_header before generating code for it.
        builder.switch_to_block(loop_header);

        // Import helper functions
        let mut sig_helper_op = self.module.make_signature();
        sig_helper_op.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_op.params.push(AbiParam::new(ptr_type)); // prog
        sig_helper_op.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_op.params.push(AbiParam::new(types::I32)); // opcode (u32)
        let callee_helper_op = self.module.declare_function("helper_op", Linkage::Import, &sig_helper_op).map_err(|e| e.to_string())?;
        let local_helper_op = self.module.declare_func_in_func(callee_helper_op, &mut builder.func);

        let mut sig_helper_check_condition = self.module.make_signature();
        sig_helper_check_condition.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_check_condition.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_check_condition.params.push(AbiParam::new(types::I64)); // reg_idx
        sig_helper_check_condition.returns.push(AbiParam::new(types::I32)); // result (0 or 1)
        let callee_helper_check_condition = self.module.declare_function("helper_check_condition", Linkage::Import, &sig_helper_check_condition).map_err(|e| e.to_string())?;
        let _local_helper_check_condition = self.module.declare_func_in_func(callee_helper_check_condition, &mut builder.func);

        let mut sig_helper_load_global = self.module.make_signature();
        sig_helper_load_global.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_load_global.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_load_global.params.push(AbiParam::new(types::I64)); // dest
        sig_helper_load_global.params.push(AbiParam::new(types::I64)); // sym_id
        let callee_helper_load_global = self.module.declare_function("helper_load_global", Linkage::Import, &sig_helper_load_global).map_err(|e| e.to_string())?;
        let local_helper_load_global = self.module.declare_func_in_func(callee_helper_load_global, &mut builder.func);

        let mut sig_helper_define = self.module.make_signature();
        sig_helper_define.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_define.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_define.params.push(AbiParam::new(types::I64)); // src
        sig_helper_define.params.push(AbiParam::new(types::I64)); // sym_id
        let callee_helper_define = self.module.declare_function("helper_define", Linkage::Import, &sig_helper_define).map_err(|e| e.to_string())?;
        let local_helper_define = self.module.declare_func_in_func(callee_helper_define, &mut builder.func);

        let mut sig_helper_load_func_ref = self.module.make_signature();
        sig_helper_load_func_ref.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_load_func_ref.params.push(AbiParam::new(ptr_type)); // prog
        sig_helper_load_func_ref.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_load_func_ref.params.push(AbiParam::new(types::I64)); // dest
        sig_helper_load_func_ref.params.push(AbiParam::new(types::I64)); // header_addr
        let callee_helper_load_func_ref = self.module.declare_function("helper_load_func_ref", Linkage::Import, &sig_helper_load_func_ref).map_err(|e| e.to_string())?;
        let local_helper_load_func_ref = self.module.declare_func_in_func(callee_helper_load_func_ref, &mut builder.func);

        let mut sig_helper_call_symbol = self.module.make_signature();
        sig_helper_call_symbol.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_call_symbol.params.push(AbiParam::new(ptr_type)); // prog
        sig_helper_call_symbol.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_call_symbol.params.push(AbiParam::new(types::I64)); // func_reg
        sig_helper_call_symbol.params.push(AbiParam::new(types::I64)); // param_start
        sig_helper_call_symbol.params.push(AbiParam::new(types::I64)); // target_reg
        let callee_helper_call_symbol = self.module.declare_function("helper_call_symbol", Linkage::Import, &sig_helper_call_symbol).map_err(|e| e.to_string())?;
        let local_helper_call_symbol = self.module.declare_func_in_func(callee_helper_call_symbol, &mut builder.func);

        let mut sig_helper_tail_call_symbol = self.module.make_signature();
        sig_helper_tail_call_symbol.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_tail_call_symbol.params.push(AbiParam::new(ptr_type)); // prog
        sig_helper_tail_call_symbol.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_tail_call_symbol.params.push(AbiParam::new(types::I64)); // func_reg
        sig_helper_tail_call_symbol.params.push(AbiParam::new(types::I64)); // param_start
        let callee_helper_tail_call_symbol = self.module.declare_function("helper_tail_call_symbol", Linkage::Import, &sig_helper_tail_call_symbol).map_err(|e| e.to_string())?;
        let local_helper_tail_call_symbol = self.module.declare_func_in_func(callee_helper_tail_call_symbol, &mut builder.func);

        let mut sig_helper_make_closure = self.module.make_signature();
        sig_helper_make_closure.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_make_closure.params.push(AbiParam::new(ptr_type)); // prog
        sig_helper_make_closure.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_make_closure.params.push(AbiParam::new(types::I64)); // dest_reg
        sig_helper_make_closure.params.push(AbiParam::new(types::I64)); // func_reg
        sig_helper_make_closure.params.push(AbiParam::new(types::I64)); // count
        sig_helper_make_closure.params.push(AbiParam::new(types::I64)); // instr_addr
        let callee_helper_make_closure = self.module.declare_function("helper_make_closure", Linkage::Import, &sig_helper_make_closure).map_err(|e| e.to_string())?;
        let local_helper_make_closure = self.module.declare_func_in_func(callee_helper_make_closure, &mut builder.func);

        let mut sig_helper_check_self_recursion = self.module.make_signature();
        sig_helper_check_self_recursion.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_check_self_recursion.params.push(AbiParam::new(types::I64)); // func_reg
        sig_helper_check_self_recursion.params.push(AbiParam::new(types::I64)); // start_addr
        sig_helper_check_self_recursion.returns.push(AbiParam::new(types::I32)); // bool
        let callee_helper_check_self_recursion = self.module.declare_function("helper_check_self_recursion", Linkage::Import, &sig_helper_check_self_recursion).map_err(|e| e.to_string())?;
        let _local_helper_check_self_recursion = self.module.declare_func_in_func(callee_helper_check_self_recursion, &mut builder.func);

        let mut sig_helper_make_ref = self.module.make_signature();
        sig_helper_make_ref.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_make_ref.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_make_ref.params.push(AbiParam::new(types::I64)); // dest_reg
        let callee_helper_make_ref = self.module.declare_function("helper_make_ref", Linkage::Import, &sig_helper_make_ref).map_err(|e| e.to_string())?;
        let local_helper_make_ref = self.module.declare_func_in_func(callee_helper_make_ref, &mut builder.func);

        let mut sig_helper_set_ref = self.module.make_signature();
        sig_helper_set_ref.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_set_ref.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_set_ref.params.push(AbiParam::new(types::I64)); // dest_reg
        sig_helper_set_ref.params.push(AbiParam::new(types::I64)); // src_reg
        let callee_helper_set_ref = self.module.declare_function("helper_set_ref", Linkage::Import, &sig_helper_set_ref).map_err(|e| e.to_string())?;
        let local_helper_set_ref = self.module.declare_func_in_func(callee_helper_set_ref, &mut builder.func);

        let mut sig_helper_deref = self.module.make_signature();
        sig_helper_deref.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_deref.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_deref.params.push(AbiParam::new(types::I64)); // dest_reg
        sig_helper_deref.params.push(AbiParam::new(types::I64)); // src_reg
        let callee_helper_deref = self.module.declare_function("helper_deref", Linkage::Import, &sig_helper_deref).map_err(|e| e.to_string())?;
        let local_helper_deref = self.module.declare_func_in_func(callee_helper_deref, &mut builder.func);

        let mut sig_helper_get_registers_ptr = self.module.make_signature();
        sig_helper_get_registers_ptr.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_get_registers_ptr.returns.push(AbiParam::new(ptr_type)); // registers
        let callee_helper_get_registers_ptr = self.module.declare_function("helper_get_registers_ptr", Linkage::Import, &sig_helper_get_registers_ptr).map_err(|e| e.to_string())?;
        let local_helper_get_registers_ptr = self.module.declare_func_in_func(callee_helper_get_registers_ptr, &mut builder.func);

        // --- PASS 2: Generate Code ---
        prog.jump_to(start_addr);
        
        let mut is_terminated = false;
        
        // Add registers_ptr param to all blocks
        for block in blocks.values() {
             builder.append_block_param(*block, ptr_type);
        }

        let mut registers_ptr = builder.block_params(entry_block)[2];

        while prog.current_address() < end_addr {
            let current_addr = prog.current_address();
            
            // Start new block if this address is a block start
            if let Some(&block) = blocks.get(&current_addr) {
                if current_addr != start_addr {
                    if !is_terminated {
                        builder.ins().jump(block, &[BlockArg::from(registers_ptr)]);
                    }
                    builder.switch_to_block(block);
                    registers_ptr = builder.block_params(block)[0];
                    is_terminated = false;
                }
            } else if is_terminated {
                // We are in dead code/data, skip to next block
                let mut next_addr = end_addr;
                for &s in &sorted_starts {
                    if s > current_addr {
                        next_addr = s;
                        break;
                    }
                }
                prog.jump_to(next_addr);
                continue;
            }

            let opcode = prog.read_opcode().unwrap(); // Safe because we scanned before
            let instr: Instr = opcode[0].try_into().unwrap();
            
            if is_terminated {
                 match instr {
                    Instr::Jump | Instr::LoadInt | Instr::LoadGlobal | Instr::Define | Instr::LoadFuncRef | Instr::LoadFloat => {
                        prog.read_int().unwrap();
                    },
                    Instr::LoadString => {
                        prog.read_string().unwrap();
                    },
                    Instr::MakeClosure => {
                        let count = opcode[3];
                        for _ in 0..count {
                            prog.read_byte().unwrap();
                        }
                    },
                    _ => {}
                 }
                 continue;
            }

            match instr {
                Instr::Jump => {
                    let cond_byte = opcode[2];
                    let distance = prog.read_int().unwrap();
                    let after_read_pos = prog.current_address();
                    let target = (after_read_pos as i64 + distance) as u64;
                    
                    let target_block = *blocks.get(&target).ok_or(format!("Jump target block not found: {}", target))?;
                    


                    if cond_byte == JumpCondition::Jump as u8 {
                        builder.ins().jump(target_block, &[BlockArg::from(registers_ptr)]);
                    } else {
                        // Conditional Jump
                        let reg_idx = opcode[1] as i64;
                        let val_size = std::mem::size_of::<LispValue>() as i64;
                        let reg_ptr = builder.ins().iadd_imm(registers_ptr, reg_idx * val_size);
                        
                        let tag = builder.ins().load(types::I8, MemFlags::trusted(), reg_ptr, TAG_OFFSET);
                        let val = builder.ins().load(types::I8, MemFlags::trusted(), reg_ptr, DATA_OFFSET);
                        
                        // is_false = (tag == 1) && (val == 0)
                        // Tag 1 is Boolean. Val 0 is false.
                        let tag_is_bool = builder.ins().icmp_imm(IntCC::Equal, tag, 1);
                        let val_is_false = builder.ins().icmp_imm(IntCC::Equal, val, 0);
                        let is_false = builder.ins().band(tag_is_bool, val_is_false);
                        
                        let fallthrough_block = *blocks.get(&after_read_pos).ok_or("Fallthrough block not found")?;

                        if cond_byte == JumpCondition::JumpTrue as u8 {
                            // Jump if !is_false (i.e. is_true)
                            // If is_false is true (1), we fallthrough.
                            // If is_false is false (0), we jump.
                            // Wait. brif(c, then, else).
                            // If is_false (it is false), we want to jump (it is true).
                            // So if is_false is 0, we jump.
                            // brif(is_false, fallthrough, target)
                            builder.ins().brif(is_false, fallthrough_block, &[BlockArg::from(registers_ptr)], target_block, &[BlockArg::from(registers_ptr)]);
                        } else {
                            // JumpFalse
                            // Jump if is_false
                            builder.ins().brif(is_false, target_block, &[BlockArg::from(registers_ptr)], fallthrough_block, &[BlockArg::from(registers_ptr)]);
                        }
                    }
                    is_terminated = true;
                },
                Instr::LoadInt => {
                    let dest_reg = opcode[1] as i64;
                    let val = prog.read_int().unwrap();
                    
                    let val_size = std::mem::size_of::<LispValue>() as i64;
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let const_tag = builder.ins().iconst(types::I8, 2); // Value::Integer
                    let val_const = builder.ins().iconst(types::I64, val);
                    
                    builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                    builder.ins().store(MemFlags::trusted(), val_const, dest_ptr, DATA_OFFSET);
                    
                    is_terminated = false;
                },
                Instr::LoadFloat => {
                    let dest_reg = opcode[1] as i64;
                    let val_bits = prog.read_int().unwrap();
                    let val = f64::from_bits(val_bits as u64);
                    
                    let val_size = std::mem::size_of::<LispValue>() as i64;
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let const_tag = builder.ins().iconst(types::I8, 3); // Value::Float
                    let val_const = builder.ins().f64const(val);
                    
                    builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                    builder.ins().store(MemFlags::trusted(), val_const, dest_ptr, DATA_OFFSET);
                    
                    is_terminated = false;
                },
                Instr::LoadGlobal => {
                    let dest_reg = opcode[1] as i64;
                    let sym_id = prog.read_int().unwrap();
                    
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let sym_id_const = builder.ins().iconst(types::I64, sym_id);
                    
                    builder.ins().call(local_helper_load_global, &[vm_ptr, registers_ptr, dest_reg_const, sym_id_const]);
                    
                    is_terminated = false;
                },
                Instr::Define => {
                    let src_reg = opcode[1] as i64;
                    let sym_id = prog.read_int().unwrap();
                    
                    let src_reg_const = builder.ins().iconst(types::I64, src_reg);
                    let sym_id_const = builder.ins().iconst(types::I64, sym_id);
                    
                    builder.ins().call(local_helper_define, &[vm_ptr, registers_ptr, src_reg_const, sym_id_const]);
                    is_terminated = false;
                },
                Instr::LoadFuncRef => {
                    let dest_reg = opcode[1] as i64;
                    let header_addr = prog.read_int().unwrap();
                    
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let header_addr_const = builder.ins().iconst(types::I64, header_addr);
                    
                    builder.ins().call(local_helper_load_func_ref, &[vm_ptr, prog_ptr, registers_ptr, dest_reg_const, header_addr_const]);
                    is_terminated = false;
                },
                Instr::CallSymbol => {
                    let func_reg = opcode[1] as i64;
                    let param_start = opcode[2] as i64;
                    let target_reg = opcode[3] as i64;
                    
                    let func_reg_const = builder.ins().iconst(types::I64, func_reg);
                    let param_start_const = builder.ins().iconst(types::I64, param_start);
                    let target_reg_const = builder.ins().iconst(types::I64, target_reg);
                    
                    builder.ins().call(local_helper_call_symbol, &[vm_ptr, prog_ptr, registers_ptr, func_reg_const, param_start_const, target_reg_const]);
                    
                    // Reload registers_ptr as it might have changed due to resize
                    let call_inst = builder.ins().call(local_helper_get_registers_ptr, &[vm_ptr]);
                    registers_ptr = builder.inst_results(call_inst)[0];
                    
                    is_terminated = false;
                },
                Instr::TailCallSymbol => {
                    let func_reg = opcode[1] as i64;
                    let param_start = opcode[2] as i64;
                    
                    let func_reg_const = builder.ins().iconst(types::I64, func_reg);
                    let param_start_const = builder.ins().iconst(types::I64, param_start);
                    
                    builder.ins().call(local_helper_tail_call_symbol, &[vm_ptr, prog_ptr, registers_ptr, func_reg_const, param_start_const]);
                    builder.ins().return_(&[]);
                    is_terminated = true;
                },
                Instr::Add | Instr::Sub | Instr::Mul | Instr::Div | 
                Instr::Eq | Instr::Neq | Instr::Lt | Instr::Gt | Instr::Leq | Instr::Geq => {
                    let dest_reg = opcode[1] as i64;
                    let src1_reg = opcode[2] as i64;
                    let src2_reg = opcode[3] as i64;
                    
                    let val_size = std::mem::size_of::<LispValue>() as i64;
                    
                    let src1_ptr = builder.ins().iadd_imm(registers_ptr, src1_reg * val_size);
                    let src2_ptr = builder.ins().iadd_imm(registers_ptr, src2_reg * val_size);
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let tag1 = builder.ins().load(types::I8, MemFlags::trusted(), src1_ptr, TAG_OFFSET);
                    let tag2 = builder.ins().load(types::I8, MemFlags::trusted(), src2_ptr, TAG_OFFSET);
                    
                    let block_int = builder.create_block();
                    let block_float_exec = builder.create_block();
                    let block_slow = builder.create_block();
                    let block_done = builder.create_block();
                    builder.append_block_param(block_done, ptr_type);
                    let block_dispatch = builder.create_block();

                    // Fast path for integers
                    let t1_x = builder.ins().bxor_imm(tag1, 2);
                    let t2_x = builder.ins().bxor_imm(tag2, 2);
                    let any_non_int = builder.ins().bor(t1_x, t2_x);
                    builder.ins().brif(any_non_int, block_dispatch, &[], block_int, &[]);

                    builder.switch_to_block(block_dispatch);
                    let tag1_32 = builder.ins().uextend(types::I32, tag1);
                    let tag2_32 = builder.ins().uextend(types::I32, tag2);
                    let tag1_shifted = builder.ins().ishl_imm(tag1_32, 4);
                    let combined = builder.ins().bor(tag1_shifted, tag2_32);
                    let index = builder.ins().iadd_imm(combined, -34); // 0x22 = 34

                    let mut table = Vec::new();
                    for i in 0..18 {
                        if i == 0 {
                            table.push(builder.func.dfg.block_call(block_int, &[]));
                        } else if i == 17 {
                            table.push(builder.func.dfg.block_call(block_float_exec, &[]));
                        } else {
                            table.push(builder.func.dfg.block_call(block_slow, &[]));
                        }
                    }
                    let default_call = builder.func.dfg.block_call(block_slow, &[]);
                    let jt_data = JumpTableData::new(default_call, &table);
                    let jt = builder.create_jump_table(jt_data);
                    builder.ins().br_table(index, jt);
                    
                    // --- Integer Path ---
                    builder.switch_to_block(block_int);
                    let val1 = builder.ins().load(types::I64, MemFlags::trusted(), src1_ptr, DATA_OFFSET);
                    let val2 = builder.ins().load(types::I64, MemFlags::trusted(), src2_ptr, DATA_OFFSET);
                    
                    match instr {
                        Instr::Add => {
                            let res = builder.ins().iadd(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 2);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Sub => {
                            let res = builder.ins().isub(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 2);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Mul => {
                            let res = builder.ins().imul(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 2);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Div => {
                            // Integer division in Lisp might need to handle 0 or return float? 
                            // For now assuming standard integer div
                            let res = builder.ins().sdiv(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 2);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Eq => {
                            let res = builder.ins().icmp(IntCC::Equal, val1, val2);
                            let res_ext = builder.ins().uextend(types::I64, res);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res_ext, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Neq => {
                            let res = builder.ins().icmp(IntCC::NotEqual, val1, val2);
                            let res_ext = builder.ins().uextend(types::I64, res);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res_ext, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Lt => {
                            let res = builder.ins().icmp(IntCC::SignedLessThan, val1, val2);
                            let res_ext = builder.ins().uextend(types::I64, res);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res_ext, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Gt => {
                            let res = builder.ins().icmp(IntCC::SignedGreaterThan, val1, val2);
                            let res_ext = builder.ins().uextend(types::I64, res);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res_ext, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Leq => {
                            let res = builder.ins().icmp(IntCC::SignedLessThanOrEqual, val1, val2);
                            let res_ext = builder.ins().uextend(types::I64, res);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res_ext, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Geq => {
                            let res = builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, val1, val2);
                            let res_ext = builder.ins().uextend(types::I64, res);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res_ext, dest_ptr, DATA_OFFSET);
                        },
                        _ => {}
                    }
                    builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)]);

                    // --- Float Path ---
                    builder.switch_to_block(block_float_exec);
                    let val1 = builder.ins().load(types::F64, MemFlags::trusted(), src1_ptr, DATA_OFFSET);
                    let val2 = builder.ins().load(types::F64, MemFlags::trusted(), src2_ptr, DATA_OFFSET);
                    
                    match instr {
                        Instr::Add => {
                            let res = builder.ins().fadd(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 3);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Sub => {
                            let res = builder.ins().fsub(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 3);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Mul => {
                            let res = builder.ins().fmul(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 3);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Div => {
                            let res = builder.ins().fdiv(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 3);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Eq => {
                            let res = builder.ins().fcmp(FloatCC::Equal, val1, val2);
                            let res_ext = builder.ins().uextend(types::I64, res);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res_ext, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Neq => {
                            let res = builder.ins().fcmp(FloatCC::NotEqual, val1, val2);
                            let res_ext = builder.ins().uextend(types::I64, res);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res_ext, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Lt => {
                            let res = builder.ins().fcmp(FloatCC::LessThan, val1, val2);
                            let res_ext = builder.ins().uextend(types::I64, res);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res_ext, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Gt => {
                            let res = builder.ins().fcmp(FloatCC::GreaterThan, val1, val2);
                            let res_ext = builder.ins().uextend(types::I64, res);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res_ext, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Leq => {
                            let res = builder.ins().fcmp(FloatCC::LessThanOrEqual, val1, val2);
                            let res_ext = builder.ins().uextend(types::I64, res);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res_ext, dest_ptr, DATA_OFFSET);
                        },
                        Instr::Geq => {
                            let res = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, val1, val2);
                            let res_ext = builder.ins().uextend(types::I64, res);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                            builder.ins().store(MemFlags::trusted(), res_ext, dest_ptr, DATA_OFFSET);
                        },
                        _ => {}
                    }
                    builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)]);

                    // --- Slow Path ---
                    builder.switch_to_block(block_slow);
                    let op_val = u32::from_le_bytes(opcode);
                    let op_const = builder.ins().iconst(types::I32, op_val as i64);
                    builder.ins().call(local_helper_op, &[vm_ptr, prog_ptr, registers_ptr, op_const]);
                    builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)]);
                    
                    builder.switch_to_block(block_done);
                    registers_ptr = builder.block_params(block_done)[0];
                },
                Instr::Not => {
                    let dest_reg = opcode[1] as i64;
                    let src_reg = opcode[2] as i64;
                    let val_size = std::mem::size_of::<LispValue>() as i64;
                    
                    let src_ptr = builder.ins().iadd_imm(registers_ptr, src_reg * val_size);
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let tag = builder.ins().load(types::I8, MemFlags::trusted(), src_ptr, TAG_OFFSET);
                    let val = builder.ins().load(types::I8, MemFlags::trusted(), src_ptr, DATA_OFFSET);
                    
                    let tag_is_bool = builder.ins().icmp_imm(IntCC::Equal, tag, 1);
                    let not_val = builder.ins().bxor_imm(val, 1);
                    
                    // If tag is bool, result is not_val. Else result is false (0).
                    let zero = builder.ins().iconst(types::I8, 0);
                    let res_val = builder.ins().select(tag_is_bool, not_val, zero);
                    
                    let res_val_ext = builder.ins().uextend(types::I64, res_val);
                    let const_tag = builder.ins().iconst(types::I8, 1);
                    
                    builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, TAG_OFFSET);
                    builder.ins().store(MemFlags::trusted(), res_val_ext, dest_ptr, DATA_OFFSET);
                    
                    is_terminated = false;
                },
                Instr::CopyReg => {
                    let dest_reg = opcode[1] as i64;
                    let src_reg = opcode[2] as i64;
                    let val_size = std::mem::size_of::<LispValue>() as i64;
                    
                    let src_ptr = builder.ins().iadd_imm(registers_ptr, src_reg * val_size);
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let tag = builder.ins().load(types::I8, MemFlags::trusted(), src_ptr, TAG_OFFSET);
                    
                    // Check if POD (tag <= 3 or tag == 6)
                    let is_pod_basic = builder.ins().icmp_imm(IntCC::UnsignedLessThanOrEqual, tag, 3);
                    let is_funcref = builder.ins().icmp_imm(IntCC::Equal, tag, 6);
                    let is_pod = builder.ins().bor(is_pod_basic, is_funcref);
                    
                    let block_copy = builder.create_block();
                    let block_slow = builder.create_block();
                    let block_done = builder.create_block();
                    builder.append_block_param(block_done, ptr_type);
                    
                    builder.ins().brif(is_pod, block_copy, &[], block_slow, &[]);
                    
                    builder.switch_to_block(block_copy);
                    // Copy full Value size. Assumes size is multiple of 8.
                    let val_size_usize = std::mem::size_of::<LispValue>();
                    assert!(val_size_usize % 8 == 0, "LispValue size must be multiple of 8");
                    let num_words = val_size_usize / 8;
                    
                    for i in 0..num_words {
                        let offset = (i * 8) as i32;
                        let val = builder.ins().load(types::I64, MemFlags::trusted(), src_ptr, offset);
                        builder.ins().store(MemFlags::trusted(), val, dest_ptr, offset);
                    }
                    builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)]);
                    
                    builder.switch_to_block(block_slow);
                    let op_val = u32::from_le_bytes(opcode);
                    let op_const = builder.ins().iconst(types::I32, op_val as i64);
                    builder.ins().call(local_helper_op, &[vm_ptr, prog_ptr, registers_ptr, op_const]);
                    builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)]);
                    
                    builder.switch_to_block(block_done);
                    registers_ptr = builder.block_params(block_done)[0];
                },
                Instr::MakeClosure => {
                    let dest_reg = opcode[1] as i64;
                    let func_reg = opcode[2] as i64;
                    let count = opcode[3] as i64;
                    let instr_addr = current_addr as i64;
                    
                    // Skip capture registers in the stream
                    for _ in 0..count {
                        prog.read_byte().unwrap();
                    }
                    
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let func_reg_const = builder.ins().iconst(types::I64, func_reg);
                    let count_const = builder.ins().iconst(types::I64, count);
                    let instr_addr_const = builder.ins().iconst(types::I64, instr_addr);
                    
                    builder.ins().call(local_helper_make_closure, &[vm_ptr, prog_ptr, registers_ptr, dest_reg_const, func_reg_const, count_const, instr_addr_const]);
                    is_terminated = false;
                },
                Instr::MakeRef => {
                    let dest_reg = opcode[1] as i64;
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    builder.ins().call(local_helper_make_ref, &[vm_ptr, registers_ptr, dest_reg_const]);
                },
                Instr::SetRef => {
                    let dest_reg = opcode[1] as i64;
                    let src_reg = opcode[2] as i64;
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let src_reg_const = builder.ins().iconst(types::I64, src_reg);
                    builder.ins().call(local_helper_set_ref, &[vm_ptr, registers_ptr, dest_reg_const, src_reg_const]);
                },
                Instr::Deref => {
                    let dest_reg = opcode[1] as i64;
                    let src_reg = opcode[2] as i64;
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let src_reg_const = builder.ins().iconst(types::I64, src_reg);
                    builder.ins().call(local_helper_deref, &[vm_ptr, registers_ptr, dest_reg_const, src_reg_const]);
                },
                Instr::Ret => {
                    if !is_terminated {
                        builder.ins().return_(&[]);
                        is_terminated = true;
                    }
                },
                // Instructions that need to skip arguments in the stream but use helper_op
                _ => {
                    // Generic helper
                    let op_val = u32::from_le_bytes(opcode);
                    let op_const = builder.ins().iconst(types::I32, op_val as i64);
                    
                    builder.ins().call(local_helper_op, &[vm_ptr, prog_ptr, registers_ptr, op_const]);
                    
                    // Advance cursor for arguments
                    match instr {
                        Instr::LoadFloat => { prog.read_int(); },
                        Instr::LoadString => { prog.read_string(); },
                        _ => {}
                    }
                    is_terminated = false;
                }
            }
        }

        // Restore cursor
        prog.jump_to(original_pos);

        // Handle implicit return at end of function if a block exists there
        if let Some(&end_block) = blocks.get(&end_addr) {
            let current_block = builder.current_block();
            if current_block == Some(end_block) {
                 if !is_terminated {
                     builder.ins().return_(&[]);
                 }
            } else {
                if !is_terminated {
                    builder.ins().jump(end_block, &[BlockArg::from(registers_ptr)]);
                }
                
                builder.switch_to_block(end_block);
                builder.ins().return_(&[]);
            }
        } else if !is_terminated {
             // If we reached the end without a terminator and no end block (unlikely if we scanned correctly),
             // we should return.
             builder.ins().return_(&[]);
        }

        builder.seal_all_blocks();
        builder.finalize();

        static JIT_COUNTER: AtomicUsize = AtomicUsize::new(0);
        let unique_id = JIT_COUNTER.fetch_add(1, Ordering::Relaxed);
        let func_name = format!("jit_fn_{}_{}", start_addr, unique_id);
        
        let id = self.module.declare_function(&func_name, Linkage::Export, &self.ctx.func.signature).map_err(|e| e.to_string())?;
        self.module.define_function(id, &mut self.ctx).map_err(|e| {
            // Print the function for debugging
            println!("{}", self.ctx.func.display());
            e.to_string()
        })?;
        
        // Record function size
        let size = self.ctx.compiled_code().map(|c| c.code_buffer().len()).unwrap_or(0);
        
        self.module.clear_context(&mut self.ctx);
        self.module.finalize_definitions().map_err(|e| e.to_string())?;

        let code = self.module.get_finalized_function(id);
        
        if size > 0 {
            let start = code as usize;
            let end = start + size;
            if let Ok(mut map) = self.function_map.lock() {
                map.push((start, end, func_name));
            }
        }

        self.cache.insert(start_addr, code);
        Ok(unsafe { std::mem::transmute(code) })
    }
}

unsafe extern "C" fn helper_check_self_recursion(vm: *mut Vm, func_reg: usize, start_addr: u64) -> i32 {
    let vm = &mut *vm;
    let func = &vm.registers[vm.window_start + func_reg];
    
    let address = if let Some(r) = func.as_ref() {
        let inner = r.borrow();
        if let Some(f) = inner.as_func_ref() {
            f.address
        } else if let Some(c) = inner.as_closure() {
            c.function.address
        } else {
            return 0;
        }
    } else {
        if let Some(f) = func.as_func_ref() {
            f.address
        } else if let Some(c) = func.as_closure() {
            c.function.address
        } else {
            return 0;
        }
    };
    
    if address == start_addr { 1 } else { 0 }
}

unsafe extern "C" fn helper_op(vm: *mut Vm, _prog: *mut VirtualProgram, registers: *mut LispValue, opcode_val: u32) {
    let opcode = opcode_val.to_le_bytes();
    let vm = &mut *vm;

    macro_rules! jit_binary_op {
        ($op:tt) => {
            {
                 let v1 = resolve_value(vm, registers, opcode[2]);
                 let v2 = resolve_value(vm, registers, opcode[3]);
                 let res_reg = opcode[1] as usize;
                 
                 match (v1, v2) {
                    (LispValue::Integer(lhs), LispValue::Integer(rhs)) => *registers.add(res_reg) = LispValue::Integer(lhs $op rhs),
                    (LispValue::Integer(lhs), LispValue::Float(rhs)) => *registers.add(res_reg) = LispValue::Float(lhs as f64 $op rhs),
                    (LispValue::Float(lhs), LispValue::Float(rhs)) => *registers.add(res_reg) = LispValue::Float(lhs $op rhs),
                    (LispValue::Float(lhs), LispValue::Integer(rhs)) => *registers.add(res_reg) = LispValue::Float(lhs $op rhs as f64),
                    (_v1, _v2) => {
                        // println!("DEBUG: Binary op failed: {:?} {:?} {:?}", opcode[0], v1, v2);
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
                 
                 let matches = match (v1, v2) {
                    (LispValue::Integer(lhs), LispValue::Integer(rhs)) => lhs $op rhs,
                    (LispValue::Integer(lhs), LispValue::Float(rhs)) => (lhs as f64) $op rhs,
                    (LispValue::Float(lhs), LispValue::Float(rhs)) => lhs $op rhs,
                    (LispValue::Float(lhs), LispValue::Integer(rhs)) => lhs $op rhs as f64,
                    _ => false,
                 };
                 *registers.add(res_reg) = LispValue::Boolean(matches);
            }
        }
    }
    
    match opcode[0].try_into() {
        Ok(Instr::Add) => jit_binary_op!(+),
        Ok(Instr::Sub) => jit_binary_op!(-),
        Ok(Instr::Mul) => jit_binary_op!(*),
        Ok(Instr::Div) => jit_binary_op!(/),
        Ok(Instr::Eq) => jit_comparison_op!(==),
        Ok(Instr::Neq) => jit_comparison_op!(!=),
        Ok(Instr::Lt) => jit_comparison_op!(<),
        Ok(Instr::Gt) => jit_comparison_op!(>),
        Ok(Instr::Leq) => jit_comparison_op!(<=),
        Ok(Instr::Geq) => jit_comparison_op!(>=),
        Ok(Instr::Not) => {
             let v = resolve_value(vm, registers, opcode[2]);
             let res_reg = opcode[1] as usize;
             match v {
                 LispValue::Boolean(b) => *registers.add(res_reg) = LispValue::Boolean(!b),
                 _ => *registers.add(res_reg) = LispValue::Boolean(false),
             }
        },
        Ok(Instr::CopyReg) => {
             let dest_reg = opcode[1] as usize;
             let src_reg = opcode[2] as usize;
             let val = (*registers.add(src_reg)).clone();

             *registers.add(dest_reg) = val;
        },
        _ => {
            // println!("JIT helper: Unimplemented op {:?}", opcode[0]);
        }
    }
}

unsafe extern "C" fn helper_check_condition(_vm: *mut Vm, registers: *mut LispValue, reg_idx: usize) -> i32 {
    let val = &*registers.add(reg_idx);
    if val.is_true() { 1 } else { 0 }
}

unsafe fn resolve_value(_vm: &Vm, registers: *mut LispValue, reg_idx: u8) -> LispValue {
    let val = &*registers.add(reg_idx as usize);
    if let Some(r) = val.as_ref() {
        r.borrow().clone()
    } else {
        val.clone()
    }
}

unsafe extern "C" fn helper_load_global(vm: *mut Vm, registers: *mut LispValue, dest_reg: usize, sym_id: i64) {
    let vm = &mut *vm;
    
    if (sym_id as usize) < vm.global_vars.len() {
        let v = &mut vm.global_vars[sym_id as usize];
        *registers.add(dest_reg) = v.clone();
    } else {
        *registers.add(dest_reg) = LispValue::Empty;
    }
}

unsafe extern "C" fn helper_define(vm: *mut Vm, registers: *mut LispValue, src_reg: usize, sym_id: i64) {
    let vm = &mut *vm;
    let val = (*registers.add(src_reg)).clone();
    // println!("DEBUG: Define sym {} = {:?}", sym_id, val);
    if sym_id as usize >= vm.global_vars.len() {
        vm.global_vars.resize(sym_id as usize + 1, LispValue::Empty);
    }
    vm.global_vars[sym_id as usize] = val;
}

unsafe extern "C" fn helper_load_func_ref(vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut LispValue, dest_reg: usize, header_addr: i64) {
    let vm = &mut *vm;
    let prog = &mut *prog;
    let header = prog.read_function_header(header_addr as u64).unwrap();
    let func_addr = header_addr as usize + std::mem::size_of::<FunctionHeader>();
    
    let jit_code = vm.jit.cache.get(&(func_addr as u64)).map(|&ptr| ptr as u64).unwrap_or(0);
    *registers.add(dest_reg) = LispValue::Object(Rc::new(HeapValue::FuncRef(FunctionData{header, address: func_addr as u64, jit_code: Cell::new(jit_code)})));
}

unsafe extern "C" fn helper_call_symbol(vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut LispValue, func_reg: usize, param_start: usize, target_reg: usize) {
    let vm = &mut *vm;
    let prog = &mut *prog;
    
    let func = &*registers.add(func_reg);
    
    let (header, address, captures, jit_code_cell) = if let Some(r) = func.as_ref() {
        // If it's in a RefCell, we can't safely get a reference to the Cell that outlives the borrow.
        // So we just return None for the cell, meaning we won't update the cache.
        let inner = r.borrow();
        if let Some(f) = inner.as_func_ref() {
            (f.header, f.address, None, None)
        } else if let Some(c) = inner.as_closure() {
            (c.function.header, c.function.address, Some(c.captures.clone()), None)
        } else {
            // println!("DEBUG: CallSymbol failed: Not a function at reg {}: {:?}", func_reg, inner);
            return
        }
    } else {
        if let Some(f) = func.as_func_ref() {
            (f.header, f.address, None, Some(&f.jit_code))
        } else if let Some(c) = func.as_closure() {
            (c.function.header, c.function.address, Some(c.captures.clone()), Some(&c.function.jit_code))
        } else {
            // println!("DEBUG: CallSymbol failed: Not a function at reg {}: {:?}", func_reg, func);
            return
        }
    };

    let size = param_start + header.register_count as usize + vm.window_start;
    if size >= vm.registers.len() {
        vm.registers.resize(size, LispValue::Empty);
    }
    let old_ws = vm.window_start;
    let ret_addr = 0; 
    
    let state = crate::vm::vm::CallState{window_start: old_ws, result_reg: header.result_reg, target_reg: target_reg as u8, return_addr: ret_addr};
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
         let func: unsafe extern "C" fn(*mut Vm, *mut VirtualProgram, *mut LispValue) = std::mem::transmute(jit_code as *const u8);
         func(vm, prog, vm.registers.as_mut_ptr().add(vm.window_start));
    } else {
         let end_addr = vm.scan_function_end(prog, address);
         vm.run_jit_function(prog, address, end_addr);
         
         // Update cache in FunctionData
         if let Some(cell) = jit_code_cell {
             if let Some(&code) = vm.jit.cache.get(&address) {
                 cell.set(code as u64);
             }
         }
    }
    
    let state = vm.call_states.pop().unwrap();
    let source_reg = vm.window_start + state.result_reg as usize;
    let target_reg = state.window_start + state.target_reg as usize;
    vm.registers.swap(source_reg, target_reg);
    
    vm.window_start = old_ws;
}

unsafe extern "C" fn helper_tail_call_symbol(vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut LispValue, func_reg: usize, param_start: usize) {
    let vm = &mut *vm;
    let prog = &mut *prog;

    let func = &*registers.add(func_reg);
    
    let (header, address, captures, jit_code_cell) = if let Some(r) = func.as_ref() {
        let inner = r.borrow();
        if let Some(f) = inner.as_func_ref() {
            (f.header, f.address, None, None)
        } else if let Some(c) = inner.as_closure() {
            (c.function.header, c.function.address, Some(c.captures.clone()), None)
        } else {
            return
        }
    } else {
        if let Some(f) = func.as_func_ref() {
            (f.header, f.address, None, Some(&f.jit_code))
        } else if let Some(c) = func.as_closure() {
            (c.function.header, c.function.address, Some(c.captures.clone()), Some(&c.function.jit_code))
        } else {
            return
        }
    };

    let size = vm.window_start + header.register_count as usize;
    if size >= vm.registers.len() {
        vm.registers.resize(size, LispValue::Empty);
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
         let func: unsafe extern "C" fn(*mut Vm, *mut VirtualProgram, *mut LispValue) = std::mem::transmute(jit_code as *const u8);
         func(vm, prog, vm.registers.as_mut_ptr().add(vm.window_start));
    } else {
         let end_addr = vm.scan_function_end(prog, address);
         vm.run_jit_function(prog, address, end_addr);
         
         // Update cache in FunctionData
         if let Some(cell) = jit_code_cell {
             if let Some(&code) = vm.jit.cache.get(&address) {
                 cell.set(code as u64);
             }
         }
    }
}

use super::vp::ClosureData;
use std::cell::RefCell;
use std::rc::Rc;

unsafe extern "C" fn helper_make_closure(_vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut LispValue, dest_reg: usize, func_reg: usize, count: usize, instr_addr: u64) {
    let prog = &mut *prog;
    
    let old_pos = prog.current_address();
    prog.jump_to(instr_addr + 4); // Skip opcode (4)
    
    let mut captures = Vec::with_capacity(count);
    for _ in 0..count {
        let reg_idx = prog.read_byte().unwrap();
        // Cloning values for capture is necessary as they escape the current scope
        let val = (*registers.add(reg_idx as usize)).clone();
        captures.push(val);
    }
    
    prog.jump_to(old_pos);
    
    let func_val = &*registers.add(func_reg);
    
    if let Some(fd) = func_val.as_func_ref() {
        // Avoid cloning FunctionData if possible, but it's small (copy)
        // The main cost is Rc allocation for ClosureData
        *registers.add(dest_reg) = LispValue::Object(Rc::new(HeapValue::Closure(ClosureData{function: fd.clone(), captures})));
    } else {
        *registers.add(dest_reg) = LispValue::Empty;
    }
}

unsafe extern "C" fn helper_make_ref(_vm: *mut Vm, registers: *mut LispValue, dest_reg: usize) {
    let val = (*registers.add(dest_reg)).clone();
    *registers.add(dest_reg) = LispValue::Object(Rc::new(HeapValue::Ref(RefCell::new(val))));
}

unsafe extern "C" fn helper_set_ref(_vm: *mut Vm, registers: *mut LispValue, dest_reg: usize, src_reg: usize) {
    if let Some(r) = (*registers.add(dest_reg)).as_ref() {
        *r.borrow_mut() = (*registers.add(src_reg)).clone();
    }
}

unsafe extern "C" fn helper_deref(_vm: *mut Vm, registers: *mut LispValue, dest_reg: usize, src_reg: usize) {
    if let Some(r) = (*registers.add(src_reg)).as_ref() {
        *registers.add(dest_reg) = r.borrow().clone();
    }
}

unsafe extern "C" fn helper_get_registers_ptr(vm: *mut Vm) -> *mut LispValue {
    let vm = &mut *vm;
    vm.registers.as_mut_ptr().add(vm.window_start)
}
