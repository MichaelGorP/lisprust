use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering};
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, Linkage, Module};
use super::vp::{Value, Instr, JumpCondition, VirtualProgram, FunctionHeader, FunctionData};
use super::vm::Vm;

pub struct Jit {
    builder_context: FunctionBuilderContext,
    ctx: codegen::Context,
    _data_ctx: DataDescription,
    module: JITModule,
    cache: HashMap<u64, *const u8>,
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
        builder.symbol("helper_load_int", helper_load_int as *const u8);
        builder.symbol("helper_check_condition", helper_check_condition as *const u8);
        builder.symbol("helper_load_global", helper_load_global as *const u8);
        builder.symbol("helper_define", helper_define as *const u8);
        builder.symbol("helper_load_func_ref", helper_load_func_ref as *const u8);
        builder.symbol("helper_call_symbol", helper_call_symbol as *const u8);
        builder.symbol("helper_tail_call_symbol", helper_tail_call_symbol as *const u8);
        builder.symbol("helper_prepare_direct_call", helper_prepare_direct_call as *const u8);
        builder.symbol("helper_check_self_recursion", helper_check_self_recursion as *const u8);

        let module = JITModule::new(builder);
        
        Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            _data_ctx: DataDescription::new(),
            module,
            cache: HashMap::new(),
        }
    }

    pub fn compile(&mut self, prog: &mut VirtualProgram, start_addr: u64, end_addr: u64) -> Result<fn(*mut Vm, *mut VirtualProgram, *mut Value), String> {
        if let Some(&code) = self.cache.get(&start_addr) {
            return Ok(unsafe { std::mem::transmute(code) });
        }

        // Define signature: fn(*mut Vm, *mut VirtualProgram, *mut Value) -> ()
        let ptr_type = self.module.target_config().pointer_type();
        self.ctx.func.signature.params.push(AbiParam::new(ptr_type)); // vm
        self.ctx.func.signature.params.push(AbiParam::new(ptr_type)); // prog
        self.ctx.func.signature.params.push(AbiParam::new(ptr_type)); // registers
        // No return value

        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);
        
        // Save cursor to restore later (though we only compile once usually)
        let original_pos = prog.current_address();

        // --- PASS 1: Scan for Basic Blocks ---
        let mut block_starts = HashSet::new();
        block_starts.insert(start_addr);
        
        prog.jump_to(start_addr);
        while prog.current_address() < end_addr {
            let _current_addr = prog.current_address();
            let opcode = prog.read_opcode().ok_or("Unexpected EOF reading opcode")?;
            let instr: Instr = opcode[0].try_into().map_err(|_| "Invalid opcode")?;
            
            match instr {
                Instr::Jump => {
                    let distance = prog.read_int().ok_or("Unexpected EOF reading jump distance")?;
                    // Target is relative to position AFTER reading int
                    let after_read_pos = prog.current_address();
                    let target = (after_read_pos as i64 + distance) as u64;
                    
                    block_starts.insert(target);
                    block_starts.insert(after_read_pos); // Fallthrough
                },
                Instr::Ret => {
                    // Ret terminates a block, next instruction (if any) starts a new one
                    block_starts.insert(prog.current_address());
                },
                // Instructions with arguments - must advance cursor
                Instr::LoadInt | Instr::LoadFloat | Instr::Define | Instr::LoadGlobal | Instr::LoadFuncRef => {
                    prog.read_int();
                },
                Instr::LoadString => {
                    prog.read_string();
                },
                // Others have no arguments (handled by read_opcode)
                _ => {}
            }
        }

        let mut blocks = HashMap::new();
        let loop_header = builder.create_block();
        blocks.insert(start_addr, loop_header);

        for &start in &block_starts {
            // Only create blocks for addresses within our function range
            if start != start_addr && start >= start_addr && start <= end_addr {
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
        builder.ins().jump(loop_header, &[]);
        builder.seal_block(entry_block);
        builder.switch_to_block(loop_header);

        // Import helper functions
        let mut sig_helper_op = self.module.make_signature();
        sig_helper_op.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_op.params.push(AbiParam::new(ptr_type)); // prog
        sig_helper_op.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_op.params.push(AbiParam::new(types::I32)); // opcode (u32)
        let callee_helper_op = self.module.declare_function("helper_op", Linkage::Import, &sig_helper_op).map_err(|e| e.to_string())?;
        let local_helper_op = self.module.declare_func_in_func(callee_helper_op, &mut builder.func);

        let mut sig_helper_load_int = self.module.make_signature();
        sig_helper_load_int.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_load_int.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_load_int.params.push(AbiParam::new(types::I64)); // dest
        sig_helper_load_int.params.push(AbiParam::new(types::I64)); // val
        let callee_helper_load_int = self.module.declare_function("helper_load_int", Linkage::Import, &sig_helper_load_int).map_err(|e| e.to_string())?;
        let local_helper_load_int = self.module.declare_func_in_func(callee_helper_load_int, &mut builder.func);

        let mut sig_helper_check_condition = self.module.make_signature();
        sig_helper_check_condition.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_check_condition.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_check_condition.params.push(AbiParam::new(types::I64)); // reg_idx
        sig_helper_check_condition.returns.push(AbiParam::new(types::I32)); // result (0 or 1)
        let callee_helper_check_condition = self.module.declare_function("helper_check_condition", Linkage::Import, &sig_helper_check_condition).map_err(|e| e.to_string())?;
        let local_helper_check_condition = self.module.declare_func_in_func(callee_helper_check_condition, &mut builder.func);

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
        sig_helper_tail_call_symbol.params.push(AbiParam::new(types::I64)); // func_reg
        sig_helper_tail_call_symbol.params.push(AbiParam::new(types::I64)); // param_start
        let callee_helper_tail_call_symbol = self.module.declare_function("helper_tail_call_symbol", Linkage::Import, &sig_helper_tail_call_symbol).map_err(|e| e.to_string())?;
        let local_helper_tail_call_symbol = self.module.declare_func_in_func(callee_helper_tail_call_symbol, &mut builder.func);

        // --- PASS 2: Generate Code ---
        prog.jump_to(start_addr);
        
        let mut is_terminated = false;

        while prog.current_address() < end_addr {
            let current_addr = prog.current_address();
            
            // Start new block if this address is a block start
            if let Some(&block) = blocks.get(&current_addr) {
                if current_addr != start_addr {
                    if !is_terminated {
                        builder.ins().jump(block, &[]);
                    }
                    builder.switch_to_block(block);
                    is_terminated = false;
                }
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
                        builder.ins().jump(target_block, &[]);
                    } else {
                        // Conditional Jump
                        let reg_idx = opcode[1] as i64;
                        let reg_idx_const = builder.ins().iconst(types::I64, reg_idx);
                        
                        let call = builder.ins().call(local_helper_check_condition, &[vm_ptr, registers_ptr, reg_idx_const]);
                        let result = builder.inst_results(call)[0];
                        
                        // result is 1 if true, 0 if false
                        // JumpTrue: jump if result != 0
                        // JumpFalse: jump if result == 0
                        
                        // We need the fallthrough block
                        // Since we are in a block, and the next instruction starts a new block (because we marked it in Pass 1),
                        // we can just use the next block.
                        // But wait, Pass 1 marks `after_read_pos` as a block start.
                        let fallthrough_block = *blocks.get(&after_read_pos).ok_or("Fallthrough block not found")?;

                        if cond_byte == JumpCondition::JumpTrue as u8 {
                            builder.ins().brif(result, target_block, &[], fallthrough_block, &[]);
                        } else {
                            // JumpFalse
                            let is_zero = builder.ins().icmp_imm(IntCC::Equal, result, 0);
                            builder.ins().brif(is_zero, target_block, &[], fallthrough_block, &[]);
                        }
                    }
                    is_terminated = true;
                },
                Instr::LoadInt => {
                    let dest_reg = opcode[1] as i64;
                    let val = prog.read_int().unwrap();
                    
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let val_const = builder.ins().iconst(types::I64, val);
                    
                    builder.ins().call(local_helper_load_int, &[vm_ptr, registers_ptr, dest_reg_const, val_const]);
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
                    
                    // Try direct call
                    let mut sig = self.module.make_signature();
                    sig.params.push(AbiParam::new(types::I64)); // vm
                    sig.params.push(AbiParam::new(types::I64)); // func_reg
                    sig.params.push(AbiParam::new(types::I64)); // param_start
                    sig.params.push(AbiParam::new(types::I64)); // result_reg_out ptr
                    sig.returns.push(AbiParam::new(types::I64)); // code ptr

                    let helper_func = self.module.declare_function("helper_prepare_direct_call", Linkage::Import, &sig).unwrap();
                    let local_helper = self.module.declare_func_in_func(helper_func, builder.func);

                    let result_reg_slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 8, 0));
                    let result_reg_ptr = builder.ins().stack_addr(types::I64, result_reg_slot, 0);

                    let call = builder.ins().call(local_helper, &[vm_ptr, func_reg_const, param_start_const, result_reg_ptr]);
                    let code_ptr = builder.inst_results(call)[0];

                    let is_null = builder.ins().icmp_imm(IntCC::Equal, code_ptr, 0);
                    let block_direct = builder.create_block();
                    let block_fallback = builder.create_block();
                    let block_cont = builder.create_block();

                    builder.ins().brif(is_null, block_fallback, &[], block_direct, &[]);

                    builder.switch_to_block(block_direct);
                    // Direct call sequence
                    let ws_offset = 48; // Offset of window_start in Vm
                    let ws_ptr = builder.ins().iadd_imm(vm_ptr, ws_offset);
                    let current_ws = builder.ins().load(types::I64, MemFlags::trusted(), ws_ptr, 0);

                    let new_ws = builder.ins().iadd(current_ws, param_start_const);
                    builder.ins().store(MemFlags::trusted(), new_ws, ws_ptr, 0);

                    let value_size = std::mem::size_of::<Value>() as i64;
                    let offset = builder.ins().imul_imm(param_start_const, value_size);
                    let new_regs_ptr = builder.ins().iadd(registers_ptr, offset);

                    let sig_ref = builder.import_signature(builder.func.signature.clone());
                    builder.ins().call_indirect(sig_ref, code_ptr, &[vm_ptr, prog_ptr, new_regs_ptr]);

                    builder.ins().store(MemFlags::trusted(), current_ws, ws_ptr, 0);

                    let result_reg_idx = builder.ins().load(types::I64, MemFlags::trusted(), result_reg_ptr, 0);
                    let src_offset = builder.ins().imul_imm(result_reg_idx, value_size);
                    let src_ptr = builder.ins().iadd(new_regs_ptr, src_offset);

                    let dest_offset = builder.ins().imul_imm(target_reg_const, value_size);
                    let dest_ptr = builder.ins().iadd(registers_ptr, dest_offset);

                    for i in 0..4 {
                        let off = i * 8;
                        let val = builder.ins().load(types::I64, MemFlags::trusted(), src_ptr, off);
                        builder.ins().store(MemFlags::trusted(), val, dest_ptr, off);
                    }

                    builder.ins().jump(block_cont, &[]);

                    builder.switch_to_block(block_fallback);
                    builder.ins().call(local_helper_call_symbol, &[vm_ptr, prog_ptr, registers_ptr, func_reg_const, param_start_const, target_reg_const]);
                    builder.ins().jump(block_cont, &[]);

                    builder.switch_to_block(block_cont);
                    is_terminated = false;
                },
                Instr::TailCallSymbol => {
                    let func_reg = opcode[1] as i64;
                    let param_start = opcode[2] as i64;
                    
                    let func_reg_const = builder.ins().iconst(types::I64, func_reg);
                    let param_start_const = builder.ins().iconst(types::I64, param_start);
                    
                    // Check self recursion
                    let mut sig = self.module.make_signature();
                    sig.params.push(AbiParam::new(types::I64)); // vm
                    sig.params.push(AbiParam::new(types::I64)); // func_reg
                    sig.params.push(AbiParam::new(types::I64)); // start_addr
                    sig.returns.push(AbiParam::new(types::I32)); // bool

                    let helper_func = self.module.declare_function("helper_check_self_recursion", Linkage::Import, &sig).unwrap();
                    let local_helper = self.module.declare_func_in_func(helper_func, builder.func);

                    let start_addr_const = builder.ins().iconst(types::I64, start_addr as i64);
                    let call = builder.ins().call(local_helper, &[vm_ptr, func_reg_const, start_addr_const]);
                    let is_self = builder.inst_results(call)[0];

                    let block_loop = builder.create_block();
                    let block_fallback = builder.create_block();

                    builder.ins().brif(is_self, block_loop, &[], block_fallback, &[]);

                    builder.switch_to_block(block_loop);
                    // Self recursion loop
                    // Copy params from param_start to 0
                    // We need param_count.
                    // Read header
                    let header_addr = start_addr - 4;
                    let header = prog.read_function_header(header_addr).unwrap();
                    let param_count = header.param_count as i64;
                    
                    let value_size = std::mem::size_of::<Value>() as i64;
                    let u64_count = value_size / 8;
                    
                    for i in 0..param_count {
                        let src_idx = param_start + i;
                        let dest_idx = i;
                        
                        let src_offset = builder.ins().iconst(types::I64, src_idx * value_size);
                        let dest_offset = builder.ins().iconst(types::I64, dest_idx * value_size);
                        
                        let src_ptr = builder.ins().iadd(registers_ptr, src_offset);
                        let dest_ptr = builder.ins().iadd(registers_ptr, dest_offset);
                        
                        // Copy value_size bytes
                        for j in 0..u64_count {
                            let off = (j * 8) as i32;
                            let val = builder.ins().load(types::I64, MemFlags::trusted(), src_ptr, off);
                            builder.ins().store(MemFlags::trusted(), val, dest_ptr, off);
                        }
                    }
                    
                    // Jump to loop header
                    let loop_header = *blocks.get(&start_addr).unwrap();
                    builder.ins().jump(loop_header, &[]);

                    builder.switch_to_block(block_fallback);
                    builder.ins().call(local_helper_tail_call_symbol, &[vm_ptr, prog_ptr, func_reg_const, param_start_const]);
                    builder.ins().return_(&[]);
                    is_terminated = true;
                },
                Instr::Add | Instr::Sub | Instr::Mul | Instr::Div | 
                Instr::Eq | Instr::Neq | Instr::Lt | Instr::Gt | Instr::Leq | Instr::Geq => {
                    let dest_reg = opcode[1] as i64;
                    let src1_reg = opcode[2] as i64;
                    let src2_reg = opcode[3] as i64;
                    
                    let val_size = std::mem::size_of::<Value>() as i64;
                    let tag_offset = 0;
                    let data_offset = 8;
                    
                    let src1_ptr = builder.ins().iadd_imm(registers_ptr, src1_reg * val_size);
                    let src2_ptr = builder.ins().iadd_imm(registers_ptr, src2_reg * val_size);
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let tag1 = builder.ins().load(types::I8, MemFlags::trusted(), src1_ptr, tag_offset);
                    let tag2 = builder.ins().load(types::I8, MemFlags::trusted(), src2_ptr, tag_offset);
                    
                    let tag1_32 = builder.ins().uextend(types::I32, tag1);
                    let tag2_32 = builder.ins().uextend(types::I32, tag2);
                    let tag1_shifted = builder.ins().ishl_imm(tag1_32, 4);
                    let combined = builder.ins().bor(tag1_shifted, tag2_32);
                    let index = builder.ins().iadd_imm(combined, -34); // 0x22 = 34

                    let block_int = builder.create_block();
                    let block_float_exec = builder.create_block();
                    let block_slow = builder.create_block();
                    let block_done = builder.create_block();

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
                    let val1 = builder.ins().load(types::I64, MemFlags::trusted(), src1_ptr, data_offset);
                    let val2 = builder.ins().load(types::I64, MemFlags::trusted(), src2_ptr, data_offset);
                    
                    match instr {
                        Instr::Add => {
                            let res = builder.ins().iadd(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 2);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Sub => {
                            let res = builder.ins().isub(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 2);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Mul => {
                            let res = builder.ins().imul(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 2);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Div => {
                            // Integer division in Lisp might need to handle 0 or return float? 
                            // For now assuming standard integer div
                            let res = builder.ins().sdiv(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 2);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Eq => {
                            let res = builder.ins().icmp(IntCC::Equal, val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Neq => {
                            let res = builder.ins().icmp(IntCC::NotEqual, val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Lt => {
                            let res = builder.ins().icmp(IntCC::SignedLessThan, val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Gt => {
                            let res = builder.ins().icmp(IntCC::SignedGreaterThan, val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Leq => {
                            let res = builder.ins().icmp(IntCC::SignedLessThanOrEqual, val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Geq => {
                            let res = builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        _ => {}
                    }
                    builder.ins().jump(block_done, &[]);

                    // --- Float Path ---
                    builder.switch_to_block(block_float_exec);
                    let val1 = builder.ins().load(types::F64, MemFlags::trusted(), src1_ptr, data_offset);
                    let val2 = builder.ins().load(types::F64, MemFlags::trusted(), src2_ptr, data_offset);
                    
                    match instr {
                        Instr::Add => {
                            let res = builder.ins().fadd(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 3);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Sub => {
                            let res = builder.ins().fsub(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 3);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Mul => {
                            let res = builder.ins().fmul(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 3);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Div => {
                            let res = builder.ins().fdiv(val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 3);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Eq => {
                            let res = builder.ins().fcmp(FloatCC::Equal, val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Neq => {
                            let res = builder.ins().fcmp(FloatCC::NotEqual, val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Lt => {
                            let res = builder.ins().fcmp(FloatCC::LessThan, val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Gt => {
                            let res = builder.ins().fcmp(FloatCC::GreaterThan, val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Leq => {
                            let res = builder.ins().fcmp(FloatCC::LessThanOrEqual, val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        Instr::Geq => {
                            let res = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, val1, val2);
                            let const_tag = builder.ins().iconst(types::I8, 1);
                            builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, tag_offset);
                            builder.ins().store(MemFlags::trusted(), res, dest_ptr, data_offset);
                        },
                        _ => {}
                    }
                    builder.ins().jump(block_done, &[]);

                    // --- Slow Path ---
                    builder.switch_to_block(block_slow);
                    let op_val = u32::from_le_bytes(opcode);
                    let op_const = builder.ins().iconst(types::I32, op_val as i64);
                    builder.ins().call(local_helper_op, &[vm_ptr, prog_ptr, registers_ptr, op_const]);
                    builder.ins().jump(block_done, &[]);
                    
                    builder.switch_to_block(block_done);
                },
                Instr::Not => {
                    let dest_reg = opcode[1] as i64;
                    let src_reg = opcode[2] as i64;
                    let val_size = std::mem::size_of::<Value>() as i64;
                    
                    let src_ptr = builder.ins().iadd_imm(registers_ptr, src_reg * val_size);
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let tag = builder.ins().load(types::I8, MemFlags::trusted(), src_ptr, 0);
                    
                    let block_bool = builder.create_block();
                    let block_other = builder.create_block();
                    let block_done = builder.create_block();
                    
                    let is_bool = builder.ins().icmp_imm(IntCC::Equal, tag, 1);
                    builder.ins().brif(is_bool, block_bool, &[], block_other, &[]);
                    
                    builder.switch_to_block(block_bool);
                    let val_bool = builder.ins().load(types::I8, MemFlags::trusted(), src_ptr, 8);
                    let not_val = builder.ins().bxor_imm(val_bool, 1);
                    let const_tag = builder.ins().iconst(types::I8, 1);
                    builder.ins().store(MemFlags::trusted(), const_tag, dest_ptr, 0);
                    builder.ins().store(MemFlags::trusted(), not_val, dest_ptr, 8);
                    builder.ins().jump(block_done, &[]);
                    
                    builder.switch_to_block(block_other);
                    let is_ref = builder.ins().icmp_imm(IntCC::Equal, tag, 8);
                    let block_slow = builder.create_block();
                    let block_false = builder.create_block();
                    builder.ins().brif(is_ref, block_slow, &[], block_false, &[]);
                    
                    builder.switch_to_block(block_false);
                    let const_tag_bool = builder.ins().iconst(types::I8, 1);
                    let const_false = builder.ins().iconst(types::I8, 0);
                    builder.ins().store(MemFlags::trusted(), const_tag_bool, dest_ptr, 0);
                    builder.ins().store(MemFlags::trusted(), const_false, dest_ptr, 8);
                    builder.ins().jump(block_done, &[]);
                    
                    builder.switch_to_block(block_slow);
                    let op_val = u32::from_le_bytes(opcode);
                    let op_const = builder.ins().iconst(types::I32, op_val as i64);
                    builder.ins().call(local_helper_op, &[vm_ptr, prog_ptr, registers_ptr, op_const]);
                    builder.ins().jump(block_done, &[]);
                    
                    builder.switch_to_block(block_done);
                },
                Instr::CopyReg => {
                    let dest_reg = opcode[1] as i64;
                    let src_reg = opcode[2] as i64;
                    let val_size = std::mem::size_of::<Value>() as i64;
                    
                    let src_ptr = builder.ins().iadd_imm(registers_ptr, src_reg * val_size);
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let tag = builder.ins().load(types::I8, MemFlags::trusted(), src_ptr, 0);
                    
                    // Check if POD (tag <= 3 or tag == 6)
                    let is_pod_basic = builder.ins().icmp_imm(IntCC::UnsignedLessThanOrEqual, tag, 3);
                    let is_funcref = builder.ins().icmp_imm(IntCC::Equal, tag, 6);
                    let is_pod = builder.ins().bor(is_pod_basic, is_funcref);
                    
                    let block_copy = builder.create_block();
                    let block_slow = builder.create_block();
                    let block_done = builder.create_block();
                    
                    builder.ins().brif(is_pod, block_copy, &[], block_slow, &[]);
                    
                    builder.switch_to_block(block_copy);
                    // Copy 32 bytes. 4 x i64.
                    for i in 0..4 {
                        let offset = i * 8;
                        let val = builder.ins().load(types::I64, MemFlags::trusted(), src_ptr, offset);
                        builder.ins().store(MemFlags::trusted(), val, dest_ptr, offset);
                    }
                    builder.ins().jump(block_done, &[]);
                    
                    builder.switch_to_block(block_slow);
                    let op_val = u32::from_le_bytes(opcode);
                    let op_const = builder.ins().iconst(types::I32, op_val as i64);
                    builder.ins().call(local_helper_op, &[vm_ptr, prog_ptr, registers_ptr, op_const]);
                    builder.ins().jump(block_done, &[]);
                    
                    builder.switch_to_block(block_done);
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
        self.module.clear_context(&mut self.ctx);
        self.module.finalize_definitions().map_err(|e| e.to_string())?;

        let code = self.module.get_finalized_function(id);
        self.cache.insert(start_addr, code);
        Ok(unsafe { std::mem::transmute(code) })
    }
}

unsafe extern "C" fn helper_check_self_recursion(vm: *mut Vm, func_reg: usize, start_addr: u64) -> i32 {
    let vm = &mut *vm;
    let func = &vm.registers[vm.window_start + func_reg];
    let resolved = if let Value::Ref(r) = func { r.borrow().clone() } else { func.clone() };
    
    let address = match resolved {
        Value::FuncRef(f) => f.address,
        Value::Closure(c) => c.function.address,
        _ => return 0,
    };
    
    if address == start_addr { 1 } else { 0 }
}

unsafe extern "C" fn helper_load_int(_vm: *mut Vm, registers: *mut Value, index: usize, val: i64) {

    *registers.add(index) = Value::Integer(val);
}

unsafe extern "C" fn helper_op(vm: *mut Vm, _prog: *mut VirtualProgram, registers: *mut Value, opcode_val: u32) {
    let opcode = opcode_val.to_le_bytes();
    let vm = &mut *vm;

    macro_rules! jit_binary_op {
        ($op:tt) => {
            {
                 let v1 = resolve_value(vm, registers, opcode[2]);
                 let v2 = resolve_value(vm, registers, opcode[3]);
                 let res_reg = opcode[1] as usize;
                 
                 match (v1, v2) {
                    (Value::Integer(lhs), Value::Integer(rhs)) => *registers.add(res_reg) = Value::Integer(lhs $op rhs),
                    (Value::Integer(lhs), Value::Float(rhs)) => *registers.add(res_reg) = Value::Float(lhs as f64 $op rhs),
                    (Value::Float(lhs), Value::Float(rhs)) => *registers.add(res_reg) = Value::Float(lhs $op rhs),
                    (Value::Float(lhs), Value::Integer(rhs)) => *registers.add(res_reg) = Value::Float(lhs $op rhs as f64),
                    (v1, v2) => {
                        println!("DEBUG: Binary op failed: {:?} {:?} {:?}", opcode[0], v1, v2);
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
                    (Value::Integer(lhs), Value::Integer(rhs)) => lhs $op rhs,
                    (Value::Integer(lhs), Value::Float(rhs)) => (lhs as f64) $op rhs,
                    (Value::Float(lhs), Value::Float(rhs)) => lhs $op rhs,
                    (Value::Float(lhs), Value::Integer(rhs)) => lhs $op rhs as f64,
                    _ => false,
                 };
                 *registers.add(res_reg) = Value::Boolean(matches);
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
                 Value::Boolean(b) => *registers.add(res_reg) = Value::Boolean(!b),
                 _ => *registers.add(res_reg) = Value::Boolean(false),
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

unsafe extern "C" fn helper_check_condition(_vm: *mut Vm, registers: *mut Value, reg_idx: usize) -> i32 {
    let val = &*registers.add(reg_idx);
    if val.is_true() { 1 } else { 0 }
}

unsafe fn resolve_value(_vm: &Vm, registers: *mut Value, reg_idx: u8) -> Value {
    let val = &*registers.add(reg_idx as usize);
    if let Value::Ref(r) = val {
        r.borrow().clone()
    } else {
        val.clone()
    }
}

unsafe extern "C" fn helper_load_global(vm: *mut Vm, registers: *mut Value, dest_reg: usize, sym_id: i64) {
    let vm = &mut *vm;
    
    if (sym_id as usize) < vm.global_vars.len() {
        let v = &mut vm.global_vars[sym_id as usize];
        match v {
            Value::FuncRef(f) => {
                if f.jit_code == 0 {
                    if let Some(&ptr) = vm.jit.cache.get(&f.address) {
                        f.jit_code = ptr as u64;
                    }
                }
            },
            Value::Closure(c) => {
                 if let Some(c_data) = std::rc::Rc::get_mut(c) {
                     if c_data.function.jit_code == 0 {
                         if let Some(&ptr) = vm.jit.cache.get(&c_data.function.address) {
                             c_data.function.jit_code = ptr as u64;
                         }
                     }
                 } else {
                     let mut c_data = (**c).clone();
                     if c_data.function.jit_code == 0 {
                         if let Some(&ptr) = vm.jit.cache.get(&c_data.function.address) {
                             c_data.function.jit_code = ptr as u64;
                         }
                     }
                     *c = std::rc::Rc::new(c_data);
                 }
            },
            _ => {}
        }
        *registers.add(dest_reg) = v.clone();
    } else {
        *registers.add(dest_reg) = Value::Empty;
    }
}

unsafe extern "C" fn helper_define(vm: *mut Vm, registers: *mut Value, src_reg: usize, sym_id: i64) {
    let vm = &mut *vm;
    let val = (*registers.add(src_reg)).clone();
    // println!("DEBUG: Define sym {} = {:?}", sym_id, val);
    if sym_id as usize >= vm.global_vars.len() {
        vm.global_vars.resize(sym_id as usize + 1, Value::Empty);
    }
    vm.global_vars[sym_id as usize] = val;
}

unsafe extern "C" fn helper_load_func_ref(vm: *mut Vm, prog: *mut VirtualProgram, registers: *mut Value, dest_reg: usize, header_addr: i64) {
    let vm = &mut *vm;
    let prog = &mut *prog;
    let header = prog.read_function_header(header_addr as u64).unwrap();
    let func_addr = header_addr as usize + std::mem::size_of::<FunctionHeader>();
    
    let jit_code = vm.jit.cache.get(&(func_addr as u64)).map(|&ptr| ptr as u64).unwrap_or(0);
    *registers.add(dest_reg) = Value::FuncRef(FunctionData{header, address: func_addr as u64, jit_code});
}

unsafe extern "C" fn helper_prepare_direct_call(vm: *mut Vm, func_reg: usize, param_start: usize, result_reg_out: *mut usize) -> *const u8 {
    let vm = &mut *vm;
    let func = &vm.registers[vm.window_start + func_reg];
    
    if let Value::FuncRef(f) = func {
        if f.jit_code != 0 {
            let header = f.header;
            let jit_code = f.jit_code;
            
            let size = vm.window_start + param_start + header.register_count as usize;
            if size >= vm.registers.len() {
                vm.registers.resize(size, Value::Empty);
            }
            *result_reg_out = header.result_reg as usize;
            return jit_code as *const u8;
        }
    }

    let resolved = if let Value::Ref(r) = func { r.borrow().clone() } else { func.clone() };

    let (header, _address, captures, jit_code) = match resolved {
        Value::FuncRef(f) => (f.header, f.address, None, f.jit_code),
        Value::Closure(c) => (c.function.header, c.function.address, Some(c.captures.clone()), c.function.jit_code),
        _ => return std::ptr::null(),
    };

    if jit_code != 0 {
        // Resize registers
        let size = vm.window_start + param_start + header.register_count as usize;
        if size >= vm.registers.len() {
            vm.registers.resize(size, Value::Empty);
        }

        // Copy captures
        if let Some(caps) = captures {
             let start_reg = vm.window_start + param_start + header.param_count as usize;
             for (i, val) in caps.into_iter().enumerate() {
                 vm.registers[start_reg + i] = val;
             }
        }
        
        *result_reg_out = header.result_reg as usize;
        return jit_code as *const u8;
    }
    
    std::ptr::null()
}

unsafe extern "C" fn helper_call_symbol(vm: *mut Vm, prog: *mut VirtualProgram, _registers: *mut Value, func_reg: usize, param_start: usize, target_reg: usize) {
    let vm = &mut *vm;
    let prog = &mut *prog;
    
    // println!("DEBUG: CallSymbol func_reg={}, param_start={}, target_reg={}", func_reg, param_start, target_reg);

    let func = vm.registers[func_reg + vm.window_start].clone();
    
    let resolved_func = if let Value::Ref(r) = &func {
        r.borrow().clone()
    } else {
        func
    };

    let (header, address, captures, jit_code) = match resolved_func {
        Value::FuncRef(f) => (f.header, f.address, None, f.jit_code),
        Value::Closure(c) => (c.function.header, c.function.address, Some(c.captures.clone()), c.function.jit_code),
        _ => {
            println!("DEBUG: CallSymbol failed: Not a function at reg {}: {:?}", func_reg, resolved_func);
            return
        }
    };

    let size = param_start + header.register_count as usize + vm.window_start;
    if size >= vm.registers.len() {
        // println!("DEBUG: Resizing registers to {}", size);
        vm.registers.resize(size, Value::Empty);
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
    
    if jit_code != 0 {
         let func: unsafe extern "C" fn(*mut Vm, *mut VirtualProgram, *mut Value) = std::mem::transmute(jit_code as *const u8);
         func(vm, prog, vm.registers.as_mut_ptr().add(vm.window_start));
    } else {
         let end_addr = vm.scan_function_end(prog, address);
         vm.run_jit_function(prog, address, end_addr);
    }
    
    let state = vm.call_states.pop().unwrap();
    let source_reg = vm.window_start + state.result_reg as usize;
    let target_reg = state.window_start + state.target_reg as usize;
    vm.registers.swap(source_reg, target_reg);
    
    vm.window_start = old_ws;
}

unsafe extern "C" fn helper_tail_call_symbol(vm: *mut Vm, prog: *mut VirtualProgram, func_reg: usize, param_start: usize) {

    let vm = &mut *vm;
    let prog = &mut *prog;

    let func = vm.registers[func_reg + vm.window_start].clone();
    let resolved_func = if let Value::Ref(r) = &func {
        r.borrow().clone()
    } else {
        func
    };

    let (header, address, captures) = match resolved_func {
        Value::FuncRef(f) => (f.header, f.address, None),
        Value::Closure(c) => (c.function.header, c.function.address, Some(c.captures.clone())),
        _ => return
    };

    let size = vm.window_start + header.register_count as usize;
    if size >= vm.registers.len() {
        vm.registers.resize(size, Value::Empty);
    }

    let mut params: Vec<Value> = Vec::new();
    for i in 0..(header.param_count as usize) {
        let idx = vm.window_start + param_start + i;
        params.push(vm.registers[idx].clone());
    }
    for (i, param) in params.into_iter().enumerate() {
        let target_reg = vm.window_start + i;
        vm.registers[target_reg] = param;
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

    let end_addr = vm.scan_function_end(prog, address);
    vm.run_jit_function(prog, address, end_addr);
}
