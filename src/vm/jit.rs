use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use cranelift::prelude::*;
use cranelift::codegen::ir::BlockArg;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, Linkage, Module};
use crate::vm::vp::{Value as LispValue, ValueKind, Instr, JumpCondition, VirtualProgram, FunctionHeader, HeapValue};
use crate::vm::vm::Vm;
use crate::vm::gc::Arena;

pub mod jit_types;
pub mod analysis;
pub mod vm_helpers;

use self::jit_types::JitType;
use self::analysis::{analyze_function, scan_function_end};
use self::vm_helpers::*;

pub struct Jit {
    builder_context: FunctionBuilderContext,
    ctx: codegen::Context,
    _data_ctx: DataDescription,
    module: JITModule,
    cache: HashMap<u64, *const u8>,
    fast_cache: HashMap<u64, *const u8>,
    signatures: HashMap<u64, (Vec<JitType>, JitType)>,
    pending_funcs: HashMap<u64, cranelift_module::FuncId>,
    pub function_map: Arc<Mutex<Vec<(usize, usize, String)>>>,
}

impl Jit {
    pub fn new() -> Self {
        let mut flag_builder = settings::builder();
        flag_builder.set("use_colocated_libcalls", "false").unwrap();
        flag_builder.set("is_pic", "false").unwrap();
        flag_builder.set("preserve_frame_pointers", "true").unwrap();
        flag_builder.set("opt_level", "speed").unwrap();
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
        builder.symbol("helper_call_function", helper_call_function as *const u8);
        builder.symbol("helper_load_string", helper_load_string as *const u8);
        builder.symbol("helper_load_symbol", helper_load_symbol as *const u8);
        builder.symbol("helper_car", helper_car as *const u8);
        builder.symbol("helper_cdr", helper_cdr as *const u8);
        builder.symbol("helper_cons", helper_cons as *const u8);
        builder.symbol("helper_is_pair", helper_is_pair as *const u8);
        builder.symbol("helper_is_null", helper_is_null as *const u8);
        builder.symbol("helper_is_eq", helper_is_eq as *const u8);
        builder.symbol("helper_prepare_map", helper_prepare_map as *const u8);
        builder.symbol("helper_ret", helper_ret as *const u8);

        let module = JITModule::new(builder);
        
        Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            _data_ctx: DataDescription::new(),
            module,
            cache: HashMap::new(),
            fast_cache: HashMap::new(),
            signatures: HashMap::new(),
            pending_funcs: HashMap::new(),
            function_map: Arc::new(Mutex::new(Vec::new())),
        }
    }

    fn generate_wrapper(&mut self, prog: &mut VirtualProgram, start_addr: u64, fast_ptr: *const u8) -> Option<*const u8> {
        let (param_types, main_type) = self.signatures.get(&start_addr)?;
        let param_count = param_types.len();
        let cranelift_type = match main_type {
            JitType::Int => types::I64,
            JitType::Float => types::F32,
        };
        
        let original_pos = prog.cursor.position();
        let header_addr = start_addr - std::mem::size_of::<FunctionHeader>() as u64;
        prog.cursor.set_position(header_addr);
        let header = FunctionHeader::read(&mut prog.cursor);
        prog.cursor.set_position(original_pos);

        let mut wrapper_ctx = codegen::Context::new();
        wrapper_ctx.func.signature.clear(self.module.isa().default_call_conv());
        let ptr_type = self.module.target_config().pointer_type();
        wrapper_ctx.func.signature.params.push(AbiParam::new(ptr_type)); // vm
        wrapper_ctx.func.signature.params.push(AbiParam::new(ptr_type)); // prog
        wrapper_ctx.func.signature.params.push(AbiParam::new(ptr_type)); // registers
        
        let mut builder_context = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut wrapper_ctx.func, &mut builder_context);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        
        let regs_ptr = builder.block_params(entry)[2];
        
        let mut args = Vec::new();
        for i in 0..param_count {
             let offset = (i as i32) * 8;
             let val = builder.ins().load(types::I64, MemFlags::trusted(), regs_ptr, offset);
             let arg = if *main_type == JitType::Float {
                 let shifted = builder.ins().ushr_imm(val, 32);
                 let truncated = builder.ins().ireduce(types::I32, shifted);
                 builder.ins().bitcast(types::F32, MemFlags::new(), truncated)
             } else {
                 val
             };
             args.push(arg);
        }
        
        let fast_ptr_val = fast_ptr as usize as i64;
        let callee = builder.ins().iconst(types::I64, fast_ptr_val);
        
        let mut sig = self.module.make_signature();
        sig.call_conv = isa::CallConv::Tail;
        for _ in 0..param_count {
            sig.params.push(AbiParam::new(cranelift_type));
        }
        sig.returns.push(AbiParam::new(cranelift_type));
        
        let sig_ref = builder.import_signature(sig);
        
        let call = builder.ins().call_indirect(sig_ref, callee, &args);
        let res = builder.inst_results(call)[0];
        
        let res_reg = header.result_reg as i32;
        let offset = res_reg * 8;
        
        let res_store = if *main_type == JitType::Float {
            let bits = builder.ins().bitcast(types::I32, MemFlags::new(), res);
            let extended = builder.ins().uextend(types::I64, bits);
            let shifted = builder.ins().ishl_imm(extended, 32);
            builder.ins().bor_imm(shifted, 2) // TAG_FLOAT
        } else {
            res
        };
        
        builder.ins().store(MemFlags::trusted(), res_store, regs_ptr, offset);
        
        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize();
        
        let wrapper_name = format!("wrapper_{}", start_addr);
        let wrapper_id = match self.module.declare_function(&wrapper_name, Linkage::Local, &wrapper_ctx.func.signature) {
            Ok(id) => id,
            Err(e) => { println!("Declare wrapper failed: {}", e); return None; }
        };
        if let Err(e) = self.module.define_function(wrapper_id, &mut wrapper_ctx) {
            println!("Define wrapper failed: {:?}", e);
            return None;
        }
        if let Err(e) = self.module.finalize_definitions() {
             println!("Finalize wrapper failed: {}", e);
             return None;
        }
        Some(self.module.get_finalized_function(wrapper_id))
    }

    fn try_compile_fast(&mut self, global_vars: &Vec<LispValue>, heap: &Arena<HeapValue>, prog: &mut VirtualProgram, start_addr: u64, end_addr: u64) -> Option<*const u8> {
        if let Some(&code) = self.fast_cache.get(&start_addr) {
            return self.generate_wrapper(prog, start_addr, code);
        }

        self.pending_funcs.clear();
        
        let _ = self.compile_fast_internal(global_vars, heap, prog, start_addr, end_addr)?;
        
        if let Err(e) = self.module.finalize_definitions() {
             println!("Finalize definitions failed: {}", e);
             return None;
        }
        
        for (addr, id) in &self.pending_funcs {
            let ptr = self.module.get_finalized_function(*id);
            self.fast_cache.insert(*addr, ptr);
        }
        
        self.pending_funcs.clear();
        
        let fast_ptr = self.fast_cache.get(&start_addr)?;
        self.generate_wrapper(prog, start_addr, *fast_ptr)
    }

    fn compile_fast_internal(&mut self, global_vars: &Vec<LispValue>, heap: &Arena<HeapValue>, prog: &mut VirtualProgram, start_addr: u64, end_addr: u64) -> Option<cranelift_module::FuncId> {
        if let Some(&id) = self.pending_funcs.get(&start_addr) {
            return Some(id);
        }
        
        let original_pos = prog.cursor.position();
        let header_addr = start_addr - std::mem::size_of::<FunctionHeader>() as u64;
        prog.cursor.set_position(header_addr);
        let header = FunctionHeader::read(&mut prog.cursor);
        
        if header.param_count > 6 {
            prog.cursor.set_position(original_pos);
            return None;
        }

        let (param_types, main_type, _) = match analyze_function(prog, start_addr, end_addr, header.param_count) {
            Some(res) => res,
            None => {
                prog.cursor.set_position(original_pos);
                return None;
            }
        };
        self.signatures.insert(start_addr, (param_types.clone(), main_type));

        let cranelift_type = match main_type {
            JitType::Int => types::I64,
            JitType::Float => types::F32,
        };

        let mut ctx = codegen::Context::new();
        ctx.func.signature.clear(isa::CallConv::Tail);
        
        for _ in 0..header.param_count {
            ctx.func.signature.params.push(AbiParam::new(cranelift_type));
        }
        ctx.func.signature.returns.push(AbiParam::new(cranelift_type));
        
        let fast_name = format!("fast_{}", start_addr);
        let fast_func_id = match self.module.declare_function(&fast_name, Linkage::Local, &ctx.func.signature) {
            Ok(id) => id,
            Err(e) => { println!("Declare func failed: {}", e); prog.cursor.set_position(original_pos); return None; }
        };
        
        self.pending_funcs.insert(start_addr, fast_func_id);
        
        let mut builder_context = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
        
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        
        let mut vars = Vec::new();
        for i in 0..header.register_count {
            let var = Variable::new(i as usize);
            builder.declare_var(var, cranelift_type);
            vars.push(var);
        }

        for i in 0..header.param_count {
            let val = builder.block_params(entry_block)[i as usize];
            builder.def_var(vars[i as usize], val);
        }
        
        let body_block = builder.create_block();
        builder.ins().jump(body_block, &[]);
        
        let mut blocks = HashMap::new();
        blocks.insert(start_addr, body_block);
        
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
                    None => { prog.cursor.set_position(original_pos); return None; }
                };
                let instr: Instr = match opcode[0].try_into() {
                    Ok(i) => i,
                    Err(_) => { prog.cursor.set_position(original_pos); return None; }
                };
                
                match instr {
                    Instr::Jump => {
                        let dist = prog.read_int().unwrap_or(0);
                        let target = (prog.cursor.position() as i64 + dist) as u64;
                        if !blocks.contains_key(&target) {
                            blocks.insert(target, builder.create_block());
                            worklist.push(target);
                        }
                        if opcode[2] != JumpCondition::Jump as u8 {
                             let fallthrough = prog.cursor.position();
                             if !blocks.contains_key(&fallthrough) {
                                 blocks.insert(fallthrough, builder.create_block());
                                 worklist.push(fallthrough);
                             }
                        }
                        if opcode[2] == JumpCondition::Jump as u8 {
                            break;
                        }
                    },
                    Instr::Not => {
                        let pos = prog.cursor.position();
                        if let Some(next_op) = prog.read_opcode() {
                            if let Ok(Instr::Jump) = next_op[0].try_into() {
                                let dist = prog.read_int().unwrap_or(0);
                                let target = (prog.cursor.position() as i64 + dist) as u64;
                                let fallthrough = prog.cursor.position();
                                
                                if !blocks.contains_key(&target) {
                                    blocks.insert(target, builder.create_block());
                                    worklist.push(target);
                                }
                                if !blocks.contains_key(&fallthrough) {
                                    blocks.insert(fallthrough, builder.create_block());
                                    worklist.push(fallthrough);
                                }
                                break;
                            }
                        }
                        prog.cursor.set_position(pos);
                    },
                    Instr::Ret => break,
                    _ => {
                        match instr {
                            Instr::LoadInt | Instr::LoadFloat | Instr::LoadGlobal | Instr::Define | Instr::LoadFuncRef => { prog.read_int(); },
                            Instr::LoadString => { prog.read_string(); },
                            Instr::TailCallSymbol => {
                                prog.read_int(); // param_start
                                prog.read_int(); // target_reg
                            },
                            Instr::Map | Instr::ForEach | Instr::Fold | Instr::FilterStep => { prog.read_byte(); },
                            Instr::Filter => { prog.read_byte(); prog.read_byte(); },
                            Instr::MakeClosure => {
                                let count = opcode[3];
                                for _ in 0..count {
                                    prog.read_byte();
                                }
                            },
                            _ => {}
                        }
                    }
                }
            }
        }
        
        let mut sorted_blocks: Vec<u64> = blocks.keys().cloned().collect();
        sorted_blocks.sort();
        
        builder.seal_block(entry_block);

        let mut const_funcs: HashMap<usize, u64> = HashMap::new();

        // Macros for compact instruction generation
        macro_rules! emit_arithmetic {
            ($builder:expr, $vars:expr, $opcode:expr, $main_type:expr, $const_funcs:expr, $int_func:ident, $float_func:ident) => {{
                let v1 = $builder.use_var($vars[$opcode[2] as usize]);
                let v2 = $builder.use_var($vars[$opcode[3] as usize]);
                let res = if $main_type == JitType::Float {
                    $builder.ins().$float_func(v1, v2)
                } else {
                    let i1 = $builder.ins().sshr_imm(v1, 3);
                    let i2 = $builder.ins().sshr_imm(v2, 3);
                    let r = $builder.ins().$int_func(i1, i2);
                    let s = $builder.ins().ishl_imm(r, 3);
                    $builder.ins().bor_imm(s, 1)
                };
                $builder.def_var($vars[$opcode[1] as usize], res);
                $const_funcs.remove(&($opcode[1] as usize));
            }};
        }

        macro_rules! emit_cmp {
            ($builder:expr, $vars:expr, $opcode:expr, $main_type:expr, $const_funcs:expr, $int_cc:expr, $float_cc:expr) => {{
                let v1 = $builder.use_var($vars[$opcode[2] as usize]);
                let v2 = $builder.use_var($vars[$opcode[3] as usize]);
                let res = if $main_type == JitType::Float {
                    $builder.ins().fcmp($float_cc, v1, v2)
                } else {
                    let i1 = $builder.ins().sshr_imm(v1, 3);
                    let i2 = $builder.ins().sshr_imm(v2, 3);
                    $builder.ins().icmp($int_cc, i1, i2)
                };
                let val = if $main_type == JitType::Float {
                    let b_int = $builder.ins().uextend(types::I64, res);
                    $builder.ins().fcvt_from_uint(types::F32, b_int)
                } else {
                    let t = $builder.ins().iconst(types::I64, 35);
                    let f = $builder.ins().iconst(types::I64, 19);
                    $builder.ins().select(res, t, f)
                };
                $builder.def_var($vars[$opcode[1] as usize], val);
                $const_funcs.remove(&($opcode[1] as usize));
            }};
        }

        for addr in sorted_blocks {
            let block = blocks[&addr];
            builder.switch_to_block(block);
            
            prog.cursor.set_position(addr);
            
            loop {
                let current_pos = prog.cursor.position();
                if current_pos != addr && blocks.contains_key(&current_pos) {
                    let next_block = blocks[&current_pos];
                    builder.ins().jump(next_block, &[]);
                    break;
                }

                if prog.cursor.position() >= end_addr { break; }
                let opcode = prog.read_opcode().unwrap();
                let instr: Instr = opcode[0].try_into().unwrap();
                
                match instr {
                    Instr::TailCallSymbol => {
                        let func_reg = opcode[1] as usize;
                        let target_addr = if let Some(&addr) = const_funcs.get(&func_reg) {
                            addr
                        } else {
                            prog.cursor.set_position(original_pos);
                            return None;
                        };

                        let target_end = scan_function_end(prog, target_addr);
                        let h_addr = target_addr - std::mem::size_of::<FunctionHeader>() as u64;
                        let pos = prog.cursor.position();
                        prog.cursor.set_position(h_addr);
                        let h = FunctionHeader::read(&mut prog.cursor);
                        prog.cursor.set_position(pos);
                        
                        let (_, tgt_ret, _) = analyze_function(prog, target_addr, target_end, h.param_count)?;
                        
                        if tgt_ret != main_type {
                            prog.cursor.set_position(original_pos);
                            return None;
                        }
                        
                        let param_start = opcode[2];
                        let _target_reg = opcode[3];
                        
                        let mut args = Vec::new();
                        for i in 0..h.param_count {
                            let arg_reg = param_start + i;
                            args.push(builder.use_var(vars[arg_reg as usize]));
                        }
                        
                        if let Some(&tgt_id) = self.pending_funcs.get(&target_addr) {
                             let local_tgt = self.module.declare_func_in_func(tgt_id, &mut builder.func);
                             builder.ins().return_call(local_tgt, &args);
                             break;
                        } else if let Some(&tgt_ptr) = self.fast_cache.get(&target_addr) {
                             let tgt_ptr_val = tgt_ptr as usize as i64;
                             let callee = builder.ins().iconst(types::I64, tgt_ptr_val);
                             let mut sig = self.module.make_signature();
                             sig.call_conv = isa::CallConv::Tail;
                             for _ in 0..h.param_count { sig.params.push(AbiParam::new(cranelift_type)); }
                             sig.returns.push(AbiParam::new(cranelift_type));
                             let sig_ref = builder.import_signature(sig);
                             builder.ins().return_call_indirect(sig_ref, callee, &args);
                             break;
                        } else {
                             if let Some(tgt_id) = self.compile_fast_internal(global_vars, heap, prog, target_addr, target_end) {
                                 let local_tgt = self.module.declare_func_in_func(tgt_id, &mut builder.func);
                                 builder.ins().return_call(local_tgt, &args);
                                 break;
                             } else {
                                 prog.cursor.set_position(original_pos);
                                 return None;
                             }
                        }
                    },
                    Instr::LoadInt => {
                        let val = prog.read_int().unwrap();
                        let v = if main_type == JitType::Float {
                            builder.ins().f32const(val as f32)
                        } else {
                            let c = builder.ins().iconst(types::I64, val);
                            let s = builder.ins().ishl_imm(c, 3);
                            builder.ins().bor_imm(s, 1)
                        };
                        builder.def_var(vars[opcode[1] as usize], v);
                        const_funcs.remove(&(opcode[1] as usize));
                    },
                    Instr::LoadFloat => {
                        let val = prog.read_float().unwrap();
                        let v = if main_type == JitType::Float {
                            builder.ins().f32const(val as f32)
                        } else {
                            builder.ins().iconst(types::I64, val as i64)
                        };
                        builder.def_var(vars[opcode[1] as usize], v);
                        const_funcs.remove(&(opcode[1] as usize));
                    },
                    Instr::LoadBool => {
                        let dest = opcode[1] as usize;
                        let val = opcode[2] != 0;
                        let v = if main_type == JitType::Float {
                            builder.ins().f32const(if val { 1.0 } else { 0.0 })
                        } else {
                            builder.ins().iconst(types::I64, if val { 35 } else { 19 }) // IMM_TRUE / IMM_FALSE
                        };
                        builder.def_var(vars[dest], v);
                        const_funcs.remove(&dest);
                    },
                    Instr::CopyReg => {
                        let v = builder.use_var(vars[opcode[2] as usize]);
                        builder.def_var(vars[opcode[1] as usize], v);
                        if let Some(&addr) = const_funcs.get(&(opcode[2] as usize)) {
                            const_funcs.insert(opcode[1] as usize, addr);
                        } else {
                            const_funcs.remove(&(opcode[1] as usize));
                        }
                    },
                    Instr::Add => emit_arithmetic!(builder, vars, opcode, main_type, const_funcs, iadd, fadd),
                    Instr::Sub => emit_arithmetic!(builder, vars, opcode, main_type, const_funcs, isub, fsub),
                    Instr::Mul => emit_arithmetic!(builder, vars, opcode, main_type, const_funcs, imul, fmul),
                    Instr::Div => emit_arithmetic!(builder, vars, opcode, main_type, const_funcs, sdiv, fdiv),
                    Instr::Lt => emit_cmp!(builder, vars, opcode, main_type, const_funcs, IntCC::SignedLessThan, FloatCC::LessThan),
                    Instr::Gt => emit_cmp!(builder, vars, opcode, main_type, const_funcs, IntCC::SignedGreaterThan, FloatCC::GreaterThan),
                    Instr::Eq => emit_cmp!(builder, vars, opcode, main_type, const_funcs, IntCC::Equal, FloatCC::Equal),
                    Instr::LoadGlobal => {
                        let sym_id = prog.read_int().unwrap();
                        if let Some(val) = global_vars.get(sym_id as usize) {
                            let addr = match val.kind() {
                                ValueKind::Object(handle) => match heap.get(handle) {
                                    Some(HeapValue::FuncRef(f)) => Some(f.address),
                                    _ => None
                                },
                                _ => None
                            };
                            
                            if let Some(address) = addr {
                                const_funcs.insert(opcode[1] as usize, address);
                            } else {
                                const_funcs.remove(&(opcode[1] as usize));
                            }
                        }
                    },
                    Instr::CallSymbol => {
                        let func_reg = opcode[1] as usize;
                        let target_addr = if let Some(&addr) = const_funcs.get(&func_reg) {
                            addr
                        } else {
                            prog.cursor.set_position(original_pos);
                            return None;
                        };

                        let target_end = scan_function_end(prog, target_addr);
                        let h_addr = target_addr - std::mem::size_of::<FunctionHeader>() as u64;
                        let pos = prog.cursor.position();
                        prog.cursor.set_position(h_addr);
                        let h = FunctionHeader::read(&mut prog.cursor);
                        prog.cursor.set_position(pos);
                        
                        let (_, tgt_ret, _) = analyze_function(prog, target_addr, target_end, h.param_count)?;
                        
                        if tgt_ret != main_type {
                            prog.cursor.set_position(original_pos);
                            return None;
                        }
                        
                        let param_start = opcode[2];
                        let target_reg = opcode[3];
                        
                        let mut args = Vec::new();
                        for i in 0..h.param_count {
                            let arg_reg = param_start + i;
                            args.push(builder.use_var(vars[arg_reg as usize]));
                        }
                        
                        if let Some(&tgt_id) = self.pending_funcs.get(&target_addr) {
                             let local_tgt = self.module.declare_func_in_func(tgt_id, &mut builder.func);
                             let call = builder.ins().call(local_tgt, &args);
                             let res = builder.inst_results(call)[0];
                             builder.def_var(vars[target_reg as usize], res);
                        } else if let Some(&tgt_ptr) = self.fast_cache.get(&target_addr) {
                             let tgt_ptr_val = tgt_ptr as usize as i64;
                             let callee = builder.ins().iconst(types::I64, tgt_ptr_val);
                             let mut sig = self.module.make_signature();
                             sig.call_conv = isa::CallConv::Tail;
                             for _ in 0..h.param_count { sig.params.push(AbiParam::new(cranelift_type)); }
                             sig.returns.push(AbiParam::new(cranelift_type));
                             let sig_ref = builder.import_signature(sig);
                             let call = builder.ins().call_indirect(sig_ref, callee, &args);
                             let res = builder.inst_results(call)[0];
                             builder.def_var(vars[target_reg as usize], res);
                        } else {
                             if let Some(tgt_id) = self.compile_fast_internal(global_vars, heap, prog, target_addr, target_end) {
                                 let local_tgt = self.module.declare_func_in_func(tgt_id, &mut builder.func);
                                 let call = builder.ins().call(local_tgt, &args);
                                 let res = builder.inst_results(call)[0];
                                 builder.def_var(vars[target_reg as usize], res);
                             } else {
                                 prog.cursor.set_position(original_pos);
                                 return None;
                             }
                        }
                        const_funcs.remove(&(target_reg as usize));
                    },
                    Instr::Not => {
                        let pos = prog.cursor.position();
                        let fused = false;
                        if let Some(next_op) = prog.read_opcode() {
                            if let Ok(Instr::Jump) = next_op[0].try_into() {
                                let dist = prog.read_int().unwrap();
                                let target = (prog.cursor.position() as i64 + dist) as u64;
                                let fallthrough = prog.cursor.position();
                                
                                let cond_val = builder.use_var(vars[opcode[2] as usize]);
                                let cond_bool = if main_type == JitType::Float {
                                    let zero = builder.ins().f32const(0.0);
                                    builder.ins().fcmp(FloatCC::NotEqual, cond_val, zero)
                                } else {
                                    builder.ins().icmp_imm(IntCC::NotEqual, cond_val, 19) // IMM_FALSE
                                };
                                let not_cond = builder.ins().bnot(cond_bool);
                                
                                let target_block = blocks[&target];
                                let fallthrough_block = blocks[&fallthrough];
                                
                                if next_op[2] == JumpCondition::JumpTrue as u8 {
                                    builder.ins().brif(not_cond, target_block, &[], fallthrough_block, &[]);
                                } else {
                                    builder.ins().brif(not_cond, fallthrough_block, &[], target_block, &[]);
                                }
                                
                                break;
                            }
                        }
                        if !fused {
                            prog.cursor.set_position(pos);
                            let v = builder.use_var(vars[opcode[2] as usize]);
                            let b = if main_type == JitType::Float {
                                let zero = builder.ins().f32const(0.0);
                                builder.ins().fcmp(FloatCC::Equal, v, zero)
                            } else {
                                builder.ins().icmp_imm(IntCC::Equal, v, 19) // IMM_FALSE
                            };
                            let res = if main_type == JitType::Float {
                                let b_int = builder.ins().uextend(types::I64, b);
                                builder.ins().fcvt_from_uint(types::F32, b_int)
                            } else {
                                let t = builder.ins().iconst(types::I64, 35);
                                let f = builder.ins().iconst(types::I64, 19);
                                builder.ins().select(b, t, f)
                            };
                            builder.def_var(vars[opcode[1] as usize], res);
                            const_funcs.remove(&(opcode[1] as usize));
                        }
                    },
                    Instr::Jump => {
                        let dist = prog.read_int().unwrap();
                        let target = (prog.cursor.position() as i64 + dist) as u64;
                        let target_block = blocks[&target];
                        
                        if opcode[2] == JumpCondition::Jump as u8 {
                            builder.ins().jump(target_block, &[]);
                        } else {
                            let v = builder.use_var(vars[opcode[1] as usize]);
                            let cond = if main_type == JitType::Float {
                                let zero = builder.ins().f32const(0.0);
                                builder.ins().fcmp(FloatCC::NotEqual, v, zero)
                            } else {
                                builder.ins().icmp_imm(IntCC::NotEqual, v, 19) // IMM_FALSE
                            };
                            let fallthrough = prog.cursor.position();
                            let fallthrough_block = blocks[&fallthrough];
                            
                            if opcode[2] == JumpCondition::JumpTrue as u8 {
                                builder.ins().brif(cond, target_block, &[], fallthrough_block, &[]);
                            } else {
                                builder.ins().brif(cond, fallthrough_block, &[], target_block, &[]);
                            }
                        }
                        break;
                    },
                    Instr::Ret => {
                        let res = builder.use_var(vars[header.result_reg as usize]);
                        builder.ins().return_(&[res]);
                        break;
                    },
                    _ => {
                        println!("Fast JIT: Unsupported instr {:?} (in default arm)", instr);
                        prog.cursor.set_position(original_pos);
                        return None;
                    }
                }
            }
        }
        
        builder.seal_all_blocks();
        builder.finalize();
        
        if let Err(e) = self.module.define_function(fast_func_id, &mut ctx) {
            println!("Define fast func failed: {:?}", e);
            prog.cursor.set_position(original_pos);
            return None;
        }
        
        prog.cursor.set_position(original_pos);
        Some(fast_func_id)
    }

    pub fn is_compiled(&self, start_addr: u64) -> bool {
        self.cache.contains_key(&start_addr)
    }

    pub fn compile(&mut self, global_vars: &Vec<LispValue>, heap: &Arena<HeapValue>, prog: &mut VirtualProgram, start_addr: u64, end_addr: u64) -> Result<fn(*mut Vm, *mut VirtualProgram, *mut LispValue), String> {
        self.module.clear_context(&mut self.ctx);
        
        if let Some(&code) = self.cache.get(&start_addr) {
            return Ok(unsafe { std::mem::transmute(code) });
        }

        if let Some(wrapper) = self.try_compile_fast(global_vars, heap, prog, start_addr, end_addr) {
            self.cache.insert(start_addr, wrapper);
            return Ok(unsafe { std::mem::transmute(wrapper) });
        }

        // Clear context if Fast JIT failed, as it might have left partial state
        self.module.clear_context(&mut self.ctx);
        self.ctx.func.signature.clear(self.module.isa().default_call_conv());
        self.builder_context = FunctionBuilderContext::new();

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
                
                // println!("Pass 1: {:?} at {}", instr, prog.current_address() - 4);

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
                    Instr::LoadInt | Instr::LoadFloat | Instr::Define | Instr::LoadGlobal | Instr::LoadFuncRef | Instr::CallFunction => {
                        let _ = prog.read_int();
                    },
                    Instr::LoadString | Instr::LoadSymbol => {
                        let _ = prog.read_string();
                    },
                    Instr::MakeClosure => {
                        let count = opcode[3];
                        for _ in 0..count {
                            let _ = prog.read_byte();
                        }
                    },
                    Instr::Map | Instr::FilterStep => {
                        let _ = prog.read_byte();
                        let target = prog.current_address() + 16;
                        if !block_starts.contains(&target) {
                            block_starts.insert(target);
                            queue.push(target);
                        }
                    },
                    Instr::ForEach | Instr::Fold => {
                        let _ = prog.read_byte();
                        let target = prog.current_address() + 12;
                        if !block_starts.contains(&target) {
                            block_starts.insert(target);
                            queue.push(target);
                        }
                    },
                    Instr::Filter => {
                        let _ = prog.read_byte();
                        let _ = prog.read_byte();
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

        let mut sig_helper_call_function = self.module.make_signature();
        sig_helper_call_function.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_call_function.params.push(AbiParam::new(ptr_type)); // prog
        sig_helper_call_function.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_call_function.params.push(AbiParam::new(types::I64)); // dest_reg
        sig_helper_call_function.params.push(AbiParam::new(types::I64)); // start_reg
        sig_helper_call_function.params.push(AbiParam::new(types::I64)); // reg_count
        sig_helper_call_function.params.push(AbiParam::new(types::I64)); // func_id
        let callee_helper_call_function = self.module.declare_function("helper_call_function", Linkage::Import, &sig_helper_call_function).map_err(|e| e.to_string())?;
        let local_helper_call_function = self.module.declare_func_in_func(callee_helper_call_function, &mut builder.func);

        let mut sig_helper_load_string = self.module.make_signature();
        sig_helper_load_string.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_load_string.params.push(AbiParam::new(ptr_type)); // prog
        sig_helper_load_string.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_load_string.params.push(AbiParam::new(types::I64)); // dest_reg
        sig_helper_load_string.params.push(AbiParam::new(types::I64)); // offset
        let callee_helper_load_string = self.module.declare_function("helper_load_string", Linkage::Import, &sig_helper_load_string).map_err(|e| e.to_string())?;
        let local_helper_load_string = self.module.declare_func_in_func(callee_helper_load_string, &mut builder.func);

        let mut sig_helper_load_symbol = self.module.make_signature();
        sig_helper_load_symbol.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_load_symbol.params.push(AbiParam::new(ptr_type)); // prog
        sig_helper_load_symbol.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_load_symbol.params.push(AbiParam::new(types::I64)); // dest_reg
        sig_helper_load_symbol.params.push(AbiParam::new(types::I64)); // offset
        let callee_helper_load_symbol = self.module.declare_function("helper_load_symbol", Linkage::Import, &sig_helper_load_symbol).map_err(|e| e.to_string())?;
        let local_helper_load_symbol = self.module.declare_func_in_func(callee_helper_load_symbol, &mut builder.func);

        let mut sig_helper_car = self.module.make_signature();
        sig_helper_car.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_car.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_car.params.push(AbiParam::new(types::I64)); // dest_reg
        sig_helper_car.params.push(AbiParam::new(types::I64)); // arg_reg
        let callee_helper_car = self.module.declare_function("helper_car", Linkage::Import, &sig_helper_car).map_err(|e| e.to_string())?;
        let local_helper_car = self.module.declare_func_in_func(callee_helper_car, &mut builder.func);

        let mut sig_helper_cdr = self.module.make_signature();
        sig_helper_cdr.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_cdr.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_cdr.params.push(AbiParam::new(types::I64)); // dest_reg
        sig_helper_cdr.params.push(AbiParam::new(types::I64)); // arg_reg
        let callee_helper_cdr = self.module.declare_function("helper_cdr", Linkage::Import, &sig_helper_cdr).map_err(|e| e.to_string())?;
        let local_helper_cdr = self.module.declare_func_in_func(callee_helper_cdr, &mut builder.func);

        let mut sig_helper_cons = self.module.make_signature();
        sig_helper_cons.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_cons.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_cons.params.push(AbiParam::new(types::I64)); // dest_reg
        sig_helper_cons.params.push(AbiParam::new(types::I64)); // car_reg
        sig_helper_cons.params.push(AbiParam::new(types::I64)); // cdr_reg
        let callee_helper_cons = self.module.declare_function("helper_cons", Linkage::Import, &sig_helper_cons).map_err(|e| e.to_string())?;
        let local_helper_cons = self.module.declare_func_in_func(callee_helper_cons, &mut builder.func);

        let mut sig_helper_is_pair = self.module.make_signature();
        sig_helper_is_pair.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_is_pair.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_is_pair.params.push(AbiParam::new(types::I64)); // dest_reg
        sig_helper_is_pair.params.push(AbiParam::new(types::I64)); // arg_reg
        let callee_helper_is_pair = self.module.declare_function("helper_is_pair", Linkage::Import, &sig_helper_is_pair).map_err(|e| e.to_string())?;
        let local_helper_is_pair = self.module.declare_func_in_func(callee_helper_is_pair, &mut builder.func);

        let mut sig_helper_is_null = self.module.make_signature();
        sig_helper_is_null.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_is_null.params.push(AbiParam::new(types::I64)); // dest_reg
        sig_helper_is_null.params.push(AbiParam::new(types::I64)); // arg_reg
        let callee_helper_is_null = self.module.declare_function("helper_is_null", Linkage::Import, &sig_helper_is_null).map_err(|e| e.to_string())?;
        let local_helper_is_null = self.module.declare_func_in_func(callee_helper_is_null, &mut builder.func);

        let mut sig_helper_is_eq = self.module.make_signature();
        sig_helper_is_eq.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_is_eq.params.push(AbiParam::new(types::I64)); // dest_reg
        sig_helper_is_eq.params.push(AbiParam::new(types::I64)); // arg1_reg
        sig_helper_is_eq.params.push(AbiParam::new(types::I64)); // arg2_reg
        let callee_helper_is_eq = self.module.declare_function("helper_is_eq", Linkage::Import, &sig_helper_is_eq).map_err(|e| e.to_string())?;
        let local_helper_is_eq = self.module.declare_func_in_func(callee_helper_is_eq, &mut builder.func);

        let mut sig_helper_prepare_map = self.module.make_signature();
        sig_helper_prepare_map.params.push(AbiParam::new(ptr_type)); // vm
        sig_helper_prepare_map.params.push(AbiParam::new(ptr_type)); // prog
        sig_helper_prepare_map.params.push(AbiParam::new(ptr_type)); // registers
        sig_helper_prepare_map.params.push(AbiParam::new(types::I64)); // func_reg
        sig_helper_prepare_map.params.push(AbiParam::new(types::I64)); // list_reg
        sig_helper_prepare_map.params.push(AbiParam::new(types::I64)); // temp_reg
        sig_helper_prepare_map.returns.push(AbiParam::new(types::I64)); // jit_code_addr
        let callee_helper_prepare_map = self.module.declare_function("helper_prepare_map", Linkage::Import, &sig_helper_prepare_map).map_err(|e| e.to_string())?;
        let local_helper_prepare_map = self.module.declare_func_in_func(callee_helper_prepare_map, &mut builder.func);

        let mut sig_helper_ret = self.module.make_signature();
        sig_helper_ret.params.push(AbiParam::new(ptr_type)); // vm
        let callee_helper_ret = self.module.declare_function("helper_ret", Linkage::Import, &sig_helper_ret).map_err(|e| e.to_string())?;
        let local_helper_ret = self.module.declare_func_in_func(callee_helper_ret, &mut builder.func);

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
                    Instr::Jump | Instr::LoadInt | Instr::LoadGlobal | Instr::Define | Instr::LoadFuncRef | Instr::LoadFloat | Instr::CallFunction => {
                        prog.read_int().unwrap();
                    },
                    Instr::LoadString | Instr::LoadSymbol => {
                        prog.read_string().unwrap();
                    },
                    Instr::MakeClosure => {
                        let count = opcode[3];
                        for _ in 0..count {
                            prog.read_byte().unwrap();
                        }
                    },
                    Instr::Map | Instr::ForEach | Instr::Fold | Instr::FilterStep => {
                        prog.read_byte().unwrap();
                    },
                    Instr::Filter => {
                        prog.read_byte().unwrap();
                        prog.read_byte().unwrap();
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
                        let val_size = 8;
                        let reg_ptr = builder.ins().iadd_imm(registers_ptr, reg_idx * val_size);
                        
                        let val = builder.ins().load(types::I64, MemFlags::trusted(), reg_ptr, 0);
                        
                        // IMM_FALSE = 19
                        let is_false = builder.ins().icmp_imm(IntCC::Equal, val, 19);
                        
                        let fallthrough_block = *blocks.get(&after_read_pos).ok_or("Fallthrough block not found")?;

                        if cond_byte == JumpCondition::JumpTrue as u8 {
                            // Jump if !is_false (i.e. is_true)
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
                    
                    let val_size = 8;
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let val_const = builder.ins().iconst(types::I64, val);
                    let val_shifted = builder.ins().ishl_imm(val_const, 3);
                    let raw = builder.ins().bor_imm(val_shifted, 1);
                    
                    builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                    
                    is_terminated = false;
                },
                Instr::LoadFloat => {
                    let dest_reg = opcode[1] as i64;
                    let val_bits = prog.read_int().unwrap();
                    let val = f64::from_bits(val_bits as u64);
                    let val_f32 = val as f32;
                    let bits = val_f32.to_bits() as i64;
                    
                    let val_size = 8;
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let bits_const = builder.ins().iconst(types::I64, bits);
                    let bits_shifted = builder.ins().ishl_imm(bits_const, 32);
                    let raw = builder.ins().bor_imm(bits_shifted, 2);
                    
                    builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                    
                    is_terminated = false;
                },
                Instr::LoadBool => {
                    let dest_reg = opcode[1] as i64;
                    let val = opcode[2] != 0;
                    
                    let val_size = 8;
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let raw_val = if val { 35 } else { 19 };
                    let raw = builder.ins().iconst(types::I64, raw_val);
                    
                    builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                    
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
                Instr::LoadString => {
                    let dest_reg = opcode[1] as i64;
                    let offset = prog.current_address() as i64;
                    prog.read_string().unwrap();
                    
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let offset_const = builder.ins().iconst(types::I64, offset);
                    
                    builder.ins().call(local_helper_load_string, &[vm_ptr, prog_ptr, registers_ptr, dest_reg_const, offset_const]);
                    is_terminated = false;
                },
                Instr::LoadSymbol => {
                    let dest_reg = opcode[1] as i64;
                    let offset = prog.current_address() as i64;
                    prog.read_string().unwrap();
                    
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let offset_const = builder.ins().iconst(types::I64, offset);
                    
                    builder.ins().call(local_helper_load_symbol, &[vm_ptr, prog_ptr, registers_ptr, dest_reg_const, offset_const]);
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
                Instr::CallFunction => {
                    let dest_reg = opcode[1] as i64;
                    let start_reg = opcode[2] as i64;
                    let reg_count = opcode[3] as i64;
                    
                    // Skip func_id in JIT stream (it's read by helper)
                    // Wait, helper reads it from prog. prog cursor must be at the right place.
                    // But JIT compilation scans the code.
                    // When running JIT code, `prog` cursor is NOT updated by JIT code unless we call helpers that do it.
                    // `helper_call_function` reads from `prog`.
                    // But `prog` passed to JIT is the same `prog`.
                    // However, `prog.cursor` position during JIT execution?
                    // JIT execution doesn't use `prog.cursor` for control flow (it uses jumps).
                    // But helpers might use it.
                    // `helper_call_function` reads `func_id`.
                    // We need to ensure `prog.cursor` points to `func_id` when `helper_call_function` is called.
                    // But `prog.cursor` is not maintained by JIT code!
                    // JIT code is just machine code.
                    
                    // Solution: Pass `func_id` explicitly to helper?
                    // But `helper_call_function` reads it from `prog`.
                    // If I change `helper_call_function` to take `func_id`, I can pass it as constant.
                    // `func_id` is in the bytecode stream. I can read it during compilation.
                    
                    let func_id = prog.read_int().unwrap();
                    
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let start_reg_const = builder.ins().iconst(types::I64, start_reg);
                    let reg_count_const = builder.ins().iconst(types::I64, reg_count);
                    let func_id_const = builder.ins().iconst(types::I64, func_id);
                    
                    builder.ins().call(local_helper_call_function, &[vm_ptr, prog_ptr, registers_ptr, dest_reg_const, start_reg_const, reg_count_const, func_id_const]);
                    is_terminated = false;
                },
                Instr::Car => {
                    let dest_reg = opcode[1] as i64;
                    let arg_reg = opcode[2] as i64;
                    
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let arg_reg_const = builder.ins().iconst(types::I64, arg_reg);
                    
                    builder.ins().call(local_helper_car, &[vm_ptr, registers_ptr, dest_reg_const, arg_reg_const]);
                    is_terminated = false;
                },
                Instr::Cdr => {
                    let dest_reg = opcode[1] as i64;
                    let arg_reg = opcode[2] as i64;
                    
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let arg_reg_const = builder.ins().iconst(types::I64, arg_reg);
                    
                    builder.ins().call(local_helper_cdr, &[vm_ptr, registers_ptr, dest_reg_const, arg_reg_const]);
                    is_terminated = false;
                },
                Instr::Cons => {
                    let dest_reg = opcode[1] as i64;
                    let car_reg = opcode[2] as i64;
                    let cdr_reg = opcode[3] as i64;
                    
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let car_reg_const = builder.ins().iconst(types::I64, car_reg);
                    let cdr_reg_const = builder.ins().iconst(types::I64, cdr_reg);
                    
                    builder.ins().call(local_helper_cons, &[vm_ptr, registers_ptr, dest_reg_const, car_reg_const, cdr_reg_const]);
                    
                    // Reload registers_ptr as it might have changed due to GC
                    let call_inst = builder.ins().call(local_helper_get_registers_ptr, &[vm_ptr]);
                    registers_ptr = builder.inst_results(call_inst)[0];
                    
                    is_terminated = false;
                },
                Instr::IsPair => {
                    let dest_reg = opcode[1] as i64;
                    let arg_reg = opcode[2] as i64;
                    
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let arg_reg_const = builder.ins().iconst(types::I64, arg_reg);
                    
                    builder.ins().call(local_helper_is_pair, &[vm_ptr, registers_ptr, dest_reg_const, arg_reg_const]);
                    is_terminated = false;
                },
                Instr::IsNull => {
                    let dest_reg = opcode[1] as i64;
                    let arg_reg = opcode[2] as i64;
                    
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let arg_reg_const = builder.ins().iconst(types::I64, arg_reg);
                    
                    builder.ins().call(local_helper_is_null, &[registers_ptr, dest_reg_const, arg_reg_const]);
                    is_terminated = false;
                },
                Instr::IsEq => {
                    let dest_reg = opcode[1] as i64;
                    let arg1_reg = opcode[2] as i64;
                    let arg2_reg = opcode[3] as i64;
                    
                    let dest_reg_const = builder.ins().iconst(types::I64, dest_reg);
                    let arg1_reg_const = builder.ins().iconst(types::I64, arg1_reg);
                    let arg2_reg_const = builder.ins().iconst(types::I64, arg2_reg);
                    
                    builder.ins().call(local_helper_is_eq, &[registers_ptr, dest_reg_const, arg1_reg_const, arg2_reg_const]);
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
                Instr::Map => {
                    let func_reg = opcode[1] as i64;
                    let list_reg = opcode[2] as i64;
                    let temp_reg = prog.read_byte().unwrap() as i64;
                    
                    let func_reg_const = builder.ins().iconst(types::I64, func_reg);
                    let list_reg_const = builder.ins().iconst(types::I64, list_reg);
                    let temp_reg_const = builder.ins().iconst(types::I64, temp_reg);
                    
                    let call_inst = builder.ins().call(local_helper_prepare_map, &[vm_ptr, prog_ptr, registers_ptr, func_reg_const, list_reg_const, temp_reg_const]);
                    let jit_code_addr = builder.inst_results(call_inst)[0];
                    
                    // Reload registers_ptr
                    let call_inst = builder.ins().call(local_helper_get_registers_ptr, &[vm_ptr]);
                    let registers_ptr_after_prep = builder.inst_results(call_inst)[0];
                    
                    let target_addr = prog.current_address() + 16;
                    let fallthrough_block = builder.create_block();
                    let call_block = builder.create_block();
                    builder.append_block_param(fallthrough_block, ptr_type);
                    builder.append_block_param(call_block, ptr_type);

                    let addr_is_zero = builder.ins().icmp_imm(IntCC::Equal, jit_code_addr, 0);

                    if let Some(&target_block) = blocks.get(&target_addr) {
                         builder.ins().brif(addr_is_zero, target_block, &[BlockArg::from(registers_ptr_after_prep)], call_block, &[BlockArg::from(registers_ptr_after_prep)]);
                    } else {
                         builder.ins().brif(addr_is_zero, fallthrough_block, &[BlockArg::from(registers_ptr_after_prep)], call_block, &[BlockArg::from(registers_ptr_after_prep)]);
                    }
                    
                    builder.switch_to_block(call_block);
                    let current_registers_ptr = builder.block_params(call_block)[0];
                    
                    // Call the JIT code
                    let mut sig_jit = self.module.make_signature();
                    sig_jit.params.push(AbiParam::new(ptr_type)); // vm
                    sig_jit.params.push(AbiParam::new(ptr_type)); // prog
                    sig_jit.params.push(AbiParam::new(ptr_type)); // registers
                    let sig_jit_ref = builder.import_signature(sig_jit);
                    
                    builder.ins().call_indirect(sig_jit_ref, jit_code_addr, &[vm_ptr, prog_ptr, current_registers_ptr]);
                    
                    // Call helper_ret
                    builder.ins().call(local_helper_ret, &[vm_ptr]);
                    
                    // Reload registers_ptr
                    let call_inst = builder.ins().call(local_helper_get_registers_ptr, &[vm_ptr]);
                    let new_registers_ptr = builder.inst_results(call_inst)[0];
                    
                    builder.ins().jump(fallthrough_block, &[BlockArg::from(new_registers_ptr)]);
                    
                    builder.switch_to_block(fallthrough_block);
                    registers_ptr = builder.block_params(fallthrough_block)[0];
                    
                    is_terminated = false;
                },
                Instr::ForEach | Instr::Filter | Instr::Fold | Instr::FilterStep => {
                    return Err(format!("Unsupported opcode in JIT: {}", instr));
                },
                Instr::Add | Instr::Sub | Instr::Mul | Instr::Div | 
                Instr::Eq | Instr::Neq | Instr::Lt | Instr::Gt | Instr::Leq | Instr::Geq => {
                    let dest_reg = opcode[1] as i64;
                    let src1_reg = opcode[2] as i64;
                    let src2_reg = opcode[3] as i64;

                    let block_int = builder.create_block();
                    let block_float_exec = builder.create_block();
                    let block_slow = builder.create_block();
                    let block_done = builder.create_block();
                    builder.append_block_param(block_done, ptr_type);
                    let block_dispatch = builder.create_block();

                    // Optimization: Peek ahead for conditional jump
                    let mut fused_jump = false;
                    let mut jump_target_block = block_done; // Default, will be overwritten
                    let mut jump_fallthrough_block = block_done; // Default
                    let mut jump_condition = JumpCondition::Jump;

                    let is_comparison = matches!(instr, Instr::Eq | Instr::Neq | Instr::Lt | Instr::Gt | Instr::Leq | Instr::Geq);
                    if is_comparison {
                        let peek_pos = prog.current_address();
                        // If the next instruction is a jump target, we cannot fuse it safely
                        // because we would skip generating the block for it.
                        if !blocks.contains_key(&peek_pos) {
                            let bytecode = prog.get_bytecode();
                            if (peek_pos as usize) + 12 <= bytecode.len() {
                                let next_op = bytecode[peek_pos as usize];
                                if next_op == Instr::Jump as u8 {
                                let next_reg = bytecode[peek_pos as usize + 1];
                                let next_cond = bytecode[peek_pos as usize + 2];
                                
                                if next_reg == dest_reg as u8 && (next_cond == JumpCondition::JumpTrue as u8 || next_cond == JumpCondition::JumpFalse as u8) {
                                    let dist_bytes = &bytecode[peek_pos as usize + 4 .. peek_pos as usize + 12];
                                    let dist = i64::from_le_bytes(dist_bytes.try_into().unwrap());
                                    
                                    let after_jump_pos = peek_pos + 12;
                                    let target_addr = (after_jump_pos as i64 + dist) as u64;
                                    
                                    if let Some(tb) = blocks.get(&target_addr) {
                                        if let Some(fb) = blocks.get(&after_jump_pos) {
                                            fused_jump = true;
                                            jump_target_block = *tb;
                                            jump_fallthrough_block = *fb;
                                            jump_condition = unsafe { std::mem::transmute(next_cond) };
                                            
                                            prog.jump(12);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    }
                    
                    let val_size = 8;
                    
                    let src1_ptr = builder.ins().iadd_imm(registers_ptr, src1_reg * val_size);
                    let src2_ptr = builder.ins().iadd_imm(registers_ptr, src2_reg * val_size);
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let val1_raw = builder.ins().load(types::I64, MemFlags::trusted(), src1_ptr, 0);
                    let val2_raw = builder.ins().load(types::I64, MemFlags::trusted(), src2_ptr, 0);

                    // Check tags (low 3 bits)
                    let tag1 = builder.ins().band_imm(val1_raw, 7);
                    let tag2 = builder.ins().band_imm(val2_raw, 7);
                    
                    // TAG_INT = 1
                    let t1_is_int = builder.ins().icmp_imm(IntCC::Equal, tag1, 1);
                    let t2_is_int = builder.ins().icmp_imm(IntCC::Equal, tag2, 1);
                    let both_int = builder.ins().band(t1_is_int, t2_is_int);
                    
                    builder.ins().brif(both_int, block_int, &[], block_slow, &[]);

                    builder.switch_to_block(block_dispatch);
                    builder.ins().jump(block_slow, &[]); // Skip dispatch for now
                    
                    // --- Integer Path ---
                    builder.switch_to_block(block_int);
                    let val1 = builder.ins().sshr_imm(val1_raw, 3);
                    let val2 = builder.ins().sshr_imm(val2_raw, 3);
                    
                    let mut comparison_result = None;

                    match instr {
                        Instr::Add => {
                            let res = builder.ins().iadd(val1, val2);
                            let res_shifted = builder.ins().ishl_imm(res, 3);
                            let res_raw = builder.ins().bor_imm(res_shifted, 1);
                            builder.ins().store(MemFlags::trusted(), res_raw, dest_ptr, 0);
                        },
                        Instr::Sub => {
                            let res = builder.ins().isub(val1, val2);
                            let res_shifted = builder.ins().ishl_imm(res, 3);
                            let res_raw = builder.ins().bor_imm(res_shifted, 1);
                            builder.ins().store(MemFlags::trusted(), res_raw, dest_ptr, 0);
                        },
                        Instr::Mul => {
                            let res = builder.ins().imul(val1, val2);
                            let res_shifted = builder.ins().ishl_imm(res, 3);
                            let res_raw = builder.ins().bor_imm(res_shifted, 1);
                            builder.ins().store(MemFlags::trusted(), res_raw, dest_ptr, 0);
                        },
                        Instr::Div => {
                            let res = builder.ins().sdiv(val1, val2);
                            let res_shifted = builder.ins().ishl_imm(res, 3);
                            let res_raw = builder.ins().bor_imm(res_shifted, 1);
                            builder.ins().store(MemFlags::trusted(), res_raw, dest_ptr, 0);
                        },
                        Instr::Eq => {
                            let res = builder.ins().icmp(IntCC::Equal, val1, val2);
                            comparison_result = Some(res);
                            let true_const = builder.ins().iconst(types::I64, 35);
                            let false_const = builder.ins().iconst(types::I64, 19);
                            let raw = builder.ins().select(res, true_const, false_const);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Neq => {
                            let res = builder.ins().icmp(IntCC::NotEqual, val1, val2);
                            comparison_result = Some(res);
                            let true_const = builder.ins().iconst(types::I64, 35);
                            let false_const = builder.ins().iconst(types::I64, 19);
                            let raw = builder.ins().select(res, true_const, false_const);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Lt => {
                            let res = builder.ins().icmp(IntCC::SignedLessThan, val1, val2);
                            comparison_result = Some(res);
                            let true_const = builder.ins().iconst(types::I64, 35);
                            let false_const = builder.ins().iconst(types::I64, 19);
                            let raw = builder.ins().select(res, true_const, false_const);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Gt => {
                            let res = builder.ins().icmp(IntCC::SignedGreaterThan, val1, val2);
                            comparison_result = Some(res);
                            let true_const = builder.ins().iconst(types::I64, 35);
                            let false_const = builder.ins().iconst(types::I64, 19);
                            let raw = builder.ins().select(res, true_const, false_const);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Leq => {
                            let res = builder.ins().icmp(IntCC::SignedLessThanOrEqual, val1, val2);
                            comparison_result = Some(res);
                            let true_const = builder.ins().iconst(types::I64, 35);
                            let false_const = builder.ins().iconst(types::I64, 19);
                            let raw = builder.ins().select(res, true_const, false_const);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Geq => {
                            let res = builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, val1, val2);
                            comparison_result = Some(res);
                            let true_const = builder.ins().iconst(types::I64, 35);
                            let false_const = builder.ins().iconst(types::I64, 19);
                            let raw = builder.ins().select(res, true_const, false_const);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        _ => {}
                    }
                    
                    if fused_jump {
                        if let Some(res) = comparison_result {
                             match jump_condition {
                                 JumpCondition::JumpTrue => builder.ins().brif(res, jump_target_block, &[BlockArg::from(registers_ptr)], jump_fallthrough_block, &[BlockArg::from(registers_ptr)]),
                                 JumpCondition::JumpFalse => builder.ins().brif(res, jump_fallthrough_block, &[BlockArg::from(registers_ptr)], jump_target_block, &[BlockArg::from(registers_ptr)]),
                                 _ => builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)])
                             };
                        } else {
                             builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)]);
                        }
                    } else {
                        builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)]);
                    }

                    // --- Float Path ---
                    builder.switch_to_block(block_float_exec);
                    
                    let val1_raw = builder.ins().load(types::I64, MemFlags::trusted(), src1_ptr, 0);
                    let val2_raw = builder.ins().load(types::I64, MemFlags::trusted(), src2_ptr, 0);
                    
                    let bits1 = builder.ins().ushr_imm(val1_raw, 32);
                    let bits2 = builder.ins().ushr_imm(val2_raw, 32);
                    
                    let trunc1 = builder.ins().ireduce(types::I32, bits1);
                    let trunc2 = builder.ins().ireduce(types::I32, bits2);
                    
                    let val1 = builder.ins().bitcast(types::F32, MemFlags::new(), trunc1);
                    let val2 = builder.ins().bitcast(types::F32, MemFlags::new(), trunc2);
                    
                    comparison_result = None;

                    match instr {
                        Instr::Add => {
                            let res = builder.ins().fadd(val1, val2);
                            let bits = builder.ins().bitcast(types::I32, MemFlags::new(), res);
                            let ext = builder.ins().uextend(types::I64, bits);
                            let shifted = builder.ins().ishl_imm(ext, 32);
                            let raw = builder.ins().bor_imm(shifted, 2);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Sub => {
                            let res = builder.ins().fsub(val1, val2);
                            let bits = builder.ins().bitcast(types::I32, MemFlags::new(), res);
                            let ext = builder.ins().uextend(types::I64, bits);
                            let shifted = builder.ins().ishl_imm(ext, 32);
                            let raw = builder.ins().bor_imm(shifted, 2);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Mul => {
                            let res = builder.ins().fmul(val1, val2);
                            let bits = builder.ins().bitcast(types::I32, MemFlags::new(), res);
                            let ext = builder.ins().uextend(types::I64, bits);
                            let shifted = builder.ins().ishl_imm(ext, 32);
                            let raw = builder.ins().bor_imm(shifted, 2);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Div => {
                            let res = builder.ins().fdiv(val1, val2);
                            let bits = builder.ins().bitcast(types::I32, MemFlags::new(), res);
                            let ext = builder.ins().uextend(types::I64, bits);
                            let shifted = builder.ins().ishl_imm(ext, 32);
                            let raw = builder.ins().bor_imm(shifted, 2);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Eq => {
                            let res = builder.ins().fcmp(FloatCC::Equal, val1, val2);
                            comparison_result = Some(res);
                            let t = builder.ins().iconst(types::I64, 35);
                            let f = builder.ins().iconst(types::I64, 19);
                            let raw = builder.ins().select(res, t, f);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Neq => {
                            let res = builder.ins().fcmp(FloatCC::NotEqual, val1, val2);
                            comparison_result = Some(res);
                            let t = builder.ins().iconst(types::I64, 35);
                            let f = builder.ins().iconst(types::I64, 19);
                            let raw = builder.ins().select(res, t, f);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Lt => {
                            let res = builder.ins().fcmp(FloatCC::LessThan, val1, val2);
                            comparison_result = Some(res);
                            let t = builder.ins().iconst(types::I64, 35);
                            let f = builder.ins().iconst(types::I64, 19);
                            let raw = builder.ins().select(res, t, f);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Gt => {
                            let res = builder.ins().fcmp(FloatCC::GreaterThan, val1, val2);
                            comparison_result = Some(res);
                            let t = builder.ins().iconst(types::I64, 35);
                            let f = builder.ins().iconst(types::I64, 19);
                            let raw = builder.ins().select(res, t, f);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Leq => {
                            let res = builder.ins().fcmp(FloatCC::LessThanOrEqual, val1, val2);
                            comparison_result = Some(res);
                            let t = builder.ins().iconst(types::I64, 35);
                            let f = builder.ins().iconst(types::I64, 19);
                            let raw = builder.ins().select(res, t, f);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        Instr::Geq => {
                            let res = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, val1, val2);
                            comparison_result = Some(res);
                            let t = builder.ins().iconst(types::I64, 35);
                            let f = builder.ins().iconst(types::I64, 19);
                            let raw = builder.ins().select(res, t, f);
                            builder.ins().store(MemFlags::trusted(), raw, dest_ptr, 0);
                        },
                        _ => {}
                    }
                    
                    if fused_jump {
                        if let Some(res) = comparison_result {
                             match jump_condition {
                                 JumpCondition::JumpTrue => builder.ins().brif(res, jump_target_block, &[BlockArg::from(registers_ptr)], jump_fallthrough_block, &[BlockArg::from(registers_ptr)]),
                                 JumpCondition::JumpFalse => builder.ins().brif(res, jump_fallthrough_block, &[BlockArg::from(registers_ptr)], jump_target_block, &[BlockArg::from(registers_ptr)]),
                                 _ => builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)])
                             };
                        } else {
                             builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)]);
                        }
                    } else {
                        builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)]);
                    }

                    // --- Slow Path ---
                    builder.switch_to_block(block_slow);
                    let op_val = u32::from_le_bytes(opcode);
                    let op_const = builder.ins().iconst(types::I32, op_val as i64);
                    builder.ins().call(local_helper_op, &[vm_ptr, prog_ptr, registers_ptr, op_const]);
                    
                    if fused_jump {
                         let val = builder.ins().load(types::I64, MemFlags::trusted(), dest_ptr, 0);
                         let is_false = builder.ins().icmp_imm(IntCC::Equal, val, 19);
                         
                         match jump_condition {
                             JumpCondition::JumpTrue => {
                                 builder.ins().brif(is_false, jump_fallthrough_block, &[BlockArg::from(registers_ptr)], jump_target_block, &[BlockArg::from(registers_ptr)]);
                             },
                             JumpCondition::JumpFalse => {
                                 builder.ins().brif(is_false, jump_target_block, &[BlockArg::from(registers_ptr)], jump_fallthrough_block, &[BlockArg::from(registers_ptr)]);
                             },
                             _ => {
                                 builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)]);
                             }
                         }
                    } else {
                        builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)]);
                    }
                    
                    builder.switch_to_block(block_done);
                    registers_ptr = builder.block_params(block_done)[0];
                },
                Instr::Not => {
                    let dest_reg = opcode[1] as i64;
                    let src_reg = opcode[2] as i64;
                    
                    let block_done = builder.create_block();
                    builder.append_block_param(block_done, ptr_type);

                    // Optimization: Peek ahead for conditional jump
                    let mut fused_jump = false;
                    let mut jump_target_block = block_done;
                    let mut jump_fallthrough_block = block_done;
                    let mut jump_condition = JumpCondition::Jump;

                    let peek_pos = prog.current_address();
                    if !blocks.contains_key(&peek_pos) {
                        let bytecode = prog.get_bytecode();
                        if (peek_pos as usize) + 12 <= bytecode.len() {
                            let next_op = bytecode[peek_pos as usize];
                            if next_op == Instr::Jump as u8 {
                                let next_reg = bytecode[peek_pos as usize + 1];
                                let next_cond = bytecode[peek_pos as usize + 2];
                                
                                if next_reg == dest_reg as u8 && (next_cond == JumpCondition::JumpTrue as u8 || next_cond == JumpCondition::JumpFalse as u8) {
                                    let dist_bytes = &bytecode[peek_pos as usize + 4 .. peek_pos as usize + 12];
                                    let dist = i64::from_le_bytes(dist_bytes.try_into().unwrap());
                                    
                                    let after_jump_pos = peek_pos + 12;
                                    let target_addr = (after_jump_pos as i64 + dist) as u64;
                                    
                                    if let Some(tb) = blocks.get(&target_addr) {
                                        if let Some(fb) = blocks.get(&after_jump_pos) {
                                            fused_jump = true;
                                            jump_target_block = *tb;
                                            jump_fallthrough_block = *fb;
                                            jump_condition = unsafe { std::mem::transmute(next_cond) };
                                            
                                            prog.jump(12);
                                        }
                                    }
                                }
                            }
                        }
                    }

                    let val_size = 8;
                    
                    let src_ptr = builder.ins().iadd_imm(registers_ptr, src_reg * val_size);
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let val = builder.ins().load(types::I64, MemFlags::trusted(), src_ptr, 0);
                    
                    // IMM_FALSE = 19
                    let is_false = builder.ins().icmp_imm(IntCC::Equal, val, 19);
                    
                    let t = builder.ins().iconst(types::I64, 35);
                    let f = builder.ins().iconst(types::I64, 19);
                    let res = builder.ins().select(is_false, t, f);
                    
                    builder.ins().store(MemFlags::trusted(), res, dest_ptr, 0);
                    
                    if fused_jump {
                        // is_false is true if val was false.
                        // So res is true.
                        // If JumpTrue, we jump if res is true (i.e. is_false is true).
                        match jump_condition {
                             JumpCondition::JumpTrue => {
                                 builder.ins().brif(is_false, jump_target_block, &[BlockArg::from(registers_ptr)], jump_fallthrough_block, &[BlockArg::from(registers_ptr)]);
                             },
                             JumpCondition::JumpFalse => {
                                 builder.ins().brif(is_false, jump_fallthrough_block, &[BlockArg::from(registers_ptr)], jump_target_block, &[BlockArg::from(registers_ptr)]);
                             },
                             _ => {
                                 builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)]);
                             }
                         }
                    } else {
                        builder.ins().jump(block_done, &[BlockArg::from(registers_ptr)]);
                    }
                    
                    builder.switch_to_block(block_done);
                    registers_ptr = builder.block_params(block_done)[0];
                    
                    is_terminated = false;
                },
                Instr::CopyReg => {
                    let dest_reg = opcode[1] as i64;
                    let src_reg = opcode[2] as i64;
                    let val_size = 8;
                    
                    let src_ptr = builder.ins().iadd_imm(registers_ptr, src_reg * val_size);
                    let dest_ptr = builder.ins().iadd_imm(registers_ptr, dest_reg * val_size);
                    
                    let val = builder.ins().load(types::I64, MemFlags::trusted(), src_ptr, 0);
                    builder.ins().store(MemFlags::trusted(), val, dest_ptr, 0);
                    
                    is_terminated = false;
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
                        Instr::LoadString | Instr::LoadSymbol => { prog.read_string(); },
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
