use std::sync::{Arc, Mutex, atomic::{AtomicBool, Ordering}};
use std::thread;
use std::time::Duration;
use std::collections::HashMap;
use std::ffi::c_void;
use iced_x86::{Decoder, DecoderOptions, Formatter, NasmFormatter, Instruction};

const CONTEXT_CONTROL: u32 = 0x100001;

extern "system" {
    fn SuspendThread(hThread: *mut c_void) -> u32;
    fn ResumeThread(hThread: *mut c_void) -> u32;
    fn GetThreadContext(hThread: *mut c_void, lpContext: *mut c_void) -> i32;
    fn GetCurrentThread() -> *mut c_void;
    fn DuplicateHandle(
        hSourceProcessHandle: *mut c_void,
        hSourceHandle: *mut c_void,
        hTargetProcessHandle: *mut c_void,
        lpTargetHandle: *mut *mut c_void,
        dwDesiredAccess: u32,
        bInheritHandle: i32,
        dwOptions: u32,
    ) -> i32;
    fn GetCurrentProcess() -> *mut c_void;
    fn CloseHandle(hObject: *mut c_void) -> i32;
}

pub struct Profiler {
    running: Arc<AtomicBool>,
    handle: Option<thread::JoinHandle<HashMap<usize, usize>>>,
    function_map: Arc<Mutex<Vec<(usize, usize, String)>>>,
}

impl Profiler {
    pub fn new(function_map: Arc<Mutex<Vec<(usize, usize, String)>>>) -> Self {
        let running = Arc::new(AtomicBool::new(true));
        let running_clone = running.clone();
        
        // Get handle to current thread (main thread)
        let main_thread_handle = unsafe {
            let current_process = GetCurrentProcess();
            let current_thread = GetCurrentThread();
            let mut real_handle: *mut c_void = std::ptr::null_mut();
            let res = DuplicateHandle(
                current_process,
                current_thread,
                current_process,
                &mut real_handle,
                0,
                0,
                2 // DUPLICATE_SAME_ACCESS
            );
            if res == 0 {
                panic!("Failed to duplicate thread handle");
            }
            real_handle
        };

        // Send handle to thread (pointer is Send)
        let handle_wrapper = main_thread_handle as usize;

        let handle = thread::spawn(move || {
            let thread_handle = handle_wrapper as *mut c_void;
            let mut samples: HashMap<usize, usize> = HashMap::new();
            
            // Allocate aligned buffer for CONTEXT
            #[repr(align(16))]
            struct ContextBuffer([u8; 2048]);
            let mut ctx_buffer = ContextBuffer([0; 2048]);
            
            while running_clone.load(Ordering::Relaxed) {
                thread::sleep(Duration::from_millis(1));
                
                unsafe {
                    if SuspendThread(thread_handle) != u32::MAX {
                        // Set ContextFlags to CONTEXT_CONTROL to get Rip
                        // ContextFlags is at offset 0x30 (48)
                        *(ctx_buffer.0.as_mut_ptr().add(48) as *mut u32) = CONTEXT_CONTROL;
                        
                        if GetThreadContext(thread_handle, ctx_buffer.0.as_mut_ptr() as *mut c_void) != 0 {
                            // Rip is at offset 0xF8 (248)
                            let rip = *(ctx_buffer.0.as_ptr().add(248) as *const u64);
                            *samples.entry(rip as usize).or_insert(0) += 1;
                        }
                        
                        ResumeThread(thread_handle);
                    }
                }
            }
            
            unsafe { CloseHandle(thread_handle); }
            samples
        });

        Profiler {
            running,
            handle: Some(handle),
            function_map,
        }
    }

    pub fn stop(&mut self) {
        self.running.store(false, Ordering::Relaxed);
        if let Some(handle) = self.handle.take() {
            let samples = handle.join().unwrap();
            self.print_report(samples);
        }
    }

    fn print_report(&self, samples: HashMap<usize, usize>) {
        let total_samples: usize = samples.values().sum();
        println!("\n--- Profiler Results ---");
        println!("Total samples: {}", total_samples);

        let map = self.function_map.lock().unwrap();
        
        // Aggregate by function
        let mut func_samples: HashMap<String, usize> = HashMap::new();
        let mut unknown_samples = 0;

        for (&ip, &count) in &samples {
            let mut found = false;
            for (start, end, name) in map.iter() {
                if ip >= *start && ip < *end {
                    *func_samples.entry(name.clone()).or_insert(0) += count;
                    found = true;
                    break;
                }
            }
            if !found {
                unknown_samples += count;
            }
        }

        let mut sorted_funcs: Vec<_> = func_samples.into_iter().collect();
        sorted_funcs.sort_by(|a, b| b.1.cmp(&a.1));
        
        for (name, count) in sorted_funcs {
            let percent = (count as f64 / total_samples as f64) * 100.0;
            println!("{}: {} ({:.2}%)", name, count, percent);
        }
        println!("unknown: {} ({:.2}%)", unknown_samples, (unknown_samples as f64 / total_samples as f64) * 100.0);

        println!("\n--- Hot Code Disassembly ---");
        
        // Disassemble functions that have samples
        for (start, end, name) in map.iter() {
            // Check if this function has any samples
            let func_total: usize = samples.iter()
                .filter(|(&ip, _)| ip >= *start && ip < *end)
                .map(|(_, &c)| c)
                .sum();
            
            if func_total > 0 {
                println!("\nFunction: {} (Total samples: {})", name, func_total);
                
                let code_slice = unsafe {
                    std::slice::from_raw_parts(*start as *const u8, end - start)
                };

                let mut decoder = Decoder::with_ip(64, code_slice, *start as u64, DecoderOptions::NONE);
                let mut formatter = NasmFormatter::new();
                formatter.options_mut().set_digit_separator("");
                formatter.options_mut().set_first_operand_char_index(10);
                
                let mut instruction = Instruction::default();
                let mut output = String::new();

                while decoder.can_decode() {
                    decoder.decode_out(&mut instruction);
                    output.clear();
                    formatter.format(&instruction, &mut output);

                    let ip = instruction.ip() as usize;
                    let len = instruction.len();
                    
                    // Count samples in this instruction range
                    let mut inst_samples = 0;
                    for offset in 0..len {
                        if let Some(c) = samples.get(&(ip + offset)) {
                            inst_samples += c;
                        }
                    }

                    if inst_samples > 0 {
                        let percent = (inst_samples as f64 / total_samples as f64) * 100.0;
                        println!("  {:016X} {}  <-- {} samples ({:.1}%)", ip, output, inst_samples, percent);
                    } else {
                        println!("  {:016X} {}", ip, output);
                    }
                }
            }
        }
    }
}
