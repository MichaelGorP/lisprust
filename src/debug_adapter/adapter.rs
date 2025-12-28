use std::collections::HashMap;
use std::io::{self, BufRead, Write, Read};
use std::sync::mpsc::{self, Receiver, Sender};
use std::thread;
use std::fs;

use serde::Deserialize;
use serde_json::{json, from_value};

use crate::vm::vm::{Vm, Debugger};
use crate::vm::vp::{VirtualProgram, Value};
use crate::vm::compiler::Compiler;
use crate::parser::Parser;
use crate::lexer;
use crate::vm::math_functions;
use crate::vm::list_functions;

use super::protocol::*;

pub struct DebugAdapter {
    sender: Sender<AdapterMessage>, // Channel to self (for stdin thread)
    receiver: Receiver<AdapterMessage>,
    seq: i64,
    
    // VM Communication
    vm_tx: Option<Sender<VmCommand>>,
    
    // State
    breakpoints: HashMap<String, Vec<i64>>,
    source_lines: Vec<usize>, // Cache of line offsets for the loaded program
    program_path: Option<String>,
}

enum AdapterMessage {
    Protocol(ProtocolMessage),
    Vm(VmEvent),
}

enum VmCommand {
    Continue,
    StepIn,
    StepOver,
    StepOut,
    Pause,
    SetBreakpoints(HashMap<String, Vec<i64>>),
    GetStackTrace(Sender<Vec<StackFrame>>),
    GetScopes(i64, Sender<Vec<Scope>>),
    GetVariables(i64, Sender<Vec<Variable>>),
}

enum VmEvent {
    Stopped(String), // reason
    Terminated,
    Output(String),
}

impl DebugAdapter {
    pub fn new() -> Self {
        let (tx, rx) = mpsc::channel();
        
        // Spawn stdin reader thread
        let tx_clone = tx.clone();
        thread::spawn(move || {
            let stdin = io::stdin();
            let mut handle = stdin.lock();
            loop {
                let mut content_length = 0;
                let mut line = String::new();
                
                // Read headers
                loop {
                    line.clear();
                    if handle.read_line(&mut line).unwrap() == 0 {
                        return; // EOF
                    }
                    let line = line.trim();
                    if line.is_empty() {
                        break; // End of headers
                    }
                    if line.starts_with("Content-Length: ") {
                        if let Ok(len) = line["Content-Length: ".len()..].parse::<usize>() {
                            content_length = len;
                        }
                    }
                }
                
                if content_length > 0 {
                    let mut buffer = vec![0u8; content_length];
                    if handle.read_exact(&mut buffer).is_ok() {
                        if let Ok(msg) = serde_json::from_slice::<ProtocolMessage>(&buffer) {
                            tx_clone.send(AdapterMessage::Protocol(msg)).unwrap();
                        }
                    }
                }
            }
        });

        DebugAdapter {
            sender: tx,
            receiver: rx,
            seq: 1,
            vm_tx: None,
            breakpoints: HashMap::new(),
            source_lines: Vec::new(),
            program_path: None,
        }
    }

    pub fn run(&mut self) {
        loop {
            if let Ok(msg) = self.receiver.recv() {
                match msg {
                    AdapterMessage::Protocol(p_msg) => {
                        match p_msg {
                            ProtocolMessage::Request(req) => self.handle_request(req),
                            _ => {}
                        }
                    },
                    AdapterMessage::Vm(v_msg) => {
                        match v_msg {
                            VmEvent::Stopped(reason) => {
                                self.send_event("stopped".to_string(), Some(json!({
                                    "reason": reason,
                                    "threadId": 1,
                                    "allThreadsStopped": true
                                })));
                            },
                            VmEvent::Terminated => {
                                self.send_event("terminated".to_string(), None);
                                self.send_event("exited".to_string(), Some(json!({"exitCode": 0})));
                                std::process::exit(0);
                            },
                            VmEvent::Output(text) => {
                                self.send_event("output".to_string(), Some(json!({
                                    "category": "stdout",
                                    "output": text
                                })));
                            }
                        }
                    }
                }
            }
        }
    }

    fn send_response(&mut self, req: &Request, success: bool, message: Option<String>, body: Option<serde_json::Value>) {
        let resp = Response {
            seq: self.seq,
            request_seq: req.seq,
            success,
            command: req.command.clone(),
            message,
            body,
        };
        self.seq += 1;
        self.send_message(ProtocolMessage::Response(resp));
    }

    fn send_event(&mut self, event: String, body: Option<serde_json::Value>) {
        let evt = Event {
            seq: self.seq,
            event,
            body,
        };
        self.seq += 1;
        self.send_message(ProtocolMessage::Event(evt));
    }

    fn send_message(&self, msg: ProtocolMessage) {
        let json = serde_json::to_string(&msg).unwrap();
        let mut stdout = io::stdout();
        write!(stdout, "Content-Length: {}\r\n\r\n{}", json.len(), json).unwrap();
        stdout.flush().unwrap();
    }

    fn handle_request(&mut self, req: Request) {
        match req.command.as_str() {
            "initialize" => {
                self.send_response(&req, true, None, Some(json!({
                    "supportsConfigurationDoneRequest": true,
                    "supportsFunctionBreakpoints": false,
                    "supportsConditionalBreakpoints": false,
                    "supportsHitConditionBreakpoints": false,
                    "supportsEvaluateForHovers": false,
                    "exceptionBreakpointFilters": [],
                    "supportsStepBack": false,
                    "supportsSetVariable": false,
                    "supportsRestartFrame": false,
                    "supportsGotoTargetsRequest": false,
                    "supportsStepInTargetsRequest": false,
                    "supportsCompletionsRequest": false,
                    "supportsModulesRequest": false,
                    "additionalModuleColumns": [],
                    "supportedChecksumAlgorithms": [],
                    "supportsRestartRequest": false,
                    "supportsExceptionOptions": false,
                    "supportsValueFormattingOptions": false,
                    "supportsExceptionInfoRequest": false,
                    "supportTerminateDebuggee": true,
                    "supportsDelayedStackTraceLoading": false,
                    "supportsLoadedSourcesRequest": false,
                    "supportsLogPoints": false,
                    "supportsTerminateThreadsRequest": false,
                    "supportsSetExpression": false,
                    "supportsTerminateRequest": false,
                    "supportsDataBreakpoints": false,
                    "supportsReadMemoryRequest": false,
                    "supportsDisassembleRequest": false,
                    "supportsCancelRequest": false,
                    "supportsBreakpointLocationsRequest": false,
                    "supportsClipboardContext": false,
                    "supportsSteppingGranularity": false,
                    "supportsInstructionBreakpoints": false,
                    "supportsExceptionFilterOptions": false,
                    "supportsSingleThreadExecutionRequests": false
                })));
                self.send_event("initialized".to_string(), None);
            },
            "launch" => {
                if let Some(args) = req.arguments.as_ref() {
                    if let Ok(launch_args) = from_value::<LaunchRequestArguments>(args.clone()) {
                        self.program_path = Some(launch_args.program.clone());
                        // Load program
                        let code = match fs::read_to_string(&launch_args.program) {
                            Ok(c) => c,
                            Err(e) => {
                                self.send_response(&req, false, Some(e.to_string()), None);
                                return;
                            }
                        };

                        // Calculate line offsets
                        self.source_lines.clear();
                        self.source_lines.push(0);
                        for (i, b) in code.bytes().enumerate() {
                            if b == b'\n' {
                                self.source_lines.push(i + 1);
                            }
                        }

                        let tokens = match lexer::tokenize(&code) {
                            Ok(t) => t,
                            Err(e) => {
                                self.send_response(&req, false, Some(format!("{:?}", e)), None);
                                return;
                            }
                        };
                        
                        let parser = Parser::new();
                        let (expr, map, _) = match parser.parse(&tokens) {
                            Ok(res) => res,
                            Err(e) => {
                                self.send_response(&req, false, Some(e.to_string()), None);
                                return;
                            }
                        };
                        
                        let mut compiler = Compiler::new(false);
                        math_functions::register_functions(&mut compiler);
                        list_functions::register_functions(&mut compiler);
                        
                        let mut prog = match compiler.compile(&expr, &map) {
                            Ok(p) => p,
                            Err(e) => {
                                self.send_response(&req, false, Some(e.to_string()), None);
                                return;
                            }
                        };

                        // Start VM thread
                        let (vm_tx, vm_rx) = mpsc::channel();
                        self.vm_tx = Some(vm_tx);
                        
                        let adapter_tx = self.sender.clone();
                        let breakpoints = self.breakpoints.clone();
                        let source_lines = self.source_lines.clone();
                        let stop_on_entry = launch_args.stop_on_entry;
                        let program_path = launch_args.program.clone();
                        
                        thread::spawn(move || {
                            let mut vm = Vm::new();
                            let mut debugger = VmDebugger {
                                cmd_rx: vm_rx,
                                adapter_tx,
                                breakpoints,
                                source_lines,
                                paused: stop_on_entry,
                                step_mode: StepMode::None,
                                program_path,
                                step_start_line: 0,
                                step_start_col: 0,
                                step_start_depth: 0,
                            };
                            
                            if stop_on_entry {
                                debugger.adapter_tx.send(AdapterMessage::Vm(VmEvent::Stopped("entry".to_string()))).unwrap();
                                debugger.wait_for_command(&vm, &prog);
                            }
                            
                            vm.run_debug(&mut prog, Some(&mut debugger));
                            debugger.adapter_tx.send(AdapterMessage::Vm(VmEvent::Terminated)).unwrap();
                        });
                        
                        self.send_response(&req, true, None, None);
                        self.send_event("process".to_string(), Some(json!({"name": launch_args.program})));
                        return;
                    }
                }
                self.send_response(&req, false, Some("Invalid arguments".to_string()), None);
            },
            "setBreakpoints" => {
                if let Some(args) = req.arguments.as_ref() {
                    #[derive(Deserialize)]
                    struct SetBreakpointsArgs {
                        source: Source,
                        breakpoints: Option<Vec<SourceBreakpoint>>,
                    }
                    #[derive(Deserialize)]
                    struct Source {
                        path: Option<String>,
                    }
                    #[derive(Deserialize)]
                    struct SourceBreakpoint {
                        line: i64,
                    }

                    if let Ok(sb_args) = from_value::<SetBreakpointsArgs>(args.clone()) {
                        if let Some(path) = sb_args.source.path {
                            // Normalize path if possible, or just use as is.
                            // VS Code usually sends absolute paths.
                            let lines: Vec<i64> = sb_args.breakpoints
                                .unwrap_or_default()
                                .iter()
                                .map(|b| b.line)
                                .collect();
                            
                            self.breakpoints.insert(path.clone(), lines.clone());
                            
                            if let Some(tx) = &self.vm_tx {
                                tx.send(VmCommand::SetBreakpoints(self.breakpoints.clone())).unwrap();
                            }

                            let breakpoints_resp: Vec<_> = lines.iter().map(|l| json!({
                                "verified": true,
                                "line": l
                            })).collect();

                            self.send_response(&req, true, None, Some(json!({
                                "breakpoints": breakpoints_resp
                            })));
                            return;
                        }
                    }
                }
                self.send_response(&req, false, Some("Invalid arguments".to_string()), None);
            },
            "configurationDone" => {
                self.send_response(&req, true, None, None);
            },
            "threads" => {
                self.send_response(&req, true, None, Some(json!({
                    "threads": [
                        { "id": 1, "name": "main" }
                    ]
                })));
            },
            "stackTrace" => {
                if let Some(tx) = &self.vm_tx {
                    let (resp_tx, resp_rx) = mpsc::channel();
                    tx.send(VmCommand::GetStackTrace(resp_tx)).unwrap();
                    if let Ok(frames) = resp_rx.recv() {
                        self.send_response(&req, true, None, Some(json!({
                            "stackFrames": frames,
                            "totalFrames": frames.len()
                        })));
                        return;
                    }
                }
                self.send_response(&req, false, Some("Failed to get stack trace".to_string()), None);
            },
            "scopes" => {
                if let Some(args) = req.arguments.as_ref() {
                    #[derive(Deserialize)]
                    struct ScopesArgs {
                        #[serde(rename = "frameId")]
                        frame_id: i64,
                    }
                    if let Ok(s_args) = from_value::<ScopesArgs>(args.clone()) {
                        if let Some(tx) = &self.vm_tx {
                            let (resp_tx, resp_rx) = mpsc::channel();
                            tx.send(VmCommand::GetScopes(s_args.frame_id, resp_tx)).unwrap();
                            if let Ok(scopes) = resp_rx.recv() {
                                self.send_response(&req, true, None, Some(json!({
                                    "scopes": scopes
                                })));
                                return;
                            }
                        }
                    }
                }
                self.send_response(&req, false, Some("Failed to get scopes".to_string()), None);
            },
            "variables" => {
                if let Some(args) = req.arguments.as_ref() {
                    #[derive(Deserialize)]
                    struct VariablesArgs {
                        #[serde(rename = "variablesReference")]
                        variables_reference: i64,
                    }
                    if let Ok(v_args) = from_value::<VariablesArgs>(args.clone()) {
                        if let Some(tx) = &self.vm_tx {
                            let (resp_tx, resp_rx) = mpsc::channel();
                            tx.send(VmCommand::GetVariables(v_args.variables_reference, resp_tx)).unwrap();
                            if let Ok(vars) = resp_rx.recv() {
                                self.send_response(&req, true, None, Some(json!({
                                    "variables": vars
                                })));
                                return;
                            }
                        }
                    }
                }
                self.send_response(&req, false, Some("Failed to get variables".to_string()), None);
            },
            "continue" => {
                if let Some(tx) = &self.vm_tx {
                    tx.send(VmCommand::Continue).unwrap();
                }
                self.send_response(&req, true, None, Some(json!({
                    "allThreadsContinued": true
                })));
            },
            "next" => {
                if let Some(tx) = &self.vm_tx {
                    tx.send(VmCommand::StepOver).unwrap();
                }
                self.send_response(&req, true, None, None);
            },
            "stepIn" => {
                if let Some(tx) = &self.vm_tx {
                    tx.send(VmCommand::StepIn).unwrap();
                }
                self.send_response(&req, true, None, None);
            },
            "stepOut" => {
                if let Some(tx) = &self.vm_tx {
                    tx.send(VmCommand::StepOut).unwrap();
                }
                self.send_response(&req, true, None, None);
            },
            "pause" => {
                if let Some(tx) = &self.vm_tx {
                    tx.send(VmCommand::Pause).unwrap();
                }
                self.send_response(&req, true, None, None);
            },
            "disconnect" => {
                 self.send_response(&req, true, None, None);
                 std::process::exit(0);
            },
            _ => {
                self.send_response(&req, true, None, None);
            }
        }
    }
}

#[derive(PartialEq, Clone, Copy)]
enum StepMode {
    None,
    StepIn,
    StepOver,
    StepOut,
}

struct VmDebugger {
    cmd_rx: Receiver<VmCommand>,
    adapter_tx: Sender<AdapterMessage>,
    breakpoints: HashMap<String, Vec<i64>>,
    source_lines: Vec<usize>,
    paused: bool,
    step_mode: StepMode,
    program_path: String,
    step_start_line: i64,
    step_start_col: i64,
    step_start_depth: usize,
}

impl VmDebugger {
    fn wait_for_command(&mut self, vm: &Vm, prog: &VirtualProgram) {
        loop {
            if let Ok(cmd) = self.cmd_rx.recv() {
                if self.handle_command(cmd, vm, prog) {
                    break;
                }
            }
        }
    }

    // Returns true if execution should resume
    fn handle_command(&mut self, cmd: VmCommand, vm: &Vm, prog: &VirtualProgram) -> bool {
        match cmd {
            VmCommand::Continue => {
                self.paused = false;
                self.step_mode = StepMode::None;
                true
            },
            VmCommand::StepIn => {
                self.paused = false;
                self.step_mode = StepMode::StepIn;
                let (line, col, _, _) = self.get_location_from_addr(prog.current_address() as usize, prog);
                self.step_start_line = line;
                self.step_start_col = col;
                self.step_start_depth = vm.call_stack().len();
                true
            },
            VmCommand::StepOver => {
                self.paused = false;
                self.step_mode = StepMode::StepOver;
                let (line, col, _, _) = self.get_location_from_addr(prog.current_address() as usize, prog);
                self.step_start_line = line;
                self.step_start_col = col;
                self.step_start_depth = vm.call_stack().len();
                true
            },
            VmCommand::StepOut => {
                self.paused = false;
                self.step_mode = StepMode::StepOut;
                let (line, col, _, _) = self.get_location_from_addr(prog.current_address() as usize, prog);
                self.step_start_line = line;
                self.step_start_col = col;
                self.step_start_depth = vm.call_stack().len();
                true
            },
            VmCommand::Pause => {
                self.paused = true;
                false
            },
            VmCommand::SetBreakpoints(bp) => {
                self.breakpoints = bp;
                false
            },
            VmCommand::GetStackTrace(tx) => {
                let frames = self.create_stack_trace(vm, prog);
                tx.send(frames).unwrap();
                false
            },
            VmCommand::GetScopes(frame_id, tx) => {
                let scopes = self.create_scopes(frame_id, vm);
                tx.send(scopes).unwrap();
                false
            },
            VmCommand::GetVariables(var_ref, tx) => {
                let vars = self.create_variables(var_ref, vm, prog);
                tx.send(vars).unwrap();
                false
            }
        }
    }
    
    fn get_line_col(&self, offset: usize) -> (i64, i64) {
        for (i, &line_start) in self.source_lines.iter().enumerate() {
            if line_start > offset {
                let line_idx = i - 1;
                let line_start_offset = self.source_lines[line_idx];
                let col = offset - line_start_offset + 1;
                return ((line_idx + 1) as i64, col as i64);
            }
        }
        if let Some(&last_start) = self.source_lines.last() {
             let col = offset - last_start + 1;
             return (self.source_lines.len() as i64, col as i64);
        }
        (0, 0)
    }

    fn get_location_from_addr(&self, addr: usize, prog: &VirtualProgram) -> (i64, i64, Option<i64>, Option<i64>) {
        let mut best_span = None;
        // Source map is sorted by address. We want the last entry where map_addr <= addr.
        for (map_addr, span) in prog.source_map.iter().rev() {
            if *map_addr <= addr {
                best_span = Some(span.clone());
                break;
            }
        }
        
        if let Some(span) = best_span {
            let (line, col) = self.get_line_col(span.start);
            let (end_line, end_col) = self.get_line_col(span.end);
            return (line, col, Some(end_line), Some(end_col));
        }
        (0, 0, None, None)
    }

    fn create_stack_trace(&self, vm: &Vm, prog: &VirtualProgram) -> Vec<StackFrame> {
        let mut frames = Vec::new();
        
        // Current frame
        let (line, col, end_line, end_col) = self.get_location_from_addr(prog.current_address() as usize, prog);
        frames.push(StackFrame {
            id: 0,
            name: "current".to_string(),
            source: Some(Source {
                name: Some("main.lisp".to_string()),
                path: Some(self.program_path.clone()),
            }),
            line,
            column: col,
            end_line,
            end_column: end_col,
        });

        // Call stack
        // Note: Vm call_stack stores return addresses.
        // We need to iterate backwards?
        // Vm call_stack is a Vec.
        for (i, call) in vm.call_stack().iter().rev().enumerate() {
             let (line, col, end_line, end_col) = self.get_location_from_addr(call.return_addr as usize, prog);
             frames.push(StackFrame {
                id: (i + 1) as i64,
                name: format!("frame {}", i + 1),
                source: Some(Source {
                    name: Some("main.lisp".to_string()),
                    path: Some(self.program_path.clone()),
                }),
                line,
                column: col,
                end_line,
                end_column: end_col,
            });
        }
        
        frames
    }

    fn create_scopes(&self, frame_id: i64, _vm: &Vm) -> Vec<Scope> {
        vec![
            Scope {
                name: "Locals".to_string(),
                variables_reference: frame_id + 1, // Map frame_id 0 -> var_ref 1, etc.
                expensive: false,
            }
        ]
    }

    fn create_variables(&self, var_ref: i64, vm: &Vm, prog: &VirtualProgram) -> Vec<Variable> {
        let frame_index = (var_ref - 1) as usize;
        let (window_start, pc) = if frame_index == 0 {
            (vm.window_start, prog.current_address() as usize)
        } else {
            // frame_index 1 is the top of call_stack (most recent caller)
            // call_stack is pushed to. So last element is most recent caller.
            // frame_index 1 -> call_states[len - 1]
            let len = vm.call_stack().len();
            if frame_index > len {
                return vec![];
            }
            let state = &vm.call_stack()[len - frame_index];
            (state.window_start, state.return_addr as usize)
        };

        // Find closest header
        let mut best_header = 0;
        for header_addr in prog.debug_symbols.keys() {
            if *header_addr < pc && *header_addr >= best_header {
                best_header = *header_addr;
            }
        }
        let symbols = prog.debug_symbols.get(&best_header);

        let mut vars = Vec::new();
        // We don't know exactly how many registers are used, but let's show the first 32 
        // or until we hit a large sequence of Empty?
        // Or just show non-empty ones in the first 64?
        for i in 0..64 {
            let reg_idx = window_start + i;
            if reg_idx >= vm.registers().len() {
                break;
            }
            let val = &vm.registers()[reg_idx];
            if let Value::Empty = val {
                continue;
            }
            
            let name = if let Some(syms) = symbols {
                syms.get(&(i as u8)).cloned().unwrap_or(format!("r{}", i))
            } else {
                format!("r{}", i)
            };

            vars.push(Variable {
                name,
                value: format!("{:?}", val),
                type_: Some("Value".to_string()),
                variables_reference: 0,
            });
        }
        vars
    }
}

impl Debugger for VmDebugger {
    fn on_step(&mut self, vm: &Vm, prog: &VirtualProgram) {
        // Check for incoming commands (non-blocking)
        while let Ok(cmd) = self.cmd_rx.try_recv() {
             if !self.handle_command(cmd, vm, prog) {
                 // If command implies pause or just data retrieval, we might need to pause or continue loop
                 // handle_command returns false if we shouldn't resume execution immediately
                 // But if we are already running, we should probably continue unless it was Pause
             }
        }

        if self.paused {
            self.adapter_tx.send(AdapterMessage::Vm(VmEvent::Stopped("pause".to_string()))).unwrap();
            self.wait_for_command(vm, prog);
            return;
        }

        let (current_line, current_col, _, _) = self.get_location_from_addr(prog.current_address() as usize, prog);

        // Check breakpoints
        // We check if the current line is in the breakpoints list for the current file.
        // Note: VS Code sends paths with different casing on Windows sometimes.
        // A robust implementation would normalize paths.
        // For now, we try exact match, and maybe case-insensitive match if that fails.
        
        let mut hit = false;
        if let Some(lines) = self.breakpoints.get(&self.program_path) {
            if lines.contains(&current_line) {
                hit = true;
            }
        } else {
             // Try case-insensitive search for Windows
             for (path, lines) in &self.breakpoints {
                 if path.eq_ignore_ascii_case(&self.program_path) {
                     if lines.contains(&current_line) {
                         hit = true;
                         break;
                     }
                 }
             }
        }

        if hit {
            // Simple debounce: don't stop if we just stopped here?
            // No, we should stop. But we need to make sure we don't get stuck.
            // The user will resume.
            self.paused = true;
            self.adapter_tx.send(AdapterMessage::Vm(VmEvent::Stopped("breakpoint".to_string()))).unwrap();
            self.wait_for_command(vm, prog);
            return;
        }

        // Step logic
        let current_depth = vm.call_stack().len();
        match self.step_mode {
            StepMode::StepIn => {
                // Stop if we entered a new frame, or returned, or changed line/col in same frame
                if current_depth != self.step_start_depth || current_line != self.step_start_line || current_col != self.step_start_col {
                    self.paused = true;
                    self.adapter_tx.send(AdapterMessage::Vm(VmEvent::Stopped("step".to_string()))).unwrap();
                    self.wait_for_command(vm, prog);
                }
            },
            StepMode::StepOver => {
                // Stop if we returned (depth < start), or same depth and changed line/col.
                // If depth > start, we are inside a call, so don't stop.
                if current_depth < self.step_start_depth {
                     self.paused = true;
                     self.adapter_tx.send(AdapterMessage::Vm(VmEvent::Stopped("step".to_string()))).unwrap();
                     self.wait_for_command(vm, prog);
                } else if current_depth == self.step_start_depth {
                    if current_line != self.step_start_line || current_col != self.step_start_col {
                        self.paused = true;
                        self.adapter_tx.send(AdapterMessage::Vm(VmEvent::Stopped("step".to_string()))).unwrap();
                        self.wait_for_command(vm, prog);
                    }
                }
            },
            StepMode::StepOut => {
                // Stop if we returned (depth < start)
                if current_depth < self.step_start_depth {
                    self.paused = true;
                    self.adapter_tx.send(AdapterMessage::Vm(VmEvent::Stopped("step".to_string()))).unwrap();
                    self.wait_for_command(vm, prog);
                }
            },
            StepMode::None => {}
        }
    }
}
