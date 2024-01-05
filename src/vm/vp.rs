use std::{io::{Read, Cursor}, mem::size_of, ptr::read};

#[repr(u8)]
#[derive(Clone, Copy)]
pub(super) enum Instr {
    //register handling
    LoadInt,
    LoadFloat,
    LoadBool,
    LoadString,
    CopyReg,
    //arithmetic
    Add,
    Sub,
    Mul,
    Div,
    //comparisons
    Eq,
    Lt,
    Gt,
    Leq,
    Geq,
    //control flow
    Not,
    Jump,
    //definitions, symbols, and function handling
    Define,
    LoadGlobal,
    LoadFuncRef
}

#[repr(u8)]
#[derive(Clone, Copy)]
pub(super) enum JumpCondition {
    JumpTrue,
    JumpFalse,
    Jump
}

impl TryFrom<u8> for Instr {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            x if x == Instr::LoadInt as u8 => Ok(Instr::LoadInt),
            x if x == Instr::LoadFloat as u8 => Ok(Instr::LoadFloat),
            x if x == Instr::LoadBool as u8 => Ok(Instr::LoadBool),
            x if x == Instr::LoadString as u8 => Ok(Instr::LoadString),
            x if x == Instr::CopyReg as u8 => Ok(Instr::CopyReg),
            x if x == Instr::Add as u8 => Ok(Instr::Add),
            x if x == Instr::Sub as u8 => Ok(Instr::Sub),
            x if x == Instr::Mul as u8 => Ok(Instr::Mul),
            x if x == Instr::Div as u8 => Ok(Instr::Div),
            x if x == Instr::Eq as u8 => Ok(Instr::Eq),
            x if x == Instr::Lt as u8 => Ok(Instr::Lt),
            x if x == Instr::Gt as u8 => Ok(Instr::Gt),
            x if x == Instr::Leq as u8 => Ok(Instr::Leq),
            x if x == Instr::Geq as u8 => Ok(Instr::Geq),
            x if x == Instr::Not as u8 => Ok(Instr::Not),
            x if x == Instr::Jump as u8 => Ok(Instr::Jump),
            x if x == Instr::Define as u8 => Ok(Instr::Define),
            x if x == Instr::LoadGlobal as u8 => Ok(Instr::LoadGlobal),
            x if x == Instr::LoadFuncRef as u8 => Ok(Instr::LoadFuncRef),
            _ => Err(())
        }
    }
}

pub(super) struct OpCode {
    data: [u8; 4]
}

impl OpCode {
    pub fn new_dest(instr: Instr, dest_reg: u8) -> OpCode {
        OpCode{data: [instr as u8, dest_reg, 0, 0]}
    }

    pub fn new(instr: Instr, dest_reg: u8, r1: u8, r2: u8) -> OpCode {
        OpCode{data: [instr as u8, dest_reg, r1, r2]}
    }

    pub fn get_data(&self) -> [u8; 4] {
        self.data
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(packed)]
pub(super) struct FunctionHeader {
    pub register_count: u8,
    pub result_reg: u8
}

impl FunctionHeader {
    pub fn as_u8_slice(&self) -> &[u8] {
         unsafe { core::slice::from_raw_parts((self as *const FunctionHeader) as *const u8, std::mem::size_of::<FunctionHeader>()) }
    }

    fn read(reader: &mut Cursor<Vec<u8>>) -> FunctionHeader {
        let mut buf = [0; std::mem::size_of::<FunctionHeader>()];
        let _ = reader.read(&mut buf);
        let header: FunctionHeader = unsafe { std::mem::transmute(buf) };
        header
    }
}

pub struct VirtualProgram {
    cursor: Cursor<Vec<u8>>,
    result_reg: u8
}


impl VirtualProgram {
    pub(super) fn new(bytecode: Vec<u8>, result_reg: u8) -> VirtualProgram {
        let prog = VirtualProgram{cursor: Cursor::new(bytecode), result_reg};
        prog
    }

    pub fn get_result_reg(&self) -> u8 {
        self.result_reg
    }

    pub fn read_opcode(&mut self) -> Option<[u8; 4]> {
        let mut buffer = [0 as u8; 4];
        if let Ok(()) = self.cursor.read_exact(&mut buffer) {
            Some(buffer)
        }
        else {
            None
        }
    }

    pub fn read_int(&mut self) -> Option<i64> {
        let mut buffer = [0 as u8; size_of::<i64>()];
        if let Ok(()) = self.cursor.read_exact(&mut buffer) {
            Some(i64::from_le_bytes(buffer))
        }
        else {
            None
        }
    }

    pub fn read_float(&mut self) -> Option<f64> {
        let mut buffer = [0 as u8; size_of::<f64>()];
        if let Ok(()) = self.cursor.read_exact(&mut buffer) {
            Some(f64::from_le_bytes(buffer))
        }
        else {
            None
        }
    }

    pub fn read_string(&mut self) -> Option<String> {
        let mut buffer = [0 as u8; size_of::<usize>()];
        if let Ok(()) = self.cursor.read_exact(&mut buffer) {
            let size = usize::from_le_bytes(buffer);
            let mut str_buf: Vec<u8> = Vec::with_capacity(size);
            str_buf.resize(size, 0);
            if let Ok(()) = self.cursor.read_exact(&mut str_buf) {
                if let Ok(str) = String::from_utf8(str_buf) {
                    return Some(str);
                }
            }
        }
        return None;
    }

    pub(super) fn read_function_header(&mut self) -> Option<FunctionHeader> {
        Some(FunctionHeader::read(&mut self.cursor))
    }

    pub fn jump(&mut self, distance: i64) {
        let pos = (self.cursor.position() as i64) + distance;
        self.cursor.set_position(pos as u64);
    }
}