use std::{io::{Read, BufReader, Cursor}, thread::current};

#[repr(u8)]
#[derive(Clone, Copy)]
pub(super) enum Instr {
    LoadInt,
    LoadFloat,
    Add,
    Sub,
    Mul,
    Div
}

impl TryFrom<u8> for Instr {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            x if x == Instr::LoadInt as u8 => Ok(Instr::LoadInt),
            x if x == Instr::LoadFloat as u8 => Ok(Instr::LoadFloat),
            x if x == Instr::Add as u8 => Ok(Instr::Add),
            x if x == Instr::Sub as u8 => Ok(Instr::Sub),
            x if x == Instr::Mul as u8 => Ok(Instr::Mul),
            x if x == Instr::Div as u8 => Ok(Instr::Div),
            _ => Err(())
        }
    }
}

pub(super) struct OpCode {
    data: [u8; 4]
}

impl OpCode {
    pub fn new(instr: Instr, dest_reg: u8) -> OpCode {
        OpCode{data: [instr as u8, dest_reg, 0, 0]}
    }

    pub fn get_data(&self) -> [u8; 4] {
        self.data
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
        let mut buffer = [0 as u8; 8];
        if let Ok(()) = self.cursor.read_exact(&mut buffer) {
            Some(i64::from_le_bytes(buffer))
        }
        else {
            None
        }
    }

    pub fn read_float(&mut self) -> Option<f64> {
        let mut buffer = [0 as u8; 8];
        if let Ok(()) = self.cursor.read_exact(&mut buffer) {
            Some(f64::from_le_bytes(buffer))
        }
        else {
            None
        }
    }
}