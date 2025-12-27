use std::io::{Cursor, Write};
use crate::parser::Atom;
use crate::vm::vp::{Instr, OpCode};

pub(super) struct BytecodeBuilder {
    pub cursor: Cursor<Vec<u8>>,
    pub listing: String,
    pub generate_asm: bool
}

impl BytecodeBuilder {
    pub fn new(generate_asm: bool) -> BytecodeBuilder {
        BytecodeBuilder{cursor: Cursor::new(vec![]), listing: String::new(), generate_asm}
    }

    pub fn load_atom(&mut self, atom: &Atom, reg: u8) {
        match atom {
            Atom::Boolean(b) => {
                let opcode = OpCode::new(Instr::LoadBool, reg, *b as u8, 0);
                let _ = self.cursor.write(&opcode.get_data());

                if self.generate_asm {
                    self.listing += &format!("{} {}, {}\n", Instr::LoadBool, reg, *b);
                }
            },
            Atom::Integer(i) => {
                let opcode = OpCode::new_dest(Instr::LoadInt, reg);
                let _ = self.cursor.write(&opcode.get_data());
                let _ = self.cursor.write(&i.to_le_bytes());

                if self.generate_asm {
                    self.listing += &format!("{} {}, {}\n", Instr::LoadInt, reg, *i);
                }
            }
            Atom::Float(f) => {
                let opcode = OpCode::new_dest(Instr::LoadFloat, reg);
                let _ = self.cursor.write(&opcode.get_data());
                let _ = self.cursor.write(&f.to_le_bytes());
                if self.generate_asm {
                    self.listing += &format!("{} {}, {}\n", Instr::LoadFloat, reg, *f);
                }
            },
            Atom::String(s) => {
                let opcode = OpCode::new_dest(Instr::LoadString, reg);
                let _ = self.cursor.write(&opcode.get_data());
                let _ = self.cursor.write(&s.len().to_le_bytes());
                let _ = self.cursor.write(s.as_bytes());
                if self.generate_asm {
                    self.listing += &format!("{} {}, {}\n", Instr::LoadString, reg, s);
                }
            },
        }
    }

    pub fn store_opcode(&mut self, instr: Instr, dest_reg: u8, r1: u8, r2: u8) {
        let opcode = [instr as u8, dest_reg, r1, r2];
        let _ = self.cursor.write(&opcode);

        if self.generate_asm {
            self.listing += &format!("{} {}, {}, {}\n", instr, dest_reg, r1, r2);
        }
    }

    pub fn store_make_closure(&mut self, dest_reg: u8, func_reg: u8, captures: &[u8]) {
        let count = captures.len();
        // Opcode: [MakeClosure, dest, func, count]
        // Note: count is limited to 255 here by u8 encoding in opcode[3]
        // If we need more, we should change encoding. For now assume < 256 captures.
        let opcode = [Instr::MakeClosure as u8, dest_reg, func_reg, count as u8];
        let _ = self.cursor.write(&opcode);
        let _ = self.cursor.write(captures);

        if self.generate_asm {
            self.listing += &format!("{} {}, {}, {:?}\n", Instr::MakeClosure, dest_reg, func_reg, captures);
        }
    }

    pub fn store_value(&mut self, val: &[u8]) {
        let _ = self.cursor.write(&val);

        if self.generate_asm {
            self.listing += &format!("[data; {}]", val.len());
        }
    }

    pub fn store_and_reset_pos(&mut self, pos: u64, val: &[u8]) {
        let cur_pos = self.cursor.position();
        self.cursor.set_position(pos);
        let _ = self.cursor.write(val);
        self.cursor.set_position(cur_pos);
    }

    pub fn position(&self) -> u64 {
        self.cursor.position()
    }
}
