use std::fmt;
use crate::vm::gc::Handle;

/// A 64-bit tagged value.
/// 
/// Layout (LSB Tagging):
/// - xxx...xxx000: Handle (Pointer to Heap)
/// - xxx...xxx001: Small Integer (61-bit signed)
/// - xxx...xxx010: Small Float (32-bit f32)
/// - xxx...xxx011: Immediate (Bool, Nil, Char, etc.)
/// - xxx...xxx100: Header (Used inside the heap, not as a value)
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Value(u64);

impl Value {
    // --- Tags (3 bits) ---
    const TAG_HANDLE: u64    = 0b000;
    const TAG_INT: u64       = 0b001;
    const TAG_FLOAT: u64     = 0b010;
    const TAG_IMMEDIATE: u64 = 0b011;
    const TAG_HEADER: u64    = 0b100;
    
    const TAG_MASK: u64      = 0b111;

    // --- Immediate Constants ---
    const IMM_NIL: u64       = (0 << 4) | Self::TAG_IMMEDIATE;
    const IMM_FALSE: u64     = (1 << 4) | Self::TAG_IMMEDIATE;
    const IMM_TRUE: u64      = (2 << 4) | Self::TAG_IMMEDIATE;
    const IMM_UNDEFINED: u64 = (3 << 4) | Self::TAG_IMMEDIATE;

    // --- Constructors ---

    #[inline(always)]
    pub fn integer(val: i64) -> Self {
        // Shift left by 3. This works for any 61-bit signed integer.
        // If it overflows 61 bits, we should technically box it (BigInt),
        // but for now we assume it fits or truncate.
        let shifted = (val as u64) << 3;
        Value(shifted | Self::TAG_INT)
    }

    #[inline(always)]
    pub fn float(val: f32) -> Self {
        // We put the u32 bits of the float into the high part of the u64
        // just to keep it clean, though low part works too.
        let bits = val.to_bits() as u64;
        let shifted = bits << 32; 
        Value(shifted | Self::TAG_FLOAT)
    }

    #[inline(always)]
    pub fn object(handle: Handle) -> Self {
        // Handle index fits in 32 bits easily.
        let shifted = (handle.index() as u64) << 3;
        Value(shifted | Self::TAG_HANDLE)
    }

    #[inline(always)]
    pub fn boolean(b: bool) -> Self {
        if b { Value(Self::IMM_TRUE) } else { Value(Self::IMM_FALSE) }
    }

    #[inline(always)]
    pub fn nil() -> Self {
        Value(Self::IMM_NIL)
    }

    #[inline(always)]
    pub fn undefined() -> Self {
        Value(Self::IMM_UNDEFINED)
    }

    // --- Type Checkers ---

    #[inline(always)]
    pub fn is_int(&self) -> bool {
        (self.0 & Self::TAG_MASK) == Self::TAG_INT
    }

    #[inline(always)]
    pub fn is_float(&self) -> bool {
        (self.0 & Self::TAG_MASK) == Self::TAG_FLOAT
    }

    #[inline(always)]
    pub fn is_object(&self) -> bool {
        (self.0 & Self::TAG_MASK) == Self::TAG_HANDLE
    }

    #[inline(always)]
    pub fn is_bool(&self) -> bool {
        self.0 == Self::IMM_TRUE || self.0 == Self::IMM_FALSE
    }

    #[inline(always)]
    pub fn is_nil(&self) -> bool {
        self.0 == Self::IMM_NIL
    }

    // --- Accessors ---

    #[inline(always)]
    pub fn as_int(&self) -> i64 {
        // Arithmetic shift right to preserve sign
        (self.0 as i64) >> 3
    }

    #[inline(always)]
    pub fn as_float(&self) -> f32 {
        let bits = (self.0 >> 32) as u32;
        f32::from_bits(bits)
    }

    #[inline(always)]
    pub fn as_handle(&self) -> Handle {
        unsafe { Handle::from_raw((self.0 >> 3) as u32) }
    }

    #[inline(always)]
    pub fn as_bool(&self) -> bool {
        self.0 == Self::IMM_TRUE
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_int() {
            write!(f, "Int({})", self.as_int())
        } else if self.is_float() {
            write!(f, "Float({})", self.as_float())
        } else if self.is_object() {
            write!(f, "Obj({:?})", self.as_handle())
        } else if self.is_nil() {
            write!(f, "nil")
        } else if self.is_bool() {
            write!(f, "Bool({})", self.as_bool())
        } else {
            write!(f, "Unknown({:#x})", self.0)
        }
    }
}
