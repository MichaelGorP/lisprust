#[derive(Clone, Copy, PartialEq, Debug)]
pub enum JitType {
    Int,
    Float,
}

// Constants for Value layout
// Assumes #[repr(C, u8)] for Value enum
pub const TAG_OFFSET: i32 = 0;
// Data offset depends on alignment. For 64-bit types (i64, f64, ptr), alignment is 8.
// So tag (1 byte) + padding (7 bytes) = 8 bytes offset.
pub const DATA_OFFSET: i32 = 8;
