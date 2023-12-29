use enum_display::EnumDisplay;


#[derive(Clone, Copy, Debug, EnumDisplay)]
pub enum Instruction {
    Define,
    Lambda,
    If,
    Not,
    And,
    Or,
    Plus,
    Minus,
    Multiply,
    Divide,
    Eq,
    Lt,
    Gt,
    Leq,
    Geq
}