use enum_display::EnumDisplay;


#[derive(Clone, Copy, Debug, EnumDisplay, PartialEq)]
pub enum Instruction {
    Define,
    Lambda,
    If,
    Let,
    LetStar,
    Letrec,
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
    Geq,
    Quote
}