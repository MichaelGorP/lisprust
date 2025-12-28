use logos::Logos;

#[derive(Debug, PartialEq, Clone, Default)]
pub enum TokenizingError {
    NumberParseError,
    #[default]
    Other,
}

impl From<std::num::ParseIntError> for TokenizingError {
    fn from(_: std::num::ParseIntError) -> Self {
        TokenizingError::NumberParseError
    }
}

impl From<std::num::ParseFloatError> for TokenizingError {
    fn from(_: std::num::ParseFloatError) -> Self {
        TokenizingError::NumberParseError
    }
}

impl From<std::convert::Infallible> for TokenizingError {
    fn from(_: std::convert::Infallible) -> Self {
        TokenizingError::Other
    }
}

impl From<std::str::ParseBoolError> for TokenizingError {
    fn from(_: std::str::ParseBoolError) -> Self {
        TokenizingError::Other
    }
}

#[derive(Logos, Debug, PartialEq)]
#[logos(error = TokenizingError)]
#[logos(skip r"[ \t\r\n\f]+")]
pub enum Token {
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[regex(r"[+-]?(0|[1-9][_0-9]*)", |lex| { lex.slice().parse() }, priority = 3)]
    Integer(i64),
    #[regex("(true|false)", |lex| { lex.slice().parse()})]
    Boolean(bool),
    #[regex(r"[+-]?((\d+\.?\d*)|(\.\d+))(([eE][+-]?)?\d+)?", |lex| { lex.slice().parse() }, priority = 2)]
    Float(f64),
    #[regex("\"*\"", |lex| lex.slice().parse())]
    String(String),
    #[regex("[^ \\t\\r\\n\\f\"\\(\\)]+", |lex| lex.slice().parse())]
    Symbol(String),
}

pub fn tokenize(prog: &str) -> Result<Vec<(Token, std::ops::Range<usize>)>, TokenizingError> {
    let lexer = Token::lexer(prog);
    let tokens: Result<Vec<(Token, std::ops::Range<usize>)>, TokenizingError> = lexer.spanned().map(|(token, span)| match token {
        Ok(t) => Ok((t, span)),
        Err(e) => Err(e)
    }).collect();
    tokens
}
