use std::fmt;
use crate::{lexer::Token, instructions};
use case_insensitive_hashmap::CaseInsensitiveHashMap;
use derive_more::derive::From;

#[derive(Debug, Clone, PartialEq, From)]
pub enum Atom {
    Boolean(bool),
    Integer(i64),
    Float(f64),
    String(String),

}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Atom::Boolean(b) => write!(f, "{}", b),
            Atom::Integer(i) => write!(f, "{}", i),
            Atom::Float(d) => write!(f, "{}", d),
            Atom::String(s) => write!(f, "{}", s),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Lambda {
    pub args: Vec<String>,
    pub body: SExpression
}

#[derive(Debug, Clone, PartialEq)]
pub enum SExpression {
    Atom(Atom),
    BuiltIn(instructions::Instruction),
    Symbol(String),
    List(Vec<SExpression>),
    Lambda(Box<Lambda>)
}

impl fmt::Display for SExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SExpression::Atom(l) => write!(f, "{}", l),
            SExpression::BuiltIn(b) => write!(f, "{}", b),
            SExpression::Symbol(s) => write!(f, "{}", s),
            SExpression::List(l) => write!(f, "{:?}", l),
            SExpression::Lambda(_) => write!(f, "Lambda")
        }
    }
}

impl<T> From<T> for SExpression
    where T: Into<Atom>,
{
    fn from(value: T) -> Self {
        SExpression::Atom(value.into())
    }
}


pub struct ParseError {
    error: String
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.error)
    }
}

pub struct Parser {
    instructions: CaseInsensitiveHashMap<instructions::Instruction>
}

impl Parser {
    pub fn new() -> Parser {
        let mut parser = Parser{instructions : CaseInsensitiveHashMap::new()};
        parser.instructions.insert("define", instructions::Instruction::Define);
        parser.instructions.insert("lambda", instructions::Instruction::Lambda);
        parser.instructions.insert("if", instructions::Instruction::If);
        parser.instructions.insert("let", instructions::Instruction::Let);
        parser.instructions.insert("let*", instructions::Instruction::LetStar);
        parser.instructions.insert("letrec", instructions::Instruction::Letrec);
        parser.instructions.insert("not", instructions::Instruction::Not);
        parser.instructions.insert("and", instructions::Instruction::And);
        parser.instructions.insert("or", instructions::Instruction::Or);
        parser.instructions.insert("+", instructions::Instruction::Plus);
        parser.instructions.insert("-", instructions::Instruction::Minus);
        parser.instructions.insert("*", instructions::Instruction::Multiply);
        parser.instructions.insert("/", instructions::Instruction::Divide);
        parser.instructions.insert("=", instructions::Instruction::Eq);
        parser.instructions.insert("<", instructions::Instruction::Lt);
        parser.instructions.insert(">", instructions::Instruction::Gt);
        parser.instructions.insert("<=", instructions::Instruction::Leq);
        parser.instructions.insert(">=", instructions::Instruction::Geq);
        parser
    }

    pub fn parse(&self, tokens: &[Token]) -> Result<(SExpression, usize), ParseError> {
        if tokens.is_empty() {
            return Err(ParseError{error: "Empty list".to_string()});
        }
        
        let mut list: Vec<SExpression> = Vec::new();
        let mut i = 0;
        while i < tokens.len() {
            let token = &tokens[i];
            match token {
                Token::Integer(n) => list.push(SExpression::Atom(Atom::Integer(*n))),
                Token::Float(f) => list.push(SExpression::Atom(Atom::Float(*f))),
                Token::Boolean(b) => list.push(SExpression::Atom(Atom::Boolean(*b))),
                Token::String(s) => list.push(SExpression::Atom(Atom::String(s.clone()))),
                Token::LParen => {
                    let sub_list = self.parse(&tokens[i + 1..])?;
                    i += sub_list.1;
                    if i == tokens.len() && list.is_empty() {
                        return Ok((sub_list.0, i));
                    }
                    else {
                        list.push(sub_list.0);
                    }
                }
                Token::RParen => { 
                    return Ok((SExpression::List(list), i + 1));
                },
                Token::Symbol(s) => {
                    let it = self.instructions.get(s.as_str());
                    match it {
                        Some(&instr) => list.push(SExpression::BuiltIn(instr)),
                        None => list.push(SExpression::Symbol(s.clone()))
                    }
                }
            }
            i += 1;
        }
        Ok((SExpression::List(list), tokens.len()))
    }
}