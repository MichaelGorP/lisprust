use std::fmt;
use crate::{lexer::Token, instructions};
use case_insensitive_hashmap::CaseInsensitiveHashMap;
use derive_more::derive::From;
use std::ops::Range;

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
pub enum SourceMap {
    Leaf(Range<usize>),
    List(Range<usize>, Vec<SourceMap>)
}

impl SourceMap {
    pub fn span(&self) -> Range<usize> {
        match self {
            SourceMap::Leaf(r) => r.clone(),
            SourceMap::List(r, _) => r.clone(),
        }
    }
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
            SExpression::List(l) => {
                write!(f, "(")?;
                for (i, e) in l.iter().enumerate() {
                    if i > 0 { write!(f, " ")?; }
                    write!(f, "{}", e)?;
                }
                write!(f, ")")
            },
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
        parser.instructions.insert("cond", instructions::Instruction::Cond);
        parser.instructions.insert("not", instructions::Instruction::Not);
        parser.instructions.insert("and", instructions::Instruction::And);
        parser.instructions.insert("or", instructions::Instruction::Or);
        parser.instructions.insert("+", instructions::Instruction::Plus);
        parser.instructions.insert("-", instructions::Instruction::Minus);
        parser.instructions.insert("*", instructions::Instruction::Multiply);
        parser.instructions.insert("/", instructions::Instruction::Divide);
        parser.instructions.insert("=", instructions::Instruction::Eq);
        parser.instructions.insert("eq?", instructions::Instruction::Eq);
        parser.instructions.insert("<", instructions::Instruction::Lt);
        parser.instructions.insert(">", instructions::Instruction::Gt);
        parser.instructions.insert("<=", instructions::Instruction::Leq);
        parser.instructions.insert(">=", instructions::Instruction::Geq);
        parser.instructions.insert("quote", instructions::Instruction::Quote);
        parser
    }

    fn parse_single(&self, tokens: &[(Token, std::ops::Range<usize>)]) -> Result<(SExpression, SourceMap, usize), ParseError> {
        if tokens.is_empty() {
             return Err(ParseError{error: "Unexpected end of input".to_string()});
        }
        let (token, span) = &tokens[0];
        let current_span = span.clone();
        
        match token {
            Token::Integer(n) => Ok((SExpression::Atom(Atom::Integer(*n)), SourceMap::Leaf(current_span), 1)),
            Token::Float(f) => Ok((SExpression::Atom(Atom::Float(*f)), SourceMap::Leaf(current_span), 1)),
            Token::Boolean(b) => Ok((SExpression::Atom(Atom::Boolean(*b)), SourceMap::Leaf(current_span), 1)),
            Token::String(s) => Ok((SExpression::Atom(Atom::String(s.clone())), SourceMap::Leaf(current_span), 1)),
            Token::Symbol(s) => {
                let it = self.instructions.get(s.as_str());
                match it {
                    Some(&instr) => Ok((SExpression::BuiltIn(instr), SourceMap::Leaf(current_span), 1)),
                    None => Ok((SExpression::Symbol(s.clone()), SourceMap::Leaf(current_span), 1))
                }
            },
            Token::Quote => {
                let (expr, map, consumed) = self.parse_single(&tokens[1..])?;
                let quote_sym = SExpression::BuiltIn(instructions::Instruction::Quote);
                let list_expr = SExpression::List(vec![quote_sym, expr]);
                let full_span = span.start..map.span().end;
                let full_map = SourceMap::List(full_span, vec![SourceMap::Leaf(span.clone()), map]);
                Ok((list_expr, full_map, consumed + 1))
            },
            Token::LParen => {
                let (list_expr, map, consumed) = self.parse(&tokens[1..])?;
                Ok((list_expr, map, consumed + 1))
            },
            Token::RParen => Err(ParseError{error: "Unexpected )".to_string()}),
        }
    }

    pub fn parse(&self, tokens: &[(Token, std::ops::Range<usize>)]) -> Result<(SExpression, SourceMap, usize), ParseError> {
        if tokens.is_empty() {
            return Err(ParseError{error: "Empty list".to_string()});
        }
        
        let mut list: Vec<SExpression> = Vec::new();
        let mut map_list: Vec<SourceMap> = Vec::new();
        let mut i = 0;
        let start_span = tokens[0].1.start;

        while i < tokens.len() {
            if let Token::RParen = tokens[i].0 {
                 let end_span = tokens[i].1.end;
                 return Ok((SExpression::List(list), SourceMap::List(start_span..end_span, map_list), i + 1));
            }
            
            let (expr, map, consumed) = self.parse_single(&tokens[i..])?;
            list.push(expr);
            map_list.push(map);
            i += consumed;
        }
        let end_span = if tokens.len() > 0 { tokens[tokens.len()-1].1.end } else { 0 };
        Ok((SExpression::List(list), SourceMap::List(start_span..end_span, map_list), tokens.len()))
    }
}