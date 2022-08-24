use operators::BinOpcode;
use pest::error::{Error, ErrorVariant, InputLocation::Pos};
use pest::iterators::Pair;
use pest::Parser;
use pest_derive::Parser;
use std::collections::VecDeque;
use std::fmt;
use std::rc::Rc;
use types::Type;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct MyParser;

pub type Identifier = String;
pub type FuncArg = (Identifier, Option<Rc<Type>>);

#[derive(Debug, PartialEq)]
pub enum Action {
    InsertChar { c: char, loc: usize },
    Backspace { loc: usize },
}

// #[derive(Debug, PartialEq)]
// pub enum Token {
//     Space,
//     Tab,
//     Newline,

//     OpenDelim(Delimiter),
//     CloseDelim(Delimiter),

//     Identifier(String),

//     OpEq,
//     OpAdd,
//     OpSub,
//     OpMult,

//     Semicolon,
// }

// impl ToString for Token {
//     fn to_string(&self) -> String {
//         unimplemented!()
//     }f
// }

#[derive(Debug, PartialEq)]
pub enum Kind {
    Declaration,
    ExprStatement,

    EmptyHole,
    InvalidText,
    Var,
    Unit,
    Int,
    Bool,
    Str,
    Func,
    If,
    Block,
    BinOp,
    FuncAp,
}

impl Kind {
    pub fn from_rule(rule: &Rule) -> Self {
        match rule {
            Rule::declaration => Kind::Declaration,
            Rule::expression_statement => Kind::ExprStatement,
            _ => unimplemented!(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct TokenTree {
    kind: Rule,
    contents: TokenContents,
}

#[derive(Debug, PartialEq)]
pub enum TokenContents {
    Token(String),
    Children(Vec<Rc<TokenTree>>),
}

// pub fn fix(s: &str) -> String {
//     println!("fix: {}", s);
//     let _ = MyParser::parse(Rule::program, &s).unwrap_or_else(|e| match e {
//         _ => {
//             if let ErrorVariant::ParsingError {
//                 positives,
//                 negatives,
//             } = e.variant
//             {
//                 if positives.contains(&Rule::placeholder) {
//                     let mut s = String::from(s);
//                     if let Pos(p) = e.location {
//                         s.insert_str(p, "_placeholder_");
//                         return fix(&s);
//                     }
//                 }
//             }
//             println!("{:#?}", e);
//             panic!()
//         }
//     });
//     s.to_string()
// }

pub fn fix(s: &str) -> String {
    println!("fix: {}", s);
    if let Err(e) = MyParser::parse(Rule::program, &s) {
        if let ErrorVariant::ParsingError {
            positives,
            negatives,
        } = e.variant
        {
            if positives.contains(&Rule::placeholder) {
                let mut s = String::from(s);
                if let Pos(p) = e.location {
                    s.insert_str(p, "_placeholder_");
                    return fix(&s);
                }
            }
        }
        // println!("{:#?}", e);
        panic!()
    }
    s.to_string()
}

impl TokenTree {
    fn from_pair(pair: Pair<Rule>) -> Rc<Self> {
        // A pair is a combination of the rule which matched and a span of input
        println!("Rule:    {:?}", pair.as_rule());
        println!("Span:    {:?}", pair.as_span());
        println!("Text:    {}", pair.as_str());

        let rule = pair.as_rule();
        let as_str = pair.as_str();
        let children: Vec<_> = pair.into_inner().map(|x| TokenTree::from_pair(x)).collect();
        let contents = if !children.is_empty() {
            TokenContents::Children(children)
        } else {
            TokenContents::Token(as_str.to_string())
        };
        Rc::new(TokenTree {
            kind: rule,
            contents,
        })
    }

    pub fn from(s: &str) -> Rc<Self> {
        let pairs = MyParser::parse(Rule::expression, &s).unwrap_or_else(|e| panic!("{}", e));
        let pair = pairs.peek().unwrap();
        Self::from_pair(pair)
    }

    // pub fn from(s: &str) {
    //     let pairs = MyParser::parse(Rule::expression, &s).unwrap_or_else(|e| panic!("{}", e));

    //     // Because ident_list is silent, the iterator will contain idents
    //     for pair in pairs {
    //         // A pair is a combination of the rule which matched and a span of input
    //         println!("Rule:    {:?}", pair.as_rule());
    //         println!("Span:    {:?}", pair.as_span());
    //         println!("Text:    {}", pair.as_str());

    //         // A pair can be converted to an iterator of the tokens which make it up:
    //         for inner_pair in pair.into_inner() {
    //             match inner_pair.as_rule() {
    //                 rule => println!("Debug: {:#?}", rule),
    //             };
    //         }
    //     }
    // }
}

impl fmt::Display for TokenTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.contents)
    }
}

impl fmt::Display for TokenContents {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenContents::Token(s) => write!(f, "{}", s),
            TokenContents::Children(children) => {
                for child in children {
                    write!(f, "{}", child)?;
                }
                Ok(())
            }
        }
    }
}

// #[derive(Debug, PartialEq)]
// pub struct Node {
//     id: u64,
// }

// #[derive(Debug, PartialEq)]
// pub enum Delimiter {
//     Parenthesis,
//     Brace,
//     Bracket,
// }

#[derive(Debug, PartialEq)]
pub struct Stmt {
    pub stmtkind: StmtKind,
    // pub tokens: TokenTree,
}

#[derive(Debug, PartialEq)]
pub enum StmtKind {
    /// just a semicolon
    EmptyHole,
    Let(Rc<Pat>, Option<Rc<Type>>, Rc<Expr>, Rc<Expr>),
    Expr(Expr),
}

#[derive(Debug, PartialEq)]
pub struct Expr {
    pub exprkind: ExprKind,
    // pub tokens: TokenTree,
}

#[derive(Debug, PartialEq)]
pub enum ExprKind {
    EmptyHole,
    InvalidText(String),
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
    Func(FuncArg, Vec<FuncArg>, Option<Rc<Type>>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Block(VecDeque<Rc<Stmt>>),
    BinOp(Rc<Expr>, Operator, Rc<Expr>),
    FuncAp(Rc<Expr>, Rc<Expr>, VecDeque<Rc<Expr>>),
}

#[derive(Debug, PartialEq)]
pub struct Pat {
    pub patkind: PatKind,
    // pub tokens: TokenTree,
}

#[derive(Debug, PartialEq)]
pub enum PatKind {
    EmptyHole,
    InvalidText(String),
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
}
#[derive(Debug, PartialEq)]
pub enum Op {
    Operand(Rc<Expr>),
    Operator(Operator),
}

#[derive(Debug, PartialEq)]
pub enum Operator {
    EmptyHole,
    InvalidText(String),
    Valid(BinOpcode),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_int() {}
}
