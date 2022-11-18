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

// pub type Identifier = String;
// pub type FuncArg = (Identifier, Option<Rc<Type>>);

pub fn handle_action(action: Action, tree: &mut Rc<TokenTree>, cursor: &mut Cursor) {
    match action {
        Action::MoveLeft => match cursor {
            Cursor::Point(Location { token, tposition }) => {
                let t = tree.token_at_index(*token).unwrap();
                if *tposition == 0 {
                    *cursor = Cursor::Point(Location {
                        token: *token - 1,
                        tposition: t.num_points() - 2,
                    })
                } else {
                    *cursor = Cursor::Point(Location {
                        token: *token,
                        tposition: *tposition - 1,
                    })
                }
            }
            _ => unimplemented!(),
        },
        Action::MoveRight => match cursor {
            Cursor::Point(Location { token, tposition }) => {
                let t = tree.token_at_index(*token).unwrap();
                if *tposition == t.num_points() - 1 {
                    *cursor = Cursor::Point(Location {
                        token: *token + 1,
                        tposition: 1,
                    })
                } else {
                    *cursor = Cursor::Point(Location {
                        token: *token,
                        tposition: *tposition + 1,
                    })
                }
            }
            _ => unimplemented!(),
        },
        _ => (),
    }
}

fn move_cursor(tree: &Rc<TokenTree>, cursor: &mut Cursor) {}

#[derive(Debug, PartialEq)]
pub enum Cursor {
    Point(Location),
    Selection { begin: Location, end: Location },
}

#[derive(Debug, PartialEq)]
pub struct Location {
    pub token: usize,
    pub tposition: usize,
}

#[derive(Debug, PartialEq)]
pub enum Action {
    MoveLeft,
    MoveRight,
    InsertChar { c: char, loc: usize },
    Backspace { loc: usize },
}

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    // Whitespace
    Space,
    Tab,
    Newline,

    Placeholder,

    // Delimiter
    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    OpenBracket,
    CloseBracket,

    Identifier(String),
    IntLit(String),
    StrLit(String),
    BoolLit(String),

    // Operators
    OpAssign,
    OpEq,
    OpAdd,
    OpSub,
    OpMult,

    Semicolon,

    // Keywords
    Let,
    If,
    Else,
}

impl Token {
    fn from(rule: &Rule, s: &str) -> Self {
        match rule {
            Rule::placeholder => Self::Placeholder,
            Rule::block_start => Self::OpenBrace,
            Rule::block_end => Self::CloseBrace,
            Rule::identifier => Self::Identifier(s.to_string()),
            Rule::literal_number => Self::IntLit(s.to_string()),
            Rule::literal_string => Self::StrLit(s.to_string()),
            Rule::literal_bool => Self::BoolLit(s.to_string()),
            Rule::op_assign => Self::OpAssign,
            Rule::op_eq => Self::OpEq,
            Rule::op_addition => Self::OpAdd,
            Rule::op_subtraction => Self::OpSub,
            Rule::op_multiplication => Self::OpMult,
            Rule::semicolon => Self::Semicolon,
            Rule::let_keyword => Self::Let,
            Rule::if_keyword => Self::If,
            Rule::else_keyword => Self::Else,
            Rule::WHITESPACE => match s {
                " " => Self::Space,
                "\t" => Self::Tab,
                "\n" => Self::Newline,
                _ => panic!("String {} not a WHITESPACE token!", s),
            },
            _ => panic!("Rule {:#?} not a primitive token!", rule),
        }
    }

    fn to_str(&self) -> String {
        use self::Token::*;
        let s = match self {
            Space => " ",
            Tab => "\t",
            Newline => "\n",
            Placeholder => "_",
            OpenParen => "(",
            CloseParen => ")",
            OpenBrace => "{",
            CloseBrace => "}",
            OpenBracket => "[",
            CloseBracket => "]",
            Identifier(s) => s,
            IntLit(s) => s,
            StrLit(s) => s,
            BoolLit(s) => s,
            OpAssign => "=",
            OpEq => "==",
            OpAdd => "+",
            OpSub => "-",
            OpMult => "*",
            Semicolon => ";",
            Let => "let",
            If => "if",
            Else => "else",
            _ => panic!(),
        };
        s.to_owned()
    }

    pub fn num_points(&self) -> usize {
        use self::Token::*;
        match self {
            Space | Tab | Placeholder | OpenParen | CloseParen | OpenBrace | CloseBrace
            | OpenBracket | CloseBracket | OpAssign | OpAdd | OpSub | OpMult | Semicolon | Let
            | If | Else | OpEq => 2,
            Identifier(s) | IntLit(s) | StrLit(s) | BoolLit(s) => s.len() + 1,
            Newline => 0,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_str())
    }
}

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
    pub form: Rule,
    pub contents: Contents,
}

#[derive(Debug, PartialEq)]
pub enum Contents {
    Token(Token),
    Children(Vec<Rc<TokenTree>>),
}

pub fn fix(s: &str) -> String {
    // println!("fix: {}", s);
    if let Err(e) = MyParser::parse(Rule::program, &s) {
        if let ErrorVariant::ParsingError {
            positives,
            negatives,
        } = e.variant
        {
            if positives.contains(&Rule::placeholder) {
                let mut s = String::from(s);
                if let Pos(p) = e.location {
                    s.insert_str(p, &Token::Placeholder.to_str());
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
            Contents::Children(children)
        } else {
            Contents::Token(Token::from(&rule, &as_str))
        };
        Rc::new(TokenTree {
            form: rule,
            contents,
        })
    }

    pub fn from(s: &str) -> Rc<Self> {
        let pairs = MyParser::parse(Rule::expression, &s).unwrap_or_else(|e| panic!("{}", e));
        let pair = pairs.peek().unwrap();
        Self::from_pair(pair)
    }

    pub fn num_tokens(&self) -> i32 {
        match &self.contents {
            Contents::Token(_) => 1,
            Contents::Children(children) => children.iter().map(|x| x.num_tokens()).sum(),
        }
    }

    pub fn token_at_index(&self, index: usize) -> Option<Token> {
        match (&self.contents, index) {
            (Contents::Token(t), 0) => Some(t.clone()),
            (Contents::Children(children), _) => {
                let mut index = index;
                for c in children {
                    let len = c.num_tokens() as usize;
                    if len > index {
                        return c.token_at_index(index);
                    } else {
                        index = index - len;
                    }
                }
                return None;
            }
            _ => None,
        }
    }
}

impl fmt::Display for TokenTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.contents)
    }
}

impl fmt::Display for Contents {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Contents::Token(t) => write!(f, "{}", t),
            Contents::Children(children) => {
                for child in children {
                    write!(f, "{}", child)?;
                }
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_int() {}
}
