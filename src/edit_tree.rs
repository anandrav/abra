use operators::BinOpcode;
use regex::Regex;
use std::collections::VecDeque;
use std::rc::Rc;
use types::Type;

use crate::parse_tree as pt;

pub type Identifier = String;
pub type FuncArg = (Identifier, Option<Rc<Type>>);

pub struct Cursor {
    parents: Vec<Rc<Expr>>,
    current: Rc<Expr>,
}

impl Cursor {
    pub fn next(self) -> Option<Self> {
        match &*self.current {
            _ => panic!("unimplemented"),
        }
    }

    pub fn edit(self, action: Action) -> Option<Self> {
        None
    }
}

#[derive(Debug)]
pub enum Expr {
    EmptyHole,
    InvalidText(String),
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
    Let(Rc<Pat>, Option<Rc<Type>>, Rc<Expr>, Rc<Expr>),
    Func(FuncArg, Vec<FuncArg>, Option<Rc<Type>>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Match(Rc<Expr>, Vec<Rule>),
    Block(VecDeque<Rc<Expr>>),
    OpSeq(VecDeque<OpSeqToken>),
    FuncAp(Rc<Expr>, Rc<Expr>, VecDeque<Rc<Expr>>),
}
impl Expr {
    pub fn from(parsed: Rc<pt::Expr>) -> Rc<Self> {
        let expr = match &*parsed {
            pt::Expr::Var(id) => Expr::Var(id.to_string()),
            pt::Expr::Str(s) => Expr::Str(s.to_string()),
            pt::Expr::Func(arg1, args, ty, body) => Expr::Func(
                arg1.clone(),
                args.clone(),
                ty.clone(),
                Expr::from(body.clone()),
            ),
            pt::Expr::FuncAp(f, arg1, args) => Expr::FuncAp(
                Expr::from(f.clone()),
                Expr::from(arg1.clone()),
                args.iter().map(|x| Expr::from(x.clone())).collect(),
            ),
            _ => {
                println!("{:#?} is unimplemented", parsed);
                panic!("unimplemented")
            }
        };
        Rc::new(expr)
    }
}
pub type Rule = (Rc<Pat>, Rc<Expr>);
#[derive(Debug)]
pub enum Pat {
    EmptyHole,
    InvalidText(String),
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
}
#[derive(Debug)]
pub enum OpSeqToken {
    Operand(Rc<Expr>),
    Operator(Operator),
}

#[derive(Debug)]
pub enum Whitespace {
    Space,
    Newline,
}

#[derive(Debug)]
pub enum Operator {
    EmptyHole,
    InvalidText(String),
    Valid(BinOpcode),
}

#[derive(Debug)]
pub enum CursorPosition {
    Before,
    After,
}

pub type CursorPositionText = usize;

macro_rules! vecdeque {
    () => (
        VecDeque::new()
    );
    ($elem:expr; $n:expr) => (
        $crate::vec::from_elem($elem, $n).to_iter().collect()
    );
    ($($x:expr),*) => (
        $crate::slice::into_vec(box [$($x),*]).to_iter().collect()
    );
    ($($x:expr,)*) => (vec![$($x),*].to_iter().collect())
}

#[derive(Debug)]
pub enum Action {
    Insert(char),
    Backspace,
    MoveLeft,
    MoveRight,
}

fn is_identifier(text: &str) -> bool {
    let re = Regex::new(r"[a-zA-Z_.][.a-zA-Z_0-9']*(\.:[.+/*=-]+)?").unwrap();
    return re.is_match(text);
}
