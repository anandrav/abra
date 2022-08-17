use operators::BinOpcode;
use regex::Regex;
use std::collections::VecDeque;
use std::rc::Rc;
use types::Type;

use crate::parse_tree as pt;

pub type Identifier = String;
pub type FuncArg = (Identifier, Option<Rc<Type>>);

#[derive(Debug)]
pub enum Token {
    Whitespace(Count),
    Newline,
    Tab,
    OpenDelim(Delimiter),
    CloseDelim(Delimiter),
    Identifier(String),
}

#[derive(Debug)]
pub enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
}

#[derive(Debug)]
pub struct Stmt {
    // pub id: NodeId,
    pub stmtkind: StmtKind,
    // pub textinfo: TextInfo,
    // pub tokens: Option<LazyTokenStream>,
}

#[derive(Debug)]
pub enum StmtKind {
    EmptyHole, // just a semicolon
    Let(Rc<Pat>, Option<Rc<Type>>, Rc<Expr>, Rc<Expr>),
    Expr(Expr),
}

#[derive(Debug)]
pub struct Expr {
    // pub id: NodeId,
    pub exprkind: ExprKind,
    // pub textinfo: TextInfo,
    // pub tokens: Option<LazyTokenStream>,
}

type Count = u64;

#[derive(Debug)]
pub struct TextInfo {
    pub chars: Count,
    pub line_breaks: Count,
}

#[derive(Debug)]
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
    OpSeq(VecDeque<Op>),
    FuncAp(Rc<Expr>, Rc<Expr>, VecDeque<Rc<Expr>>),
}

impl Expr {
    pub fn from(parsed: Rc<pt::Expr>) -> Rc<Self> {
        let exprkind = match &*parsed {
            pt::Expr::Var(id) => ExprKind::Var(id.to_string()),
            pt::Expr::Str(s) => ExprKind::Str(s.to_string()),
            pt::Expr::Func(arg1, args, ty, body) => ExprKind::Func(
                arg1.clone(),
                args.clone(),
                ty.clone(),
                Expr::from(body.clone()),
            ),
            pt::Expr::FuncAp(f, arg1, args) => ExprKind::FuncAp(
                Expr::from(f.clone()),
                Expr::from(arg1.clone()),
                args.iter().map(|x| Expr::from(x.clone())).collect(),
            ),
            _ => {
                println!("{:#?} is unimplemented", parsed);
                panic!("unimplemented")
            }
        };
        Rc::new(Expr { exprkind })
    }
}

pub type Rule = (Rc<Pat>, Rc<Expr>);

#[derive(Debug)]
pub struct Pat {
    // pub id: NodeId,
    pub patkind: ExprKind,
    // pub tokens: Option<LazyTokenStream>,
}

#[derive(Debug)]
pub enum PatKind {
    EmptyHole,
    InvalidText(String),
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
}
#[derive(Debug)]
pub enum Op {
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
