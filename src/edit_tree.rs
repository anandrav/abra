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

impl ToString for Token {
    fn to_string(&self) -> String {
        unimplemented!()
    }
}

#[derive(Debug)]
pub enum TokenTree {
    Leaf(Token),
    Children(Vec<TokenTree>),
}

#[derive(Debug)]
pub enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
}

#[derive(Debug)]
pub struct Stmt {
    pub stmtkind: StmtKind,
    // pub tokens: TokenTree,
}

#[derive(Debug)]
pub enum StmtKind {
    /// just a semicolon
    EmptyHole,
    Let(Rc<Pat>, Option<Rc<Type>>, Rc<Expr>, Rc<Expr>),
    Expr(Expr),
}

#[derive(Debug)]
pub struct Expr {
    pub exprkind: ExprKind,
    // pub tokens: TokenTree,
}

type Count = u64;

// #[derive(Debug)]
// pub struct TextInfo {
//     pub chars: Count,
//     pub line_breaks: Count,
// }

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
        let exprkind = match &*parsed.exprkind {
            pt::ExprKind::Var(id) => ExprKind::Var(id.to_string()),
            pt::ExprKind::Str(s) => ExprKind::Str(s.to_string()),
            pt::ExprKind::Func(arg1, args, ty, body) => ExprKind::Func(
                arg1.clone(),
                args.clone(),
                ty.clone(),
                Expr::from(body.clone()),
            ),
            pt::ExprKind::FuncAp(f, arg1, args) => ExprKind::FuncAp(
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
    pub patkind: ExprKind,
    // pub tokens: TokenTree,
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

// macro_rules! vecdeque {
//     () => (
//         VecDeque::new()
//     );
//     ($elem:expr; $n:expr) => (
//         $crate::vec::from_elem($elem, $n).to_iter().collect()
//     );
//     ($($x:expr),*) => (
//         $crate::slice::into_vec(box [$($x),*]).to_iter().collect()
//     );
//     ($($x:expr,)*) => (vec![$($x),*].to_iter().collect())
// }

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
