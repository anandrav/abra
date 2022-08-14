use operators::BinOpcode;
use regex::Regex;
use std::collections::VecDeque;
use std::rc::Rc;
use types::Type;

pub type Identifier = String;
pub type FuncArg = (Identifier, Option<Rc<Type>>);

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
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    FuncAp(Rc<Expr>, Rc<Expr>, VecDeque<Rc<Expr>>),
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
