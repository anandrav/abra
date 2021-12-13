use std::rc::Rc;
use operators::BinOpcode;
use types::Type;

pub type Identifier = String;

#[derive(Debug)]
pub enum Expr {
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    Let(Rc<Pat>, Option<Type>, Rc<Expr>, Rc<Expr>),
    Func(Identifier, Option<Type>, Option<Type>, Rc<Expr>),
    FuncAp(Rc<Expr>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Match(Rc<Expr>, Vec<Rule>)
}

pub type Rule = (Rc<Pat>, Rc<Expr>);

#[derive(Debug)]
pub enum Pat {
    Var(Identifier)
}