use operators::BinOpcode;
use std::rc::Rc;
use types::Type;

pub type Identifier = String;
pub type FuncArg = (Identifier, Option<Rc<Type>>);

#[derive(Debug)]
pub enum Expr {
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    Let(Rc<Pat>, Option<Rc<Type>>, Rc<Expr>, Rc<Expr>),
    Func(FuncArg, Vec<FuncArg>, Option<Rc<Type>>, Rc<Expr>),
    FuncAp(Rc<Expr>, Rc<Expr>, Vec<Rc<Expr>>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Match(Rc<Expr>, Vec<Rule>),
}

pub type Rule = (Rc<Pat>, Rc<Expr>);

#[derive(Debug)]
pub enum Pat {
    Var(Identifier),
}
