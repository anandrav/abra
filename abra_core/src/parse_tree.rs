use operators::BinOpcode;
use types::Type;

type Identifier = String;

#[derive(Debug)]
pub enum Expr {
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    BinOp(Box<Expr>, BinOpcode, Box<Expr>),
    Let(Box<Pat>, Option<Type>, Box<Expr>, Box<Expr>),
    Func(Identifier, Option<Type>, Box<Expr>),
    FuncAp(Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<Rule>)
}

pub type Rule = (Box<Pat>, Box<Expr>);

#[derive(Debug)]
pub enum Pat {
    Var(Identifier)
}