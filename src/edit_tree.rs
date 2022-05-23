use operators::BinOpcode;
use std::rc::Rc;
use types::Type;

pub type Identifier = String;
pub type FuncArg = (Identifier, Option<Rc<Type>>);

#[derive(Debug)]
pub struct Block {Vec<Line>}

#[derive(Debug)]
pub struct Line {Vec<Line>}

#[derive(Debug)]
pub enum Operand {
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
    Let(Rc<Pat>, Option<Rc<Type>>, Rc<Expr>, Rc<Expr>),
    Func(FuncArg, Vec<FuncArg>, Option<Rc<Type>>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Match(Rc<Expr>, Vec<Rule>),
}

#[derive(Debug)]
pub enum Pat {
    Var(Identifier),
}