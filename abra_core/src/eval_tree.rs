use environment::Environment;
use operators::BinOpcode;
use std::cell::RefCell;
use std::rc::Rc;

pub type Identifier = String;

#[derive(Debug)]
pub enum Expr {
    Var(Identifier),
    Unit,
    Int(i32),
    Str(String),
    Bool(bool),
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    Let(Rc<Pat>, Rc<Expr>, Rc<Expr>),
    Func(Identifier, Rc<Expr>, Rc<RefCell<Environment>>),
    FuncAp(Rc<Expr>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    // Match(Rc<Expr>, Vec<Rule>),
}

// pub type Rule = (Rc<Pat>, Rc<Expr>);

#[derive(Debug)]
pub enum Pat {
    Var(String),
}
