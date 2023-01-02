use crate::environment::Environment;
use crate::operators::BinOpcode;
use crate::side_effects;
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
    Func(Identifier, Rc<Expr>, Option<Rc<RefCell<Environment>>>),
    FuncAp(Rc<Expr>, Rc<Expr>, Option<Rc<RefCell<Environment>>>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    EffectAp(side_effects::Effect, Vec<Rc<Expr>>),
    ConsumedEffect,
}

#[derive(Debug)]
pub enum Pat {
    Var(String),
}

pub fn is_val(expr: &Rc<Expr>) -> bool {
    use self::Expr::*;
    matches!(&*expr.clone(), Unit | Int(_) | Str(_) | Bool(_) | Func(..))
}
