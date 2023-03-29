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
    Tuple(Vec<Rc<Expr>>),
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
    Tuple(Vec<Rc<Pat>>),
}

pub fn is_val(expr: &Rc<Expr>) -> bool {
    use self::Expr::*;
    match expr.as_ref() {
        Var(_) => false,
        Unit => true,
        Int(_) => true,
        Str(_) => true,
        Bool(_) => true,
        Func(_, _, _) => true,
        Tuple(elements) => elements.iter().all(is_val),
        BinOp(_, _, _) => false,
        Let(_, _, _) => false,
        FuncAp(_, _, _) => false,
        If(_, _, _) => false,
        EffectAp(_, _) => false,
        ConsumedEffect => false,
    }
}
