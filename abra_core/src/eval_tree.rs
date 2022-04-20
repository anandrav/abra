use environment::Environment;
use operators::BinOpcode;
use side_effects;
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
    FuncAp(Rc<Expr>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    // Match(Rc<Expr>, Vec<Rule>),
    EffectAp(side_effects::Effect, Vec<Rc<Expr>>),
    ConsumedEffect,
}

// pub type Rule = (Rc<Pat>, Rc<Expr>);

#[derive(Debug)]
pub enum Pat {
    Var(String),
}

pub fn is_val(expr: &Rc<Expr>) -> bool {
    use self::Expr::*;
    match &*expr.clone() {
        Unit | Int(_) | Str(_) | Bool(_) => true,
        _ => false,
    }
}
