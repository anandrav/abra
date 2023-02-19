use std::{
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::operators::BinOpcode;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Unknown(Id),
    Unit,
    Int,
    Bool,
    String,
    Arrow(Rc<Type>, Rc<Type>),
}

impl Type {
    pub fn fresh() -> Rc<Self> {
        Rc::new(Type::Unknown(Id::new()))
    }

    pub fn contains_unknown(&self) -> bool {
        match self {
            Type::Unknown(_) => true,
            Type::Unit => false,
            Type::Int => false,
            Type::Bool => false,
            Type::String => false,
            Type::Arrow(t1, t2) => t1.contains_unknown() || t2.contains_unknown(),
        }
    }

    pub fn of_binop(opcode: &BinOpcode) -> Rc<Self> {
        match opcode {
            BinOpcode::Add | BinOpcode::Subtract | BinOpcode::Multiply | BinOpcode::Divide => {
                Rc::new(Type::Int)
            }
            BinOpcode::Equals | BinOpcode::LessThan | BinOpcode::GreaterThan => Rc::new(Type::Bool),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Id {
    pub id: usize,
}

impl Id {
    pub fn new() -> Self {
        static ID_COUNTER: std::sync::atomic::AtomicUsize = AtomicUsize::new(1);
        let id = ID_COUNTER.fetch_add(1, Ordering::Relaxed);
        Self { id }
    }
}
