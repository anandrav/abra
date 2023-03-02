use std::{fmt, rc::Rc};

use crate::{ast, operators::BinOpcode};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Unknown(Prov),
    Unit,
    Int,
    Bool,
    String,
    Arrow(Rc<Type>, Rc<Type>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Prov {
    Node(ast::Id),
    MALeft(ast::Id),
    MARight(ast::Id),
}

impl Type {
    // pub fn fresh() -> Rc<Self> {
    //     Rc::new(Type::Unknown(Id::new()))
    // }

    // pub fn matched_arrow(id: ast::Id) -> Rc<Self> {
    //     Rc::new(Type::Arrow(
    //         Type::Unknown(id.clone()).into(),
    //         Type::Unknown(id).into(),
    //     ))
    // }

    // pub fn matched_arrow_n(tys: Vec<Rc<Type>>) -> Rc<Type> {
    //     if tys.len() == 0 {
    //         unreachable!()
    //     } else if tys.len() == 1 {
    //         tys[0].clone()
    //     } else {
    //         Rc::new(Type::Arrow(
    //             tys[0].clone(),
    //             Type::matched_arrow_n(tys[1..].to_vec()),
    //         ))
    //     }
    // }

    // pub fn is_unknown(&self) -> bool {
    //     matches!(self, Type::Unknown(_))
    // }

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

pub fn types_of_binop(opcode: &BinOpcode) -> Vec<Rc<Type>> {
    match opcode {
        BinOpcode::Add | BinOpcode::Subtract | BinOpcode::Multiply | BinOpcode::Divide => {
            vec![Rc::new(Type::Int), Rc::new(Type::Int), Rc::new(Type::Int)]
        }
        BinOpcode::Equals | BinOpcode::LessThan | BinOpcode::GreaterThan => {
            vec![Rc::new(Type::Int), Rc::new(Type::Int), Rc::new(Type::Bool)]
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Unknown(id) => write!(f, "?"),
            Type::Unit => write!(f, "unit"),
            Type::Int => write!(f, "int"),
            Type::Bool => write!(f, "bool"),
            Type::String => write!(f, "string"),
            Type::Arrow(t1, t2) => write!(f, "{} -> {}", t1, t2),
        }
    }
}

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub struct Id {
//     pub id: usize,
// }

// impl Id {
//     pub fn new() -> Self {
//         static ID_COUNTER: std::sync::atomic::AtomicUsize = AtomicUsize::new(1);
//         let id = ID_COUNTER.fetch_add(1, Ordering::Relaxed);
//         Self { id }
//     }
// }
