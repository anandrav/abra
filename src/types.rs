use std::{fmt, rc::Rc};

use crate::{ast, operators::BinOpcode};

// TODO: use this for Types instead, because all Types have a provenance.
// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub struct Type {
//     pub typekind: TypeKind,
//     pub prov: Prov,
// }

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub enum TypeKind {
//     Unknown(Prov),
//     Unit,
//     Int,
//     Bool,
//     String,
//     Arrow(Rc<Type>, Rc<Type>),
// }

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Unknown(Prov),
    Unit,
    Int,
    Bool,
    String,
    Arrow(Rc<Type>, Rc<Type>),
}

impl Type {
    pub fn make_arrow(args: Vec<Rc<Type>>, out: Rc<Type>) -> Rc<Type> {
        args.into_iter()
            .rev()
            .fold(out, |acc, arg| Rc::new(Type::Arrow(arg, acc)))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Prov {
    Node(ast::Id),
    FuncArg(ast::Id, u8), // u8 represents the index of the argument
    FuncOut(ast::Id, u8), // u8 represents how many arguments before this output
}

impl Type {
    // pub fn contains_unknown(&self) -> bool {
    //     match self {
    //         Type::Unknown(_) => true,
    //         Type::Unit => false,
    //         Type::Int => false,
    //         Type::Bool => false,
    //         Type::String => false,
    //         Type::Arrow(t1, t2) => t1.contains_unknown() || t2.contains_unknown(),
    //     }
    // }
}

pub fn types_of_binop(opcode: &BinOpcode) -> (Rc<Type>, Rc<Type>, Rc<Type>) {
    match opcode {
        BinOpcode::Add | BinOpcode::Subtract | BinOpcode::Multiply | BinOpcode::Divide => {
            (Rc::new(Type::Int), Rc::new(Type::Int), Rc::new(Type::Int))
        }
        BinOpcode::Equals | BinOpcode::LessThan | BinOpcode::GreaterThan => {
            (Rc::new(Type::Int), Rc::new(Type::Int), Rc::new(Type::Bool))
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Unknown(_id) => write!(f, "?"),
            Type::Unit => write!(f, "unit"),
            Type::Int => write!(f, "int"),
            Type::Bool => write!(f, "bool"),
            Type::String => write!(f, "string"),
            Type::Arrow(t1, t2) => write!(f, "({} -> {})", t1, t2),
        }
    }
}
