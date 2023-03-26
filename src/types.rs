use std::{fmt, rc::Rc};

use crate::{ast, operators::BinOpcode};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SType {
    pub typekind: STypeKind,
    pub prov: Prov,
}

impl SType {
    pub fn from_node(node: Rc<impl ast::Node>) -> Rc<SType> {
        SType {
            typekind: STypeKind::Unknown,
            prov: Prov::Node(node.id()),
        }
        .into()
    }

    pub fn make_unknown(prov: Prov) -> Rc<SType> {
        SType {
            typekind: STypeKind::Unknown,
            prov,
        }
        .into()
    }

    pub fn make_unit(prov: Prov) -> Rc<SType> {
        SType {
            typekind: STypeKind::Unit,
            prov,
        }
        .into()
    }

    pub fn make_int(prov: Prov) -> Rc<SType> {
        SType {
            typekind: STypeKind::Int,
            prov,
        }
        .into()
    }

    pub fn make_bool(prov: Prov) -> Rc<SType> {
        SType {
            typekind: STypeKind::Bool,
            prov,
        }
        .into()
    }

    pub fn make_string(prov: Prov) -> Rc<SType> {
        SType {
            typekind: STypeKind::String,
            prov,
        }
        .into()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum STypeKind {
    Unknown,
    Unit,
    Int,
    Bool,
    String,
    Arrow(Vec<Rc<SType>>, Rc<SType>),
}

impl STypeKind {
    // pub fn is_primitive(&self) -> bool {
    //     match self {
    //         STypeKind::Unknown => false,
    //         STypeKind::Unit => true,
    //         STypeKind::Int => true,
    //         STypeKind::Bool => true,
    //         STypeKind::String => true,
    //         STypeKind::Arrow(_, _) => false,
    //     }
    // }
}

impl SType {
    // pub fn make_arrow(args: Vec<Rc<SType>>, out: Rc<SType>, id: ast::Id) -> Rc<SType> {
    //     args.into_iter().rev().fold(out, |acc, arg| {
    //         Rc::new(SType {
    //             typekind: STypeKind::Arrow(vec![arg], acc),
    //             prov: Prov::Node(id),
    //         })
    //     })
    // }
    pub fn make_arrow(args: Vec<Rc<SType>>, out: Rc<SType>, id: ast::Id) -> Rc<SType> {
        Rc::new(SType {
            typekind: STypeKind::Arrow(args, out),
            prov: Prov::Node(id),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Prov {
    Node(ast::Id),
    Builtin(String), // a builtin function or constant, which doesn't exist in the AST

    // INVARIANT: the provenances in FuncArg and FuncOut are either Node or Builtin.
    FuncArg(Box<Prov>, u8), // u8 represents the index of the argument
    FuncOut(Box<Prov>),     // u8 represents how many arguments before this output
                            // TODO remove the u8 from FuncOut because no more currying
}

impl SType {
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

pub fn types_of_binop(
    opcode: &BinOpcode,
    node_left: Rc<ast::Expr>,
    node_right: Rc<ast::Expr>,
    node_op: Rc<ast::Expr>,
) -> (Rc<SType>, Rc<SType>, Rc<SType>) {
    match opcode {
        BinOpcode::Add | BinOpcode::Subtract | BinOpcode::Multiply | BinOpcode::Divide => (
            SType::make_int(Prov::Node(node_left.id)),
            SType::make_int(Prov::Node(node_right.id)),
            SType::make_int(Prov::Node(node_op.id)),
        ),
        BinOpcode::Equals | BinOpcode::LessThan | BinOpcode::GreaterThan => (
            SType::make_int(Prov::Node(node_left.id)),
            SType::make_int(Prov::Node(node_right.id)),
            SType::make_bool(Prov::Node(node_op.id)),
        ),
    }
}

impl fmt::Display for SType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.typekind {
            STypeKind::Unknown => write!(f, "?"),
            STypeKind::Unit => write!(f, "unit"),
            STypeKind::Int => write!(f, "int"),
            STypeKind::Bool => write!(f, "bool"),
            STypeKind::String => write!(f, "string"),
            STypeKind::Arrow(t1, t2) => {
                write!(f, "(")?;
                for t in t1 {
                    write!(f, "{}, ", t)?;
                }
                write!(f, ") -> {}", t2)
            }
        }
    }
}
