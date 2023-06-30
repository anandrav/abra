use crate::environment::Environment;
use crate::operators::BinOpcode;
use crate::side_effects;
use crate::statics::TypeFullyInstantiated;

use std::cell::RefCell;
use std::rc::Rc;

pub type Identifier = String;

#[derive(Debug, PartialEq)]
pub enum Expr {
    Var(Identifier),
    VarOverloaded(Identifier, TypeFullyInstantiated),
    Unit,
    Int(i32),
    Float(f32),
    Str(String),
    Bool(bool),
    Tuple(Vec<Rc<Expr>>),
    TaggedVariant(Identifier, Rc<Expr>),
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    Let(Rc<Pat>, Rc<Expr>, Rc<Expr>),
    Func(Vec<Identifier>, Rc<Expr>, Option<Rc<RefCell<Environment>>>),
    FuncAp(Rc<Expr>, Vec<Rc<Expr>>, Option<Rc<RefCell<Environment>>>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Match(Rc<Expr>, Vec<MatchArm>),
    EffectAp(side_effects::Effect, Vec<Rc<Expr>>),
    BuiltinAp(Builtin, Vec<Rc<Expr>>),
    ConsumedEffect,
}

impl Eq for Expr {}

pub type MatchArm = (Rc<Pat>, Rc<Expr>);

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum Builtin {
    IntToString,
    FloatToString,
    IntToFloat,
    RoundFloatToInt,
    AppendStrings,
    EqualsInt,
    EqualsString,
    AddInt,
    MinusInt,
    MultiplyInt,
    DivideInt,
    PowInt,
    AddFloat,
    MinusFloat,
    MultiplyFloat,
    DivideFloat,
    PowFloat,
}

// only works for values right now:
impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use self::Expr::*;
        match self {
            Var(ident) => write!(f, "{}", ident),
            Unit => write!(f, "no result"),
            Int(i) => write!(f, "{}", i),
            Float(fl) => write!(f, "{}", fl),
            Str(s) => write!(f, "{}", s),
            Bool(b) => write!(f, "{}", b),
            Tuple(elements) => {
                write!(f, "(")?;
                for (i, element) in elements.iter().enumerate() {
                    write!(f, "{}", element)?;
                    if i != elements.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            TaggedVariant(tag, data) => write!(f, "variant[{tag}], {data}"),
            Func(param, _body, _) => write!(f, "fn {:?} -> (body)", param),
            EffectAp(_eff, _) => write!(f, "built-in effect"),
            _ => panic!("only implemented for values, {:?}", self),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Pat {
    Wildcard,
    Unit,
    Int(i32),
    Float(f32),
    Str(String),
    Bool(bool),
    Var(String),
    TaggedVariant(Identifier, Option<Rc<Pat>>),
    Tuple(Vec<Rc<Pat>>),
}

impl Eq for Pat {}

pub fn is_val(expr: &Rc<Expr>) -> bool {
    use self::Expr::*;
    match expr.as_ref() {
        Var(_) => false,
        VarOverloaded(_, _) => false,
        Unit => true,
        Int(_) => true,
        Float(_) => true,
        Str(_) => true,
        Bool(_) => true,
        Func(_, _, _) => true,
        Tuple(elements) => elements.iter().all(is_val),
        TaggedVariant(_, data) => is_val(data),
        BinOp(_, _, _) => false,
        Let(_, _, _) => false,
        FuncAp(_, _, _) => false,
        If(_, _, _) => false,
        Match(_, _) => false,
        EffectAp(_, _) => false,
        BuiltinAp(_, _) => false,
        ConsumedEffect => false,
    }
}
