use crate::environment::EvalEnv;
use crate::operators::BinOpcode;

use crate::statics::TypeMonomorphized;
use crate::EffectCode;

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

pub(crate) type Identifier = String;

#[derive(Debug, PartialEq)]
pub enum Expr {
    Var(Identifier),
    VarOverloaded(Identifier, TypeMonomorphized),
    Unit,
    Int(i64),
    Float(f64),
    Str(String),
    Bool(bool),
    Tuple(Vec<Rc<Expr>>),
    Struct(String, Rc<RefCell<HashMap<String, Rc<Expr>>>>),
    FieldAccess(Rc<Expr>, Identifier),
    IndexAccess(Rc<Expr>, Rc<Expr>),
    TaggedVariant(Identifier, Rc<Expr>),
    Array(Rc<RefCell<Vec<Rc<Expr>>>>),
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    Let(Rc<Pat>, Rc<Expr>, Rc<Expr>),
    Set(Rc<PlaceExpr>, Rc<Expr>, Rc<Expr>),
    Func(Vec<Identifier>, Rc<Expr>, Option<EvalEnv>),
    FuncAp(Rc<Expr>, Vec<Rc<Expr>>, Option<EvalEnv>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    WhileLoop(Rc<Expr>, Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Match(Rc<Expr>, Vec<MatchArm>),
    EffectAp(EffectCode, Vec<Rc<Expr>>),
    BuiltinAp(Builtin, Vec<Rc<Expr>>),
    ConsumedEffect,
}

impl Expr {
    pub fn get_int(&self) -> i64 {
        match self {
            Expr::Int(i) => *i,
            _ => panic!("not an int"),
        }
    }
    pub fn get_float(&self) -> f64 {
        match self {
            Expr::Float(f) => *f,
            _ => panic!("not a float"),
        }
    }
    pub fn get_string(&self) -> String {
        match self {
            Expr::Str(s) => s.clone(),
            _ => panic!("not a string"),
        }
    }
    pub fn get_tuple(&self) -> Vec<Rc<Expr>> {
        match self {
            Expr::Tuple(elems) => elems.clone(),
            _ => panic!("not a tuple"),
        }
    }
}

impl From<()> for Expr {
    fn from(_: ()) -> Self {
        Expr::Unit
    }
}
impl From<i64> for Expr {
    fn from(i: i64) -> Self {
        Expr::Int(i)
    }
}
impl From<f64> for Expr {
    fn from(f: f64) -> Self {
        Expr::Float(f)
    }
}
impl From<&str> for Expr {
    fn from(s: &str) -> Self {
        Expr::Str(s.to_owned())
    }
}

impl Eq for Expr {}

pub(crate) type MatchArm = (Rc<Pat>, Rc<Expr>);

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
    LessThanInt,
    PowInt,
    AddFloat,
    MinusFloat,
    MultiplyFloat,
    DivideFloat,
    PowFloat,
    SqrtFloat,
    LessThanFloat,
    Append,
    Len,
    Pop,
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
            Struct(name, fields) => {
                write!(f, "{name}{{")?;
                for (i, (name, value)) in fields.borrow().iter().enumerate() {
                    write!(f, "{}: {}", name, value)?;
                    if i != fields.borrow().len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "}}")
            }
            TaggedVariant(tag, data) => write!(f, "variant[{tag}], {data}"),
            Array(elements) => {
                let elements = elements.borrow();
                write!(f, "[ ")?;
                for (i, element) in elements.iter().enumerate() {
                    write!(f, "{}", element)?;
                    if i != elements.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, " ]")
            }
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
    Int(i64),
    Float(f32),
    Str(String),
    Bool(bool),
    Var(String),
    TaggedVariant(Identifier, Option<Rc<Pat>>),
    Tuple(Vec<Rc<Pat>>),
}

#[derive(Debug, PartialEq)]
pub enum PlaceExpr {
    Var(String),
    FieldAccess(Rc<Expr>, String),
    IndexAccess(Rc<Expr>, Rc<Expr>),
}

impl Eq for Pat {}

pub(crate) fn is_val(expr: &Rc<Expr>) -> bool {
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
        Struct(_, fields) => fields.borrow().values().all(is_val),
        FieldAccess(_, _) => false,
        IndexAccess(_, _) => false,
        TaggedVariant(_, data) => is_val(data),
        Array(exprs) => exprs.borrow().iter().all(is_val),
        BinOp(_, _, _) => false,
        Let(_, _, _) => false,
        Set(_, _, _) => false,
        FuncAp(_, _, _) => false,
        If(_, _, _) => false,
        WhileLoop(_, _, _, _) => false,
        Match(_, _) => false,
        EffectAp(_, _) => false,
        BuiltinAp(_, _) => false,
        ConsumedEffect => false,
    }
}
