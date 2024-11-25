// Rust addon API

use crate::vm::Vm;

#[repr(C)]
pub enum Type {
    Unit,
    Int,
    Float,
    Bool,
    String,
    Function(Vec<Type>, Box<Type>),
    Tuple(Vec<Type>),
    Nominal(Nominal, Vec<Type>),
}

#[repr(C)]
pub enum Nominal {
    Array,
}

#[repr(C)]
pub struct AddonDesc {
    pub name: &'static str,
    pub funcs: &'static [FuncDesc],
}

#[repr(C)]
pub struct FuncDesc {
    pub name: &'static str,
    pub arg_types: &'static [Type],
    pub ret_type: Type,
    pub func: fn(&mut Vm),
}
