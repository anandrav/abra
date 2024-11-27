// Rust addon API

use crate::vm::Vm;

// #[repr(C)]
// pub struct AddonDesc {
//     pub name: &'static str,
//     pub funcs: Array<FuncDesc>,
// }

// #[repr(C)]
// pub struct FuncDesc {
//     pub name: &'static str,
//     // pub arg_types: Array<Type>,
//     // pub ret_type: Type,
//     pub func: fn(&mut Vm),
// }

// #[repr(C)]
// pub enum Type {
//     Unit,
//     Int,
//     Float,
//     Bool,
//     String,
//     Function { args: Array<Type>, ret: *const Type },
//     Tuple(Array<Type>),
//     Nominal(Nominal, Array<Type>),
// }

// #[repr(C)]
// pub struct Array<T> {
//     pub ptr: *const T,
//     pub len: usize,
// }

// #[repr(C)]
// pub enum Nominal {
//     Array,
// }
