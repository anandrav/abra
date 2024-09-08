use crate::statics;
use once_cell::sync::Lazy;
use std::rc::Rc;
use std::sync::OnceLock;
use strum::FromRepr;
use strum::IntoEnumIterator;
use strum::VariantArray;
use strum_macros::EnumIter;

#[derive(Debug, Clone)]
pub struct EffectStruct {
    pub name: String,
    pub type_signature: (Vec<statics::Monotype>, statics::Monotype),
}

// static DEFAULT_EFFECT_LIST2: OnceLock<Vec<EffectStruct>> = OnceLock::new();

// pub fn get_default_effects() -> &'static Vec<EffectStruct> {
//     DEFAULT_EFFECT_LIST2.get_or_init(|| {
//         vec![
//             EffectStruct {
//                 name: String::from("print_string"),
//                 type_signature: (vec![statics::Monotype::String], statics::Monotype::Unit),
//             },
//             EffectStruct {
//                 name: String::from("read"),
//                 type_signature: (vec![], statics::Monotype::String),
//             },
//         ]
//     })
// }

pub trait EffectTrait {
    fn enumerate() -> Vec<EffectStruct>
    where
        Self: Sized;

    fn type_signature(&self) -> (Vec<statics::Monotype>, statics::Monotype);

    fn function_name(&self) -> String;
}

#[derive(Debug, Clone, PartialEq, Eq, EnumIter, VariantArray, FromRepr)]
pub enum DefaultEffects {
    PrintString,
    Read,
}

impl EffectTrait for DefaultEffects {
    fn enumerate() -> Vec<EffectStruct> {
        Self::VARIANTS
            .iter()
            .map(|effect| {
                let effect = effect.to_owned();
                EffectStruct {
                    name: effect.function_name(),
                    type_signature: effect.type_signature(),
                }
            })
            .collect()
    }

    fn type_signature(&self) -> (Vec<statics::Monotype>, statics::Monotype) {
        match self {
            // print_string: string -> void
            DefaultEffects::PrintString => {
                (vec![statics::Monotype::String], statics::Monotype::Unit)
            }
            // read: void -> string
            DefaultEffects::Read => (vec![], statics::Monotype::String),
        }
    }

    fn function_name(&self) -> String {
        match self {
            DefaultEffects::PrintString => String::from("print_string"),
            DefaultEffects::Read => String::from("read"),
        }
    }
}

pub type EffectCode = u16;

pub static DEFAULT_EFFECT_LIST: Lazy<Vec<EffectStruct>> = Lazy::new(DefaultEffects::enumerate);
