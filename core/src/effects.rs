use crate::statics;
use strum::FromRepr;
use strum::VariantArray;
use strum_macros::EnumIter;

#[derive(Debug, Clone)]
pub struct EffectStruct {
    pub name: String,
    pub type_signature: (Vec<statics::Monotype>, statics::Monotype),
}

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
            DefaultEffects::Read => String::from("readline"),
        }
    }
}

pub type EffectCode = u16;
