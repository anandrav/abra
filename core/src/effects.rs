use crate::statics;
pub use strum::FromRepr;
pub use strum::VariantArray;

pub use crate::statics::Monotype as Type;

#[derive(Debug, Clone)]
pub struct EffectDesc {
    pub name: &'static str,
    pub type_signature: (Vec<statics::Monotype>, statics::Monotype),
}

pub trait EffectTrait: VariantArray {
    fn enumerate() -> Vec<EffectDesc>
    where
        Self: Sized,
    {
        Self::VARIANTS
            .iter()
            .map(|effect| {
                let effect = effect.to_owned();
                EffectDesc {
                    name: effect.function_name(),
                    type_signature: effect.type_signature(),
                }
            })
            .collect()
    }

    fn type_signature(&self) -> (Vec<statics::Monotype>, statics::Monotype);

    fn function_name(&self) -> &'static str;
}

#[derive(Debug, Clone, PartialEq, Eq, VariantArray, FromRepr)]
pub enum DefaultEffects {
    PrintString,
    Read,
}

impl EffectTrait for DefaultEffects {
    fn type_signature(&self) -> (Vec<statics::Monotype>, statics::Monotype) {
        match self {
            // print_string: string -> void
            DefaultEffects::PrintString => {
                (vec![statics::Monotype::String], statics::Monotype::Unit)
            }
            // readline: void -> string
            DefaultEffects::Read => (vec![], statics::Monotype::String),
        }
    }

    fn function_name(&self) -> &'static str {
        match self {
            DefaultEffects::PrintString => "print_string",
            DefaultEffects::Read => "readline",
        }
    }
}

pub type EffectCode = u16;
