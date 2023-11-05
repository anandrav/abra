use crate::eval_tree;
use crate::eval_tree::EffectCode;
use crate::statics;
use debug_print::debug_print;
use once_cell::sync::Lazy;
use std::rc::Rc;
use strum::IntoEnumIterator;
use strum_macros::EnumIter;

pub trait EffectTrait {
    fn enumerate() -> Vec<Self>
    where
        Self: Sized;

    fn type_signature(&self) -> (Vec<statics::TypeMonomorphized>, statics::TypeMonomorphized);

    fn function_name(&self) -> String;
}

#[derive(Debug, Clone)]
pub enum Input {
    Unit,
    // Cin(String),
}

#[derive(Debug, Clone, PartialEq, Eq, EnumIter)]
pub enum Effect {
    // TODO rename to DefaultEffects
    PrintString,
    // ReadLn,
}

impl EffectTrait for Effect {
    fn enumerate() -> Vec<Self> {
        Effect::iter().collect()
    }

    fn type_signature(&self) -> (Vec<statics::TypeMonomorphized>, statics::TypeMonomorphized) {
        match self {
            // print_string: string -> void
            Effect::PrintString => (
                vec![statics::TypeMonomorphized::String],
                statics::TypeMonomorphized::Unit,
            ),
        }
    }

    fn function_name(&self) -> String {
        match self {
            Effect::PrintString => String::from("print_string"),
        }
    }
}

static EFFECT_LIST: Lazy<Vec<Effect>> = Lazy::new(|| Effect::enumerate());

pub fn handle_effect_example(
    effect_code: EffectCode,
    args: Vec<Rc<eval_tree::Expr>>,
    output: &mut String,
) -> Input {
    let effect = &EFFECT_LIST[effect_code as usize];
    match effect {
        Effect::PrintString => match &*args[0] {
            eval_tree::Expr::Str(string) => {
                output.push_str(string);
                // output.push('\n');
                debug_print!("{}", string);
                Input::Unit
            }
            _ => panic!("wrong arguments for {:#?} effect", effect),
        },
        // Effect::ReadLn => Input::Cin(String::from("this is input")),
    }
}
