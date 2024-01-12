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
    Read,
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
            // read: void -> string
            Effect::Read => (vec![], statics::TypeMonomorphized::String),
        }
    }

    fn function_name(&self) -> String {
        match self {
            Effect::PrintString => String::from("print_string"),
            Effect::Read => String::from("read"),
        }
    }
}

static EFFECT_LIST: Lazy<Vec<Effect>> = Lazy::new(Effect::enumerate);

pub fn handle_effect_example(
    effect_code: EffectCode,
    args: Vec<Rc<eval_tree::Expr>>,
    output: &mut String,
) -> Rc<eval_tree::Expr> {
    let effect = &EFFECT_LIST[effect_code as usize];
    match effect {
        Effect::PrintString => match &*args[0] {
            eval_tree::Expr::Str(string) => {
                output.push_str(string);
                debug_print!("{}", string);
                eval_tree::Expr::from(()).into()
            }
            _ => panic!("wrong arguments for {:#?} effect", effect),
        },
        Effect::Read => {
            let mut input = String::new();
            std::io::stdin().read_line(&mut input).unwrap();
            eval_tree::Expr::from(input.trim()).into()
        }
    }
}
