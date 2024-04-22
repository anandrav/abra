use crate::eval_tree;
use crate::eval_tree::EffectCode;
use crate::statics;
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
pub enum DefaultEffects {
    PrintString,
    Read,
}

impl EffectTrait for DefaultEffects {
    fn enumerate() -> Vec<Self> {
        DefaultEffects::iter().collect()
    }

    fn type_signature(&self) -> (Vec<statics::TypeMonomorphized>, statics::TypeMonomorphized) {
        match self {
            // print_string: string -> void
            DefaultEffects::PrintString => (
                vec![statics::TypeMonomorphized::String],
                statics::TypeMonomorphized::Unit,
            ),
            // read: void -> string
            DefaultEffects::Read => (vec![], statics::TypeMonomorphized::String),
        }
    }

    fn function_name(&self) -> String {
        match self {
            DefaultEffects::PrintString => String::from("print_string"),
            DefaultEffects::Read => String::from("read"),
        }
    }
}

pub static DEFAULT_EFFECT_LIST: Lazy<Vec<DefaultEffects>> = Lazy::new(DefaultEffects::enumerate);

pub fn default_effect_handler(
    effect_code: EffectCode,
    args: Vec<Rc<eval_tree::Expr>>,
) -> Rc<eval_tree::Expr> {
    let effect = &DEFAULT_EFFECT_LIST[effect_code as usize];
    match effect {
        DefaultEffects::PrintString => match &*args[0] {
            eval_tree::Expr::Str(string) => {
                print!("{}", string);
                eval_tree::Expr::from(()).into()
            }
            _ => panic!("wrong arguments for {:#?} effect", effect),
        },
        DefaultEffects::Read => {
            let mut input = String::new();
            std::io::stdin().read_line(&mut input).unwrap();
            eval_tree::Expr::from(input.trim()).into()
        }
    }
}
