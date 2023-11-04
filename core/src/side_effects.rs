use crate::eval_tree;
use crate::statics;
use debug_print::debug_print;
use std::rc::Rc;
use strum::IntoEnumIterator;
use strum_macros::EnumIter;

trait EffectTrait {
    type PerformCtx;

    fn enumerate() -> Vec<Self>
    where
        Self: Sized;

    fn perform(
        &self,
        ctx: &mut Self::PerformCtx,
        args: Vec<Rc<eval_tree::Expr>>,
    ) -> Rc<eval_tree::Expr>;

    fn type_signature(&self) -> (Vec<statics::TypeMonomorphized>, statics::TypeMonomorphized);

    fn function_name(&self) -> String;
}

#[derive(Debug, Clone)]
pub struct Cout(String);
#[derive(Debug, Clone)]
pub struct Cin(String);

#[derive(Debug, Clone)]
pub enum Input {
    Unit,
    // Cin(String),
}

#[derive(Debug, Clone, PartialEq, Eq, EnumIter)]
pub enum Effect {
    // TODO rename to DefaultEffects
    Print,
    // ReadLn,
}

struct DefaultPerformCtx {
    pub console_output: String,
}

impl EffectTrait for Effect {
    type PerformCtx = DefaultPerformCtx;

    fn enumerate() -> Vec<Self> {
        Effect::iter().collect()
    }

    fn perform(
        &self,
        ctx: &mut Self::PerformCtx,
        args: Vec<Rc<eval_tree::Expr>>,
    ) -> Rc<eval_tree::Expr> {
        match self {
            Effect::Print => match &*args[0] {
                eval_tree::Expr::Str(string) => {
                    ctx.console_output.push_str(string);
                    debug_print!("{}", string);
                    Rc::new(eval_tree::Expr::Unit)
                }
                _ => panic!("wrong arguments for {:#?} effect", self),
            },
        }
    }

    fn type_signature(&self) -> (Vec<statics::TypeMonomorphized>, statics::TypeMonomorphized) {
        match self {
            Effect::Print => (
                vec![statics::TypeMonomorphized::String],
                statics::TypeMonomorphized::Unit,
            ),
        }
    }

    fn function_name(&self) -> String {
        match self {
            Effect::Print => String::from("print"),
        }
    }
}

pub fn handle_effect(effect: Effect, args: Vec<Rc<eval_tree::Expr>>, output: &mut String) -> Input {
    match effect {
        Effect::Print => match &*args[0] {
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
