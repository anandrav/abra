use crate::eval_tree;
use debug_print::debug_print;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Cout(String);
#[derive(Debug, Clone)]
pub struct Cin(String);

#[derive(Debug, Clone)]
pub enum Input {
    Unit,
    // Cin(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Effect {
    Print,
    // ReadLn,
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
