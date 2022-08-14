use eval_tree;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Cout(String);
#[derive(Debug, Clone)]
pub struct Cin(String);

#[derive(Debug, Clone)]
pub enum Input {
    Unit,
    Cin(String),
}

#[derive(Debug, Clone)]
pub enum Effect {
    Print,
    Read,
}

pub fn handle_effect(effect: &Effect, args: &Vec<Rc<eval_tree::Expr>>) -> Input {
    match effect {
        Effect::Print => match &*args[0] {
            eval_tree::Expr::Str(string) => {
                println!("{}", string);
                Input::Unit
            }
            _ => panic!("wrong arguments for {:#?} effect", effect),
        },
        Effect::Read => Input::Cin(String::from("this is input")),
    }
}
