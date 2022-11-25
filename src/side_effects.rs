use debug_print::debug_println;
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
    StringOfInt,
    // ReadLn,
}

pub fn handle_effect(
    effect: &Effect,
    args: &Vec<Rc<eval_tree::Expr>>,
    output: &mut String,
) -> Input {
    match effect {
        Effect::Print => match &*args[0] {
            eval_tree::Expr::Str(string) => {
                output.push_str(string);
                output.push('\n');
                debug_println!("{}", string);
                Input::Unit
            }
            _ => panic!("wrong arguments for {:#?} effect", effect),
        },
        Effect::StringOfInt => match &*args[0] {
            eval_tree::Expr::Int(n) => Input::Cin(n.to_string()),
            _ => panic!("wrong arguments for {:#?} effect", effect),
        },
        // Effect::ReadLn => Input::Cin(String::from("this is input")),
    }
}
