use crate::eval_tree;
use debug_print::debug_println;
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Effect {
    Print,
    IntToString,
    AppendStrings,
    // ReadLn,
}

pub fn handle_effect(effect: Effect, args: Vec<Rc<eval_tree::Expr>>, output: &mut String) -> Input {
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
        Effect::IntToString => match &*args[0] {
            eval_tree::Expr::Int(n) => Input::Cin(n.to_string()),
            _ => panic!("wrong arguments ({:#?}) for {:#?} effect", args[0], effect),
        },
        Effect::AppendStrings => match (&*args[0], &*args[1]) {
            (eval_tree::Expr::Str(s1), eval_tree::Expr::Str(s2)) => Input::Cin({
                let mut s1 = s1.clone();
                s1.push_str(s2);
                s1
            }),
            _ => panic!("wrong arguments ({:#?}) for {:#?} effect", args[0], effect),
        },
        // Effect::ReadLn => Input::Cin(String::from("this is input")),
    }
}
