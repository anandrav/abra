use debug_print::debug_println;
use eframe::egui;
use eval_tree;
use std::rc::Rc;
use std::sync::mpsc::Sender;

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
    tx: &Sender<String>,
    ctx: &egui::Context,
) -> Input {
    match effect {
        Effect::Print => match &*args[0] {
            eval_tree::Expr::Str(string) => {
                let mut with_newline = string.clone();
                with_newline.push('\n');
                tx.send(with_newline).unwrap();
                ctx.request_repaint();
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
