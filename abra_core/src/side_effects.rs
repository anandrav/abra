#[derive(Debug, Clone)]
pub struct Cout(String);
#[derive(Debug, Clone)]
pub struct Cin(String);

// #[derive(Debug)]
// pub enum Output {
//     Cout(Cout),
// }

#[derive(Debug, Clone)]
pub enum Input {
    Cin(String),
}

#[derive(Debug, Clone)]
pub enum Effect {
    Print(Cout),
    Read,
}

use self::Effect::*;

pub fn handle_effect(effect: &Effect) -> Option<Input> {
    match effect {
        Print(Cout(string)) => {
            println!("{}", string);
            None
        }
        Read => Some(Input::Cin(String::from("this is input"))),
    }
}
