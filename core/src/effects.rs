use crate::statics;
use crate::vm::Vm;

use crate::statics::Monotype as Type;

#[derive(Debug, Clone)]
pub struct Effect {
    pub name: &'static str, // TODO make this &'static str
    pub type_signature: (Vec<statics::Monotype>, statics::Monotype),
    pub func: fn(&mut Vm) -> (),
}

pub fn default_effects() -> Vec<Effect> {
    vec![
        Effect {
            name: "print_string",
            type_signature: (vec![Type::String], Type::Unit),
            func: |vm: &mut Vm| {
                let s = vm.top().get_string(vm);
                print!("{}", s);
                vm.pop();
                vm.push_nil();
            },
        },
        Effect {
            name: "readline",
            type_signature: (vec![], Type::String),
            func: |vm: &mut Vm| {
                let mut input = String::new();
                std::io::stdin().read_line(&mut input).unwrap();
                vm.push_str(&input[0..input.len() - 1]);
            },
        },
    ]
}

pub type EffectCode = u16;
