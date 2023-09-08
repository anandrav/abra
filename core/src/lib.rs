pub mod ast;
mod environment;
mod eval_tree;
pub mod interpreter;
mod operators;
pub mod side_effects;
pub mod statics;
pub mod translate;

pub fn abra_hello_world() {
    println!("Hello, world!");
}
