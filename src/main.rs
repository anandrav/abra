#[macro_use]
extern crate lalrpop_util;
extern crate abra;
extern crate eframe;
extern crate pest;
extern crate pest_derive;
extern crate regex;

mod abstract_syntax_tree;
mod environment;
mod eval_tree;
mod interpreter;
mod operators;
mod side_effects;
mod token_tree;
mod translate;
mod types;

use eframe::{
    egui::{
        self,
        style::{Margin, Spacing},
        Color32, Label, RichText,
    },
    epaint::Vec2,
};

use token_tree::*;

// When compiling natively:
#[cfg(not(target_arch = "wasm32"))]
fn main() {
    // Log to stdout (if you run with `RUST_LOG=debug`).
    tracing_subscriber::fmt::init();

    let options = eframe::NativeOptions::default();
    eframe::run_native(
        "My egui App",
        options,
        Box::new(|_cc| Box::new(MyApp::default())),
    );
}

// when compiling to web using trunk.
#[cfg(target_arch = "wasm32")]
fn main() {
    // Make sure panics are logged using `console.error`.
    console_error_panic_hook::set_once();

    // Redirect tracing to console.log and friends:
    tracing_wasm::set_as_global_default();

    let options = eframe::WebOptions::default();
    eframe::start_web(
        "the_canvas_id",
        options,
        Box::new(|_cc| Box::new(MyApp::default())),
    )
    .expect("failed to start eframe");
}

struct MyApp {
    text: String,
    output: String,
}

impl Default for MyApp {
    fn default() -> Self {
        Self {
            text: String::from(
                r#"
1 + 2 * 3 - 4 * 5
"#,
            ),
            output: String::default(),
        }
    }
}

fn get_program_output(text: &String) -> Result<String, String> {
    let mut env = interpreter::make_new_environment();
    let parse_tree = abstract_syntax_tree::parse(&text)?;
    // let token_tree = token_tree::TokenTree::from(text);
    // let eval_tree = translate::
    let mut eval_tree = translate::translate_expr(parse_tree.exprkind.clone());
    let mut result = String::from("");
    let mut next_input = None;
    result += "===============================PROGRAM OUTPUT=================================\n";
    loop {
        let result = interpreter::interpret(eval_tree, env.clone(), 1, &next_input);
        eval_tree = result.expr;
        env = result.new_env;
        next_input = match result.effect {
            None => None,
            Some((effect, args)) => Some(side_effects::handle_effect(&effect, &args)),
        };
        match (&next_input, eval_tree::is_val(&eval_tree)) {
            (None, true) => {
                break;
            }
            _ => {
                // println!("Env is: {:#?}", env);
                // println!("Expr is: {:#?}", eval_tree)
            }
        };
    }
    result += "================================================================================\n";
    result += &format!("Expr evaluated to: {:#?}", eval_tree);
    Ok(result)
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        // self.text = fix(&mut self.text);
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.heading("Abra Editor");
            ui.text_edit_multiline(&mut self.text);
            if ui.button("Run code").clicked() {
                self.output = match get_program_output(&self.text) {
                    Ok(output) => output,
                    Err(error) => error,
                }
            }
            ui.label(&self.output);
        });
    }
}
