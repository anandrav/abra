#[macro_use]
extern crate lalrpop_util;
extern crate abra;
extern crate eframe;
extern crate pest;
extern crate pest_derive;
extern crate regex;

mod ast;
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
        Color32, Frame, Label, RichText,
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
                r#"{

let helper = func(x,y,n) {
    if n == 0 {
        x
    } else {
        helper(y,x+y,n-1)
    }
};

let fibonacci = func(n) {
    helper(0,1,n)
};

print("The first 10 fibonacci numbers are:");
let print_fib = func(n) {
    print(string_of_int(fibonacci(n)))
};
let iter_n = func(i, n, f) {
    if i > n {
        ()
    } else {{
        f(i);
        iter_n(i+1, n, f);
    }}
};
iter_n(0, 10, print_fib);

}"#,
            ),
            output: String::default(),
        }
    }
}

fn get_program_output(text: &String) -> Result<String, String> {
    let mut env = interpreter::make_new_environment();
    let parse_tree = ast::parse(&text)?;
    // let token_tree = token_tree::TokenTree::from(text);
    // let eval_tree = translate::
    let mut eval_tree = translate::translate_expr(parse_tree.exprkind.clone());
    println!("{:#?}", eval_tree);
    let mut output = String::from("");
    let mut next_input = None;
    output += "=====PROGRAM OUTPUT=====\n\n";
    println!("Expr is: {:#?}", eval_tree);
    loop {
        let result = interpreter::interpret(eval_tree, env.clone(), 1, &next_input);
        eval_tree = result.expr;
        env = result.new_env;
        next_input = match result.effect {
            None => None,
            Some((effect, args)) => Some(side_effects::handle_effect(&effect, &args, &mut output)),
        };
        match (&next_input, eval_tree::is_val(&eval_tree)) {
            (None, true) => {
                break;
            }
            _ => {
                println!("Env is: {:#?}", env);
                println!("Expr is: {:#?}", eval_tree)
            }
        };
    }
    output += "\n========================\n";
    output += &format!("Expression evaluated to: {:#?}", eval_tree);
    Ok(output)
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        egui::CentralPanel::default().show(ctx, |ui| {
            egui::Window::new("Abra Editor")
                .title_bar(false)
                .anchor(egui::Align2::CENTER_TOP, egui::vec2(0.0, 0.0))
                .scroll2([true, true])
                .default_width(700.0)
                .default_height(1000.0)
                .show(ctx, |ui| {
                    ui.set_width(570.0);
                    ui.vertical_centered_justified(|ui| {
                        ui.heading("Abra Editor");
                        ui.code_editor(&mut self.text);
                        if ui.button("Run code").clicked() {
                            self.output = match get_program_output(&self.text) {
                                Ok(output) => output,
                                Err(error) => error,
                            }
                        }
                        ui.vertical(|ui| {
                            ui.monospace(&self.output);
                        });
                    });
                });
        });
    }
}
