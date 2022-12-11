#[macro_use]
extern crate lalrpop_util;
extern crate abra;
extern crate debug_print;
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
mod translate;
mod types;

use debug_print::debug_println;

use eframe::egui;

use interpreter::Interpreter;

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
    interpreter: Option<Interpreter>,
}

impl Default for MyApp {
    fn default() -> Self {
        Self {
            text: String::from(
                r#"let helper = func(x,y,n) {
    if n == 0 {
        x
    } else {
        helper(y,x+y,n-1)
    }
};

let fibonacci = func(n) {
    helper(0,1,n)
};

print("The first 30 fibonacci numbers are:");
let print_fib = func(n) {
    print(string_of_int(fibonacci(n)))
};
let iter_n = func(i, n, f) {
    if i > n {
        ()
    } else {
        f(i);
        iter_n(i+1, n, f);
    }
};
iter_n(0, 30, print_fib);"#,
            ),
            output: String::default(),
            interpreter: None,
        }
    }
}

/*
game plan:
    - in interpreter.rs, make a struct that contains the interpreter's state and a function for running for a step
    - make the interpreter struct have a function is_finished() (which uses is_val() underneath)
    - add a bool to UI's state that tracks whether the interpreter is running
    - if a print side effect occurred after running, append the string to the console window and make it scroll to the bottom
    - whenever Run code is clicked, reset the interpreter's state and set 'running' to true
*/

fn get_program_output(text: &String) -> Result<String, String> {
    let mut env = interpreter::make_new_environment();
    // add braces to make it a block expression
    let text_with_braces = "{".to_owned() + text + "}";
    let parse_tree = ast::parse(&text_with_braces)?;
    let mut eval_tree = translate::translate_expr(parse_tree.exprkind.clone());
    debug_println!("{:#?}", eval_tree);
    let mut output = String::from("");
    let mut next_input = None;
    output += "=====PROGRAM OUTPUT=====\n\n";
    debug_println!("Expr is: {:#?}", eval_tree);
    let steps = if cfg!(debug_assertions) {
        debug_println!("Debugging enabled");
        1
    } else {
        i32::MAX
    };

    loop {
        let result = interpreter::interpret(eval_tree, env.clone(), steps, &next_input);
        eval_tree = result.expr;
        env = result.new_env;
        next_input = match result.effect {
            None => None,
            Some((effect, args)) => Some(side_effects::handle_effect(effect, args, &mut output)),
        };
        match (&next_input, eval_tree::is_val(&eval_tree)) {
            (None, true) => {
                break;
            }
            _ => {
                debug_println!("Env is: {:#?}", env);
                debug_println!("Expr is: {:#?}", eval_tree)
            }
        };
    }
    output += "\n========================\n";
    output += &format!("Expression evaluated to: {:#?}", eval_tree);
    Ok(output)
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        let width = 570.0;
        egui::CentralPanel::default().show(ctx, |ui| {
            // this is a bad hack. this forces update() to be called as much as possible
            // so that the program can run on the UI thread.
            // I did this because web assembly does not support threads currently
            ui.ctx().request_repaint();
            let steps = if cfg!(debug_assertions) { 1 } else { i32::MAX };
            // sig Fn(&side_effects::Effect, &Vec<Rc<Expr>>) -> side_effects::Input
            let mut output_copy = self.output.clone();
            let effect_handler =
                |effect, args| side_effects::handle_effect(effect, args, &mut output_copy);
            if let Some(interpreter) = &mut self.interpreter {
                interpreter.run(effect_handler, steps);
                self.output = output_copy;
            }

            egui::Window::new("Abra Editor")
                .title_bar(false)
                .anchor(egui::Align2::CENTER_TOP, egui::vec2(0.0, 0.0))
                .scroll2([true, true])
                .default_width(700.0)
                .default_height(1000.0)
                .show(ctx, |ui| {
                    ui.set_width(width);
                    ui.vertical_centered_justified(|ui| {
                        ui.set_width(width);
                        ui.heading("Abra Editor");
                        egui::ScrollArea::vertical()
                            .max_height(400.0)
                            .min_scrolled_height(300.0)
                            .show(ui, |ui| {
                                if ui.code_editor(&mut self.text).changed() {
                                    // self.text =
                                    debug_println!("was changed");
                                };
                            });
                        if ui.button("Run code").clicked() {
                            // self.output = match get_program_output(&self.text) {
                            //     Ok(output) => output,
                            //     Err(error) => error,
                            // };
                            self.interpreter = None;
                            self.output.clear();
                            let text_with_braces = "{".to_owned() + &self.text + "}";
                            match ast::parse(&text_with_braces) {
                                Ok(parse_tree) => {
                                    let eval_tree =
                                        translate::translate_expr(parse_tree.exprkind.clone());
                                    self.interpreter = Some(Interpreter::new(eval_tree));
                                }
                                Err(err) => {
                                    self.output = err;
                                }
                            }
                        }
                        ui.vertical(|ui| {
                            egui::ScrollArea::vertical()
                                .max_height(400.0)
                                .min_scrolled_height(300.0)
                                .show(ui, |ui| {
                                    ui.set_width(width);
                                    ui.monospace(&self.output);
                                });
                        });
                    });
                });
        });
    }
}
