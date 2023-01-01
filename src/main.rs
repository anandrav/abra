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
        "Abra Editor",
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
    prev_text: String,
    output: String,
    interpreter: Option<Interpreter>,
}

impl Default for MyApp {
    fn default() -> Self {
        let blah = String::from(
            r#"let fibonacci = func(n) {
    if n == 0 {
        0
    } else {
        if n == 1 {
            1
        } else {
            fibonacci(n - 1) + fibonacci(n - 2)
        }
    }
};
let run_fibonacci = func(n) {
    print(string_of_int(fibonacci(n)))
};
let from_i_to_n = func(i, n, f) {
    if i > n {
        ()
    } else {
        f(i);
        from_i_to_n(i + 1, n, f);
    }
};

print("The first 30 fibonacci numbers are:");
from_i_to_n(0, 30, run_fibonacci);"#,
        );
        Self {
            text: blah.clone(),
            prev_text: blah,
            output: String::default(),
            interpreter: None,
        }
    }
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        let width = 570.0;
        egui::CentralPanel::default().show(ctx, |ui| {
            // HACK. this forces update() to be called as much as possible
            // so that the program can run on the UI thread.
            // I did this because web assembly does not support threads currently
            ui.ctx().request_repaint();
            let steps = if cfg!(debug_assertions) { 1 } else { 1000 };
            let mut output_copy = self.output.clone();
            let effect_handler =
                |effect, args| side_effects::handle_effect(effect, args, &mut output_copy);
            if let Some(interpreter) = &mut self.interpreter {
                if !interpreter.is_finished() {
                    interpreter.run(effect_handler, steps);
                    self.output = output_copy;
                    if interpreter.is_finished() {
                        self.output +=
                            &format!("Evaluated to: {:?}", interpreter.get_val().unwrap());
                    }
                }
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
                                    if let Some(fixed) = ast::fix(&self.text, 15) {
                                        self.text = fixed;
                                        debug_println!("valid syntax {:#?}", self.text);
                                        self.prev_text = self.text.clone();
                                    } else {
                                        debug_println!("invalid syntax");
                                        self.text = self.prev_text.clone();
                                    }
                                };
                            });
                        if ui.button("Run code").clicked() {
                            self.interpreter = None;
                            self.output.clear();
                            match ast::parse_or_err(&self.text) {
                                Ok(parse_tree) => {
                                    let eval_tree =
                                        translate::translate_expr(parse_tree.exprkind.clone());
                                    let interpreter = Interpreter::new(eval_tree);
                                    if interpreter.is_finished() {
                                        self.output += &format!(
                                            "Evaluated to: {:?}",
                                            interpreter.get_val().unwrap()
                                        );
                                    }
                                    self.interpreter = Some(interpreter);
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
