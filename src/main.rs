extern crate abra;
extern crate debug_print;
extern crate disjoint_sets;
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
mod statics;
mod translate;
mod types;

use debug_print::debug_println;

use eframe::egui;

use egui::Color32;
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
        Box::new(|_cc| Box::<MyApp>::default()),
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
    wasm_bindgen_futures::spawn_local(async {
        eframe::start_web(
            "the_canvas_id", // hardcode it
            options,
            Box::new(|_cc| Box::<MyApp>::default()),
        )
        .await
        .expect("failed to start eframe");
    });
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
                r#"let x = 2;
let y = 4;
x + y"#,
            ),
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
            if let Some(interpreter) = &self.interpreter {
                if interpreter.is_finished() {
                    self.interpreter = None;
                } else {
                    ui.ctx().request_repaint();
                }
            }
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
                                    // self.text =
                                    debug_println!("was changed");
                                };
                            });
                        if ui
                            .add(egui::Button::new("Run code").fill(Color32::LIGHT_GREEN))
                            .clicked()
                        {
                            self.interpreter = None;
                            self.output.clear();
                            let text_with_braces = "{".to_owned() + &self.text + "}";
                            match ast::parse_or_err(&text_with_braces) {
                                Ok(parse_tree) => {
                                    let mut constraints = Vec::new();
                                    statics::generate_constraints_expr(
                                        statics::TyCtx::empty(),
                                        statics::Mode::Syn,
                                        parse_tree.clone(),
                                        &mut constraints,
                                    );
                                    println!("Constraints: {:#?}", constraints);
                                    statics::solve_constraints(constraints);
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
