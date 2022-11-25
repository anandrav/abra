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
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, Receiver, Sender};
use std::sync::Arc;
use std::thread::{self, JoinHandle};
use std::time::Duration;

use eframe::egui;

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
    running: Arc<AtomicBool>,
    running_thread: Option<std::thread::JoinHandle<()>>,
    tx: Sender<String>,
    rx: Receiver<String>,
}

impl Default for MyApp {
    fn default() -> Self {
        let (tx, rx) = mpsc::channel::<String>();
        Self {
            text: String::from(
                r#"let fibonacci = func(n) {
    if n == 0 {
        0
    } else {
        if n == 1 {
            1
        } else {
            fibonacci(n-1) + fibonacci(n-2)
        }
    }
};

print("The first 30 fibonacci numbers are:");
let iter_n = func(i, n) {
    if i > n {
        ()
    } else {
        print(string_of_int(fibonacci(i)));
        iter_n(i+1, n);
    }
};
iter_n(0, 30);"#,
            ),
            output: String::default(),
            running: Arc::new(AtomicBool::new(false)),
            running_thread: None,
            tx: tx,
            rx: rx,
        }
    }
}

fn run_program(
    text: &String,
    tx: &Sender<String>,
    ctx: &egui::Context,
    running: Arc<AtomicBool>,
) -> Result<(), String> {
    let mut env = interpreter::make_new_environment();
    // add braces to make it a block expression
    let text_with_braces = "{".to_owned() + text + "}";
    let parse_tree = ast::parse(&text_with_braces)?;
    let mut eval_tree = translate::translate_expr(parse_tree.exprkind.clone());
    debug_println!("{:#?}", eval_tree);
    let mut next_input = None;
    debug_println!("Expr is: {:#?}", eval_tree);
    let steps = if cfg!(debug_assertions) {
        debug_println!("Debugging enabled");
        1
    } else {
        1000000
    };

    loop {
        let still_running = running.load(Ordering::Relaxed);
        if !still_running {
            return Ok(());
        }
        let result = interpreter::interpret(eval_tree, env.clone(), steps, &next_input);
        eval_tree = result.expr;
        env = result.new_env;
        next_input = match result.effect {
            None => None,
            Some((effect, args)) => Some(side_effects::handle_effect(&effect, &args, &tx, &ctx)),
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
    tx.send("========================\n".to_string()).unwrap();
    tx.send(format!("Expression evaluated to: {:#?}", eval_tree))
        .unwrap();
    ctx.request_repaint();
    Ok(())
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        let width = 570.0;

        egui::CentralPanel::default().show(ctx, |_ui| {
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
                                ui.code_editor(&mut self.text);
                            });
                        if ui.button("Run code").clicked() {
                            // stop the old program
                            self.running.swap(false, Ordering::Relaxed);
                            self.running_thread.take().map(JoinHandle::join);
                            self.running_thread = None;
                            self.output.clear();
                            // clear the receiver too
                            let mut iter = self.rx.try_iter();
                            while iter.next().is_some() {}
                            // start new program
                            let text_capture = self.text.clone();
                            let tx = self.tx.clone();
                            let ctx = ctx.clone();
                            self.running.swap(true, Ordering::Relaxed);
                            let running = self.running.clone();
                            self.running_thread = Some(std::thread::spawn(move || {
                                if let Err(err) = run_program(&text_capture, &tx, &ctx, running) {
                                    tx.send(err).unwrap();
                                    ctx.request_repaint();
                                }
                            }));
                        }
                        if let Ok(str) = self.rx.try_recv() {
                            self.output.push_str(&str);
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
