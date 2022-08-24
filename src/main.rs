#[macro_use]
extern crate lalrpop_util;
extern crate abra;
extern crate eframe;
extern crate pest;
extern crate pest_derive;
extern crate regex;

mod operators;
mod parse_tree;
mod token_tree;
mod types;
use eframe::egui;

fn main() {
    let tt = token_tree::TokenTree::from("2 + 3");
    // dbg!(tt);
    println!("{}", tt.to_string());

    let options = eframe::NativeOptions::default();
    eframe::run_native(
        "My egui App",
        options,
        Box::new(|_cc| Box::new(MyApp::default())),
    );
}

struct MyApp {
    text: String,
}

impl Default for MyApp {
    fn default() -> Self {
        Self {
            text: "2 + 3;".to_owned(),
        }
    }
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        self.text = token_tree::fix(&mut self.text);
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.heading("Abra Editor");
            ui.text_edit_multiline(&mut self.text);
        });
    }
}
