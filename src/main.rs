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
use std::rc::Rc;

use eframe::{
    egui::{
        self,
        style::{Margin, Spacing},
        Color32, Label, RichText,
    },
    epaint::Vec2,
};

use token_tree::*;

fn main() {
    let tt = TokenTree::from("2 + 3;");
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
    program: Rc<TokenTree>,
    cursor: Cursor,
}

impl Default for MyApp {
    fn default() -> Self {
        Self {
            text: "2 +3 +  83 + 9;".to_owned(),
            program: TokenTree::from("2 +3 +  83 + 9;"),
            cursor: Cursor::Point(Location {
                token: 0,
                tposition: 0,
            }),
        }
    }
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        if ctx.input().key_pressed(egui::Key::ArrowLeft) {
            println!("key left pressed");
            handle_action(Action::MoveLeft, &mut self.program, &mut self.cursor);
        }
        if ctx.input().key_pressed(egui::Key::ArrowRight) {
            println!("key right pressed");
            handle_action(Action::MoveRight, &mut self.program, &mut self.cursor);
        }
        self.text = fix(&mut self.text);
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.heading("Abra Editor");
            // ui.text_edit_multiline(&mut self.text);
            egui::ScrollArea::vertical().show(ui, |ui| {
                ui.horizontal(|ui| {
                    let mut tokens: Vec<Token> = vec![];
                    fn collect_leaves(tt: &Rc<TokenTree>, leaves: &mut Vec<Token>) {
                        match &tt.contents {
                            Contents::Token(t) => leaves.push(t.clone()),
                            Contents::Children(children) => {
                                for c in children.iter() {
                                    collect_leaves(c, leaves)
                                }
                            }
                        }
                    }

                    collect_leaves(&self.program, &mut tokens);

                    match (&self.cursor) {
                        Cursor::Point(Location { token, tposition }) => {
                            let index = token;
                            for i in 0..*index {
                                ui.spacing_mut().item_spacing = Vec2 { x: 0.0, y: 0.0 };
                                ui.label(
                                    RichText::new(tokens[i].to_string())
                                        .monospace()
                                        .color(Color32::WHITE)
                                        .background_color(Color32::DARK_GRAY),
                                );
                            }
                            if tokens[*index].num_points() == 2 {
                                if *tposition != 0 {
                                    ui.spacing_mut().item_spacing = Vec2 { x: 0.0, y: 0.0 };
                                    ui.label(
                                        RichText::new(tokens[*index].to_string())
                                            .monospace()
                                            .color(Color32::WHITE)
                                            .background_color(Color32::DARK_GRAY),
                                    );
                                }
                                ui.spacing_mut().item_spacing = Vec2 { x: 0.0, y: 0.0 };
                                ui.label(
                                    RichText::new("|")
                                        .color(Color32::RED)
                                        .background_color(Color32::DARK_GRAY),
                                );
                                if *tposition == 0 {
                                    ui.spacing_mut().item_spacing = Vec2 { x: 0.0, y: 0.0 };
                                    ui.label(
                                        RichText::new(tokens[*index].to_string())
                                            .monospace()
                                            .color(Color32::WHITE)
                                            .background_color(Color32::DARK_GRAY),
                                    );
                                }
                            } else {
                                let mut first = tokens[*index].to_string();
                                let second = first.split_off(*tposition);
                                println!("{}, {}", first, second);
                                ui.spacing_mut().item_spacing = Vec2 { x: 0.0, y: 0.0 };
                                ui.label(
                                    RichText::new(first.to_string())
                                        .monospace()
                                        .color(Color32::WHITE)
                                        .background_color(Color32::DARK_GRAY),
                                );
                                ui.spacing_mut().item_spacing = Vec2 { x: 0.0, y: 0.0 };
                                ui.label(
                                    RichText::new("|")
                                        .color(Color32::RED)
                                        .background_color(Color32::DARK_GRAY),
                                );
                                ui.spacing_mut().item_spacing = Vec2 { x: 0.0, y: 0.0 };
                                ui.label(
                                    RichText::new(second.to_string())
                                        .monospace()
                                        .color(Color32::WHITE)
                                        .background_color(Color32::DARK_GRAY),
                                );
                            }
                            for i in *index + 1..tokens.len() {
                                ui.spacing_mut().item_spacing = Vec2 { x: 0.0, y: 0.0 };
                                ui.label(
                                    RichText::new(tokens[i].to_string())
                                        .monospace()
                                        .color(Color32::WHITE)
                                        .background_color(Color32::DARK_GRAY),
                                );
                            }
                        }
                        Cursor::Selection { begin, end } => unimplemented!(),
                    }
                });
            });
        });
    }
}
