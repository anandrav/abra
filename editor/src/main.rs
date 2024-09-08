extern crate abra_core;
extern crate debug_print;
extern crate eframe;
extern crate regex;
extern crate syntect;

use std::rc::Rc;

use abra_core::{vm::Vm, SourceFile};

use eframe::egui;
use once_cell::sync::Lazy;

use crate::egui::Color32;

use abra_core::side_effects::{self, DefaultEffects, EffectTrait};

// When compiling natively:
#[cfg(not(target_arch = "wasm32"))]
fn main() {
    // Log to stdout (if you run with `RUST_LOG=debug`).

    tracing_subscriber::fmt::init();

    let options = eframe::NativeOptions::default();
    eframe::run_native(
        "My egui App",
        options,
        Box::new(|_cc| Ok(Box::<MyApp>::default())),
    )
    .expect("Could not launch egui app");
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
        eframe::WebRunner::new()
            .start(
                "the_canvas_id", // hardcode it
                options,
                Box::new(|_cc| Ok(Box::<MyApp>::default())),
            )
            .await
            .expect("failed to start eframe");
    });
}

const _DEMO: &str = r#"type person = {
    name: string,
    color: string
}
let user = person("", "")
println("Enter your name: ")
user.name <- read()
println("Enter you favorite color: ")
user.color <- read()
println(user.name & "'s favorite color is " & user.color)

func fib(n) {
    match n {
        0 -> 0
        1 -> 1
        _ -> fib(n-1) + fib(n-2)
    }
}

let list = range(0,9)
println("numbers: ")
println(list)

let list = map(list, fib)
println("fibonacci: ")
println(list)

let list = map(list, x -> x ^ 3)
println("cubed: ")
println(list)

let list = filter(list, x -> x mod 2 = 1)
println("only odds: ")
println(list)
"#;

struct MyApp {
    text: String,
    readline: bool,
    input: String,
    output: String,
    vm: Option<Vm>,
}

impl Default for MyApp {
    fn default() -> Self {
        Self {
            text: String::from(_DEMO),
            readline: false,
            input: String::default(),
            output: String::default(),
            vm: None,
        }
    }
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        let mut visuals = egui::Visuals::light();
        // let ink = egui::Color32::from_rgb(35, 20, 16);
        visuals.override_text_color = Some(Color32::WHITE);
        let chestnut = egui::Color32::from_rgb(75, 35, 26);
        visuals.window_fill = chestnut;
        let parchment = egui::Color32::from_rgb(252, 245, 229);
        visuals.extreme_bg_color = parchment;
        ctx.set_visuals(visuals);
        let width = 570.0;
        egui::CentralPanel::default().show(ctx, |ui| {
            // HACK. this forces update() to be called as much as possible
            // so that the program can run on the UI thread.
            // I did this because web assembly does not support threads currently
            let steps = 1000;
            if !self.readline {
                if self.vm.is_some() && self.vm.as_ref().unwrap().is_done() {
                    self.vm = None;
                }
                if let Some(vm) = &mut self.vm {
                    vm.run_n_steps(steps);
                    vm.gc();

                    if let Some(pending_effect) = vm.get_pending_effect() {
                        let effect = DefaultEffects::from_repr(pending_effect as usize).unwrap();
                        match effect {
                            abra_core::side_effects::DefaultEffects::PrintString => {
                                let s = vm.top().get_string(&vm);
                                self.output.push_str(&s);
                                vm.pop();
                                vm.push_nil();
                            }
                            abra_core::side_effects::DefaultEffects::Read => {
                                self.readline = true;
                            }
                        }
                        vm.clear_pending_effect();
                    }
                    ui.ctx().request_repaint();
                }
            }

            egui::Window::new("Abra Editor")
                .title_bar(false)
                .anchor(egui::Align2::CENTER_TOP, egui::vec2(0.0, 0.0))
                .scroll([true, true])
                .default_width(700.0)
                .default_height(1000.0)
                .show(ctx, |ui| {
                    ui.set_width(width);
                    ui.vertical_centered_justified(|ui| {
                        ui.label(
                            egui::RichText::new("Abra Editor")
                                .heading()
                                .color(egui::Color32::GOLD),
                        );
                        egui::ScrollArea::vertical()
                            .max_height(500.0)
                            .min_scrolled_height(400.0)
                            .show(ui, |ui| {
                                let mut layouter =
                                    |ui: &egui::Ui, string: &str, _wrap_width: f32| {
                                        let language = "hs";
                                        let highlighter = Highlighter::default();
                                        let layout_job =
                                            highlighter.highlight_impl(string, language).unwrap();
                                        ui.fonts(|f| f.layout_job(layout_job))
                                    };

                                let code_editor = egui::TextEdit::multiline(&mut self.text)
                                    .desired_rows(20)
                                    .code_editor()
                                    .layouter(&mut layouter);
                                ui.add(code_editor);
                            });

                        ui.visuals_mut().override_text_color = Some(Color32::WHITE);
                        let enter_color = if self.readline {
                            Color32::from_rgb(71, 207, 63)
                        } else {
                            Color32::from_rgb(150, 150, 150)
                        };
                        if ui
                            .add(egui::Button::new("Enter").fill(enter_color))
                            .clicked()
                            && self.readline
                        {
                            if let Some(vm) = &mut self.vm {
                                vm.push_str(self.input.trim().into());
                                self.readline = false;
                                self.input.clear();
                            }
                        }

                        ui.visuals_mut().override_text_color = None;
                        ui.add(egui::TextEdit::singleline(&mut self.input));

                        ui.visuals_mut().override_text_color = Some(Color32::WHITE);
                        if ui
                            .add(egui::Button::new("Run Code").fill(Color32::from_rgb(71, 207, 63)))
                            .clicked()
                        {
                            self.vm = None;
                            self.output.clear();
                            self.input.clear();
                            self.readline = false;

                            let mut source_files = Vec::new();
                            source_files.push(SourceFile {
                                name: "prelude.abra".to_string(),
                                contents: abra_core::_PRELUDE.to_string(),
                            });
                            source_files.push(SourceFile {
                                name: "main.abra".to_string(),
                                contents: self.text.clone(),
                            });
                            match abra_core::compile_bytecode(
                                source_files,
                                DefaultEffects::enumerate(),
                            ) {
                                Ok(program) => {
                                    self.vm = Some(Vm::new(program));
                                }
                                Err(err) => {
                                    self.output = err.to_string();
                                }
                            }
                        }

                        ui.visuals_mut().override_text_color = None;
                        if !self.output.is_empty() {
                            ui.visuals_mut().override_text_color = None;
                            egui::ScrollArea::vertical()
                                .id_source("output_scroll_area")
                                .max_height(400.0)
                                .stick_to_bottom(true)
                                .show(ui, |ui| {
                                    let mut output_clone = self.output.clone();
                                    ui.code_editor(&mut output_clone)
                                });
                        }
                    });
                });
        });
    }
}

struct Highlighter {
    ps: syntect::parsing::SyntaxSet,
    ts: syntect::highlighting::ThemeSet,
}

impl Default for Highlighter {
    fn default() -> Self {
        Self {
            ps: syntect::parsing::SyntaxSet::load_defaults_newlines(),
            ts: syntect::highlighting::ThemeSet::load_defaults(),
        }
    }
}

fn as_byte_range(whole: &str, range: &str) -> std::ops::Range<usize> {
    let whole_start = whole.as_ptr() as usize;
    let range_start = range.as_ptr() as usize;
    assert!(whole_start <= range_start);
    assert!(range_start + range.len() <= whole_start + whole.len());
    let offset = range_start - whole_start;
    offset..(offset + range.len())
}

impl Highlighter {
    fn highlight_impl(&self, text: &str, language: &str) -> Option<egui::text::LayoutJob> {
        use syntect::easy::HighlightLines;
        use syntect::highlighting::FontStyle;
        use syntect::util::LinesWithEndings;

        let syntax = self
            .ps
            .find_syntax_by_name(language)
            .or_else(|| self.ps.find_syntax_by_extension(language))?;

        let theme = "InspiredGitHub";
        let mut h = HighlightLines::new(syntax, &self.ts.themes[theme]);

        use egui::text::{LayoutSection, TextFormat};

        let mut job = egui::text::LayoutJob {
            text: text.into(),
            ..Default::default()
        };

        for line in LinesWithEndings::from(text) {
            for (style, range) in h.highlight_line(line, &self.ps).ok()? {
                let fg = style.foreground;
                let text_color = egui::Color32::from_rgb(fg.r, fg.g, fg.b);
                let italics = style.font_style.contains(FontStyle::ITALIC);
                let underline = style.font_style.contains(FontStyle::ITALIC);
                let underline = if underline {
                    egui::Stroke::new(1.0, text_color)
                } else {
                    egui::Stroke::NONE
                };
                job.sections.push(LayoutSection {
                    leading_space: 0.0,
                    byte_range: as_byte_range(text, range),
                    format: TextFormat {
                        font_id: egui::FontId::monospace(12.0),
                        color: text_color,
                        italics,
                        underline,
                        ..Default::default()
                    },
                });
            }
        }

        Some(job)
    }
}
