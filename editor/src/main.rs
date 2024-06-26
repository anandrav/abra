extern crate abra_core;
extern crate debug_print;
extern crate eframe;
extern crate regex;
extern crate syntect;

use std::rc::Rc;

use abra_core::SourceFile;

use eframe::egui;
use once_cell::sync::Lazy;

use crate::egui::Color32;

use abra_core::interpreter::{Interpreter, InterpreterStatus};
use abra_core::side_effects::{self, EffectTrait};

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
                Box::new(|_cc| Box::<MyApp>::default()),
            )
            .await
            .expect("failed to start eframe");
    });
}

const _LIST: &str = r#"type list<'a> = nil | cons of ('a, list<'a>)

let my_list = cons(1, nil)

match my_list
    nil -> print("empty list")
    cons (~head, ~tail) -> print(int_to_string(head))

"#;

const _OPTION: &str = r#"type maybe = none | some of 'a

let n = some(3)

match n
    none -> print("no int")
    some ~n -> print(n)

"#;

const _TYPE_FUNCTION: &str = r#"type pair<'a> = ('a, 'a)

let npair: pair<int> = (1, 2)

let bpair: pair<bool> = (true, false)

"#;

const _OLD_FIB: &str = r#"let fibonacci(n) = {
    match n
        0 -> 0
        1 -> 1
        _ -> fibonacci(n-1) + fibonacci(n-2)
}

type range = (int, int)

let for_range(r: range, f) = {
    let (i, n) = r
    if i < n {
        f(i)
        for_range((i+1, n), f)
    }
}

let print_fibonacci(n) = println(int_to_string(fibonacci(n)))

println("The first 20 fibonacci numbers are:")

for_range((0, 20), print_fibonacci)
"#;

const _FIB: &str = r#"let fibonacci(n) = {
    match n
        0 -> 0
        1 -> 1
        _ -> fibonacci(n-1) + fibonacci(n-2)
}

println("The first 10 fibonacci numbers are:")
for_each(range(0, 9), n -> println(fibonacci(n)))
"#;

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

func fibonacci(n) {
    match n {
        0 -> 0
        1 -> 1
        _ -> fibonacci(n-1) + fibonacci(n-2)
    }
}

let list = range(0,9)
println("numbers: ")
println(list)

let list = map(list, fibonacci)
println("fibonacci: ")
println(list)

let list = map(list, x -> x ^ 3)
println("cubed: ")
println(list)

let list = filter(list, x -> x mod 2 = 1)
println("only odds: ")
println(list)

let list = map(list, x -> to_float(x) * 3.14)
println("times pi: ")
println(list)

print(newline)
print("they add up to: ")
println(sumf(list))
"#;

const _MORE_LIST: &str = r#"type list<'a> = nil | cons ('a, list<'a>)

let numbers = cons(1,nil)
let bools = cons(true, cons(true,nil))

let f(x: list<'a>) = {
	match x
		nil -> print("nil")
		cons (false, _) -> print("false")
		_ -> print("true")
}

f(bools)
"#;

const _SQUARED_LIST: &str = r#"type list<'a> = nil | cons ('a, list<'a>)

let print_list(xs: list<int>) =
	match xs
		nil -> print("")
		cons (~x, ~xs) -> {
			print(int_to_string(x))
			print_list(xs)
		}

let squared_list(xs: list<int>) =
	match xs
		nil -> nil
		cons (~x, ~xs) -> cons(x*x, squared_list(xs))


let my_list = cons(1, cons(2, cons(3, cons(4, cons(5, nil)))))
print("some numbers:")
print_list(my_list)
print("the same numbers, squared:")
print_list(squared_list(my_list))
"#;

const _SWAP: &str = r#"let swap(pair: ('a, 'b)) = {
    let (first, second) = pair
    (second, first)
}

swap((1, true))

swap(("hello", 2))
"#;

const _MORE_OPS: &str = r#"let x = 2 + 2 = 4
let y = true
println(x)
println(y)
println(x and y)
"#;

const _FUNC_ANNOT: &str = r#"
let add: (int, int) -> int = (x, y) -> x + y

add(1, 2)
"#;

const _SCRATCH: &str = r#"
let arr = [ 1, 2, 3, 4 ]
arr[0] <- 6
arr
"#;

const _INTERFACES: &str = r#"
interface Num {
    plus: (self, self) -> self
    minus: (self, self) -> self
    multiply: (self, self) -> self
    divide: (self, self) -> self
    pow: (self, self) -> self
}
implement Num for int {
    let add(a, b) = add_int(a, b)
    let minus(a, b) = minus_int(a, b)
    let multiply(a, b) = multiply_int(a, b)
    let divide(a, b) = divide_int(a, b)
    let pow(a, b) = pow_int(a, b)
}
implement Num for float {
    let add(a, b) = add_float(a, b)
    let minus(a, b) = minus_float(a, b)
    let multiply(a, b) = multiply_float(a, b)
    let divide(a, b) = divide_float(a, b)
    let pow(a, b) = pow_float(a, b)
}

type list<'a> = nil | cons ('a, list<'a>)

interface Equals {
    equals: (self, self) -> bool
}
implement Equals for void {
    let equals(a, b) = true
}
implement Equals for int {
    let equals(a, b) = equals_int(a, b)
}
implement Equals for bool {
    let equals(a, b) =
        if a and b {
            true
        } else if a or b {
            false
        } else {
            true
        }
}
implement Equals for string {
    let equals(a, b) = equals_string(a, b)
}
implement Equals for list<'a Equals> {
    let equals(a, b) = {
        match (a, b)
            (nil, nil) -> true
            (cons (~x, ~xs), cons (~y, ~ys)) -> {
                equals(x, y) and equals(xs, ys)
            }
            _ -> false
    }
}

interface ToString {
    to_string: self -> string
}
implement ToString for string {
	let to_string(s) = s
}
implement ToString for void {
	let to_string(s) = "()"
}
implement ToString for int {
	let to_string(n) = int_to_string(n)
}
implement ToString for bool {
	let to_string(b) = if b "true" else "false"
}
implement ToString for float {
    let to_string(f) = float_to_string(f)
}

implement ToString for list<'a ToString> {
    let to_string(xs) = {
        let helper(xs) =
            match xs
                nil -> ""
                cons (~x, nil) -> {
                    to_string(x)
                }
                cons (~x, ~xs) -> {
                    to_string(x) & ", " & helper(xs)
                }
        "[ " & helper(xs) & " ]"
    }
}
let print(x: 'b ToString) = print_string(to_string(x))
let println(x: 'b ToString) = {
    print_string(to_string(x))
    print_string(newline)
}

let range(lo: int, hi: int) =
    if lo > hi
        nil
    else
        cons(lo, range(lo + 1, hi))

let fold(xs: list<'b>, f: ('a, 'b) -> 'a, acc: 'a) -> 'a =
    match xs
        nil -> acc
        cons (~head, ~tail) -> fold(tail, f, f(acc, head))

let sum(xs: list<int>) -> int = fold(xs, (a, b) -> a + b, 0)

let concat(xs: list<string>, sep: string) -> string =
    match xs
        nil -> ""
        cons (~head, cons(~last, nil)) -> {
            head & sep & last
        }
        cons (~head, ~tail) -> {
            head & sep & concat(tail, sep)
        }

let map(xs: list<'a>, f: 'a -> 'b) -> list<'b> =
    match xs
        nil -> nil
        cons (~head, ~tail) -> cons(f(head), map(tail, f))

let for_each(xs: list<'a>, f: 'a -> 'b) -> void =
    match xs
        nil -> ()
        cons (~head, ~tail) -> {
            f(head)
            for_each(tail, f)
        }

let filter(xs: list<'a>, f: 'a -> bool) -> list<'a> =
    match xs
        nil -> nil
        cons (~head, ~tail) ->
            if f(head) cons(head, filter(tail, f)) else filter(tail, f)

let reverse(xs: list<'c>) -> list<'c> =
    fold(xs, (acc, head) -> cons(head, acc), nil)

println("hello world")
println(123)
println(true)
println(false)
let numbers = cons(1, cons(2, cons(3, cons(4, cons(5, nil)))))
println(numbers)
let numbers = map(numbers, x -> x * x)
println(numbers)

println("2 + 2 = 4?")
println(equals(2 + 2,4))
println("true = false?")
println(equals(true, false))
println("hello = hello?")
println(equals("hello", "hello"))

println(add_float(2.1, 3.60001))
println(minus_float(2.1, 3.60001))
println(multiply_float(2.1, 3.60001))
println(divide_float(2.1, 3.60001))
println(pow_float(2.1, 3.60001))
"#;

struct MyApp {
    text: String,
    readline: bool,
    input: String,
    output: String,
    interpreter: Option<Interpreter>,
    effect_result: Option<Rc<abra_core::eval_tree::Expr>>,
}

impl Default for MyApp {
    fn default() -> Self {
        Self {
            text: String::from(_DEMO),
            readline: false,
            input: String::default(),
            output: String::default(),
            interpreter: None,
            effect_result: None,
        }
    }
}

static EFFECT_LIST: Lazy<Vec<abra_core::side_effects::DefaultEffects>> =
    Lazy::new(abra_core::side_effects::DefaultEffects::enumerate);

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
            let steps = if cfg!(debug_assertions) { 1 } else { 1000 };
            if !self.readline {
                if let Some(interpreter) = &mut self.interpreter {
                    let status = interpreter.run(steps, self.effect_result.take());
                    match status {
                        InterpreterStatus::Error(msg) => {
                            self.output += &msg;
                            self.interpreter = None;
                        }
                        InterpreterStatus::Finished => {
                            self.output += &format!(
                                "\nLast line evaluated to: {}",
                                interpreter.get_val().unwrap()
                            );
                            self.interpreter = None;
                        }
                        InterpreterStatus::OutOfSteps => {
                            ui.ctx().request_repaint();
                        }
                        InterpreterStatus::Effect(code, args) => {
                            let effect = &EFFECT_LIST[code as usize];
                            match effect {
                                abra_core::side_effects::DefaultEffects::PrintString => {
                                    match &*args[0] {
                                        abra_core::eval_tree::Expr::Str(string) => {
                                            self.output.push_str(string);
                                            self.effect_result =
                                                Some(abra_core::eval_tree::Expr::Unit.into());
                                        }
                                        _ => panic!("wrong arguments for {:#?} effect", effect),
                                    }
                                }
                                abra_core::side_effects::DefaultEffects::Read => {
                                    self.readline = true;
                                }
                            }
                            ui.ctx().request_repaint();
                        }
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
                            self.effect_result =
                                Some(abra_core::eval_tree::Expr::from(self.input.trim()).into());
                            self.readline = false;
                            self.input.clear();
                        }

                        ui.visuals_mut().override_text_color = None;
                        ui.add(egui::TextEdit::singleline(&mut self.input));

                        ui.visuals_mut().override_text_color = Some(Color32::WHITE);
                        if ui
                            .add(egui::Button::new("Run Code").fill(Color32::from_rgb(71, 207, 63)))
                            .clicked()
                        {
                            self.interpreter = None;
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
                            match abra_core::compile::<side_effects::DefaultEffects>(source_files) {
                                Ok(runtime) => {
                                    self.interpreter = Some(runtime.toplevel_interpreter());
                                    // let args = vec![runtime.make_int(10)];
                                    // self.interpreter =
                                    //     Some(runtime.func_interpreter("fibonacci", args));
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
