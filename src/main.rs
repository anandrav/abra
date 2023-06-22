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

use std::rc::Rc;

use debug_print::debug_println;

use eframe::egui;

use crate::egui::Color32;
use interpreter::Interpreter;

use crate::statics::make_new_gamma;

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

const _LIST: &str = r#"type list<'a> = nil | cons ('a, list<'a>)

let my_list = cons(1, nil)

match my_list
    nil -> print("empty list")
    cons (~head, ~tail) -> print(int_to_string(head))

"#;

const _OPTION: &str = r#"type maybe = none | some 'a

let n = some(3)

match n
    none -> print("no int")
    some ~n -> print(n)

"#;

const _TYPE_FUNCTION: &str = r#"type pair<'a> = ('a, 'a)

let npair: pair<int> = (1, 2)

let bpair: pair<bool> = (true, false)

"#;

const _FIB: &str = r#"let fibonacci(n) = {
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

let n = 10

println("The first " & to_string(n) & " fibonacci numbers are:")
for_range((0,n), i -> println(fibonacci(i)))
println("done!")
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

// let map(l: list<'a>, f: 'a -> 'b) = {
// 	match l
// 		nil -> nil
// 		cons (~head, ~tail) -> cons(f(head), map(tail, f))
// }

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

// const _INTERFACES: &str = r#"interface ToString {
//     to_string: self -> string
// }
// implement ToString for string {
// 	let to_string(s) = s
// }
// implement ToString for int {
// 	let to_string(n) = int_to_string(n)
// }

// print_string(to_string("123"))
// "#;

const _INTERFACES: &str = r#"interface ToString {
    to_string: self -> string
}
implement ToString for string {
	let to_string(s) = s
}
implement ToString for int {
	let to_string(n) = int_to_string(n)
}
implement ToString for bool {
	let to_string(b) = if b "true" else "false"
}
type list<'a> = nil | cons ('a, list<'a>)
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

let map(xs: list<'a>, f: 'a -> 'b) =
    match xs
        nil -> nil
        cons (~head, ~tail) -> cons(f(head), map(tail, f))

let filter(xs: list<'a>, f: 'a -> bool) =
    match xs
        nil -> nil
        cons (~head, ~tail) -> 
            if f(head) cons(head, filter(tail, f)) else filter(tail, f)

println("hello world")
println(123)
println(true)
println(false)
let numbers = cons(1, cons(2, cons(3, cons(4, cons(5, nil)))))
println(numbers)
let numbers = map(numbers, x -> x * x)
println(numbers)
"#;

const PRELUDE: &str = r#"interface ToString {
    to_string: self -> string
}
implement ToString for string {
	let to_string(s) = s
}
implement ToString for int {
	let to_string(n) = int_to_string(n)
}
implement ToString for bool {
	let to_string(b) = if b "true" else "false"
}
type list<'a> = nil | cons ('a, list<'a>)
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

let map(xs: list<'a>, f: 'a -> 'b) =
    match xs
        nil -> nil
        cons (~head, ~tail) -> cons(f(head), map(tail, f))

let filter(xs: list<'a>, f: 'a -> bool) =
    match xs
        nil -> nil
        cons (~head, ~tail) -> 
            if f(head) cons(head, filter(tail, f)) else filter(tail, f)
"#;

impl Default for MyApp {
    fn default() -> Self {
        Self {
            text: String::from(_FIB),
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
            let steps = if cfg!(debug_assertions) { 1 } else { 1000 };
            let mut more_output = String::new();
            let effect_handler =
                |effect, args| side_effects::handle_effect(effect, args, &mut more_output);
            if let Some(interpreter) = &mut self.interpreter {
                interpreter.run(effect_handler, steps);
                self.output.push_str(&more_output);
                if interpreter.is_finished() {
                    self.output += &format!(
                        "\nLast line evaluated to: {}",
                        interpreter.get_val().unwrap()
                    );
                    self.interpreter = None;
                } else {
                    ui.ctx().request_repaint();
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
                                if ui.code_editor(&mut self.text).changed() {};
                            });
                        if ui
                            .add(egui::Button::new("Run code").fill(Color32::LIGHT_GREEN))
                            .clicked()
                        {
                            self.interpreter = None;
                            self.output.clear();
                            let source = PRELUDE.to_owned() + &self.text;
                            match ast::parse_or_err(&source) {
                                Ok(parse_tree) => {
                                    debug_println!("successfully parsed.");
                                    let mut node_map = ast::NodeMap::new();
                                    ast::initialize_node_map(
                                        &mut node_map,
                                        &(parse_tree.clone() as Rc<dyn ast::Node>),
                                    );
                                    debug_println!("initialized node map.");
                                    let mut inference_ctx = statics::InferenceContext::new();
                                    let tyctx = make_new_gamma();
                                    statics::gather_definitions_toplevel(
                                        &mut inference_ctx,
                                        tyctx.clone(),
                                        parse_tree.clone(),
                                    );
                                    let tyctx = statics::generate_constraints_toplevel(
                                        tyctx,
                                        parse_tree.clone(),
                                        &mut inference_ctx,
                                    );
                                    debug_println!("generated constraints.");
                                    let result = statics::result_of_constraint_solving(
                                        &inference_ctx,
                                        tyctx.clone(),
                                        &node_map,
                                        &source,
                                    );
                                    match result {
                                        Ok(_) => {
                                            debug_println!("solved constraints.");
                                            let (eval_tree, overloaded_func_map) =
                                                translate::translate(
                                                    &inference_ctx,
                                                    tyctx.clone(),
                                                    &node_map,
                                                    parse_tree,
                                                );
                                            self.interpreter = Some(Interpreter::new(
                                                &inference_ctx,
                                                tyctx,
                                                overloaded_func_map,
                                                eval_tree,
                                            ));
                                            debug_println!("initialized new interpreter.");
                                        }
                                        Err(err) => {
                                            debug_println!("constraint solving failed.");
                                            self.output = err;
                                        }
                                    }
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
