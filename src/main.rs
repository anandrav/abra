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

println("The first 20 fibonacci numbers are:")
foreach(range(1, 20), n -> println(fibonacci(n)))
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

const _FUNC_ANNOT: &str = r#"
let add: (int, int) -> int = (x, y) -> x + y

add(1, 2)
"#;

const _SCRATCH: &str = r#"let list = [1, 2, 3, 4, 5, 6]
print("numbers: ")
println(list)

let list = map(list, x -> x * x * x)
print("squared: ")
println(list)

let list = filter(list, x -> x mod 2 = 0)
print("only even: ")
println(list)

let list = ["The", "Abra", "Programming", "Language"]
let s = concat(list, " ~ ")
println(newline & s)

"#;

const _INTERFACES: &str = r#"
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
let hack = equals((), ())
let hack = equals(1, 1)
let hack = equals(true, true)
let hack = equals("hello", "hello")
let hack = equals(cons(1, nil), cons(1, nil))

interface ToString {
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

println("2 + 2 = 4?")
println(equals(2 + 2,4))
println("true = false?")
println(equals(true, false))
println("hello = hello?")
println(equals("hello", "hello"))
"#;

const PRELUDE: &str = r#"
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
let hack = equals((), ())
let hack = equals(1, 1)
let hack = equals(true, true)
let hack = equals("hello", "hello")
let hack = [1, 2, 3, 4]
let hack = equals(cons(true, nil), cons(false, nil))

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

let foreach(xs: list<'a>, f: 'a -> 'b) -> void =
    match xs
        nil -> ()
        cons (~head, ~tail) -> {
            f(head)
            foreach(tail, f)
        }

let filter(xs: list<'a>, f: 'a -> bool) -> list<'a> =
    match xs
        nil -> nil
        cons (~head, ~tail) -> 
            if f(head) cons(head, filter(tail, f)) else filter(tail, f)

let hack = [1, 2, 3, 4]

"#;

impl Default for MyApp {
    fn default() -> Self {
        Self {
            text: String::from(_SCRATCH),
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
                            // let source = &self.text;
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
