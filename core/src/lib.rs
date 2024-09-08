use std::{collections::HashMap, rc::Rc};

use side_effects::DefaultEffects;
pub use side_effects::EffectCode;
pub use side_effects::EffectStruct;

mod assembly;
pub mod ast;
mod builtin;
pub mod environment;

pub mod side_effects;
pub mod statics;
mod translate_bytecode;
pub mod vm;

use translate_bytecode::CompiledProgram;
use translate_bytecode::Translator;

pub fn abra_hello_world() {
    println!("Hello, world!");
}

pub struct SourceFile {
    pub name: String,
    pub contents: String,
}

pub fn source_files_single(src: &str) -> Vec<SourceFile> {
    vec![
        SourceFile {
            name: "prelude.abra".to_owned(),
            contents: _PRELUDE.to_owned(),
        },
        SourceFile {
            name: "test.abra".to_owned(),
            contents: src.to_owned(),
        },
    ]
}

pub fn compile_bytecode(
    source_files: Vec<SourceFile>,
    effects: Vec<EffectStruct>,
) -> Result<CompiledProgram, String> {
    let mut filename_to_source = HashMap::new();
    let mut filenames = Vec::new();
    for source_file in &source_files {
        filenames.push(source_file.name.clone());
        filename_to_source.insert(source_file.name.clone(), source_file.contents.clone());
    }
    let sources = ast::Sources { filename_to_source };

    let toplevels = ast::parse_or_err(&source_files)?;

    let mut node_map = ast::NodeMap::new();
    for parse_tree in &toplevels {
        ast::initialize_node_map(&mut node_map, &(parse_tree.clone() as Rc<dyn ast::Node>));
    }

    let mut inference_ctx = statics::InferenceContext::new(effects.clone());
    let tyctx = statics::Gamma::empty();
    for parse_tree in &toplevels {
        statics::gather_definitions_toplevel(&mut inference_ctx, tyctx.clone(), parse_tree.clone());
    }
    for parse_tree in &toplevels {
        statics::generate_constraints_toplevel(
            tyctx.clone(),
            parse_tree.clone(),
            &mut inference_ctx,
        );
    }

    statics::result_of_constraint_solving(&mut inference_ctx, &node_map, &sources)?;

    statics::result_of_additional_analysis(&mut inference_ctx, &toplevels, &node_map, &sources)?;

    let translator = Translator::new(inference_ctx, node_map, sources, toplevels, effects);
    Ok(translator.translate())
}

// TODO: prelude should only contain builtin operations like adding ints and conversions to strings, etc.
// it should not contain standard library functions like map, fold, etc.
pub const _PRELUDE: &str = r#"
func not(b: bool) = if b false else true

interface Num {
    add: (self, self) -> self
    subtract: (self, self) -> self
    multiply: (self, self) -> self
    divide: (self, self) -> self
    power: (self, self) -> self
    less_than: (self, self) -> bool
    less_than_or_equal: (self, self) -> bool
    greater_than: (self, self) -> bool
    greater_than_or_equal: (self, self) -> bool
}

implement Num for int {
    func add(a, b) = add_int(a, b)
    func subtract(a, b) = subtract_int(a, b)
    func multiply(a, b) = multiply_int(a, b)
    func divide(a, b) = divide_int(a, b)
    func power(a, b) = power_int(a, b)
    func less_than(a, b) = less_than_int(a, b)
    func less_than_or_equal(a, b) = (a < b) or (a = b)
    func greater_than(a, b) = not(a < b) and not(a = b)
    func greater_than_or_equal(a, b) = not(a < b)
}

implement Num for float {
    func add(a, b) = add_float(a, b)
    func subtract(a, b) = subtract_float(a, b)
    func multiply(a, b) = multiply_float(a, b)
    func divide(a, b) = divide_float(a, b)
    func power(a, b) = power_float(a, b)
    func less_than(a, b) = less_than_float(a, b)
    func less_than_or_equal(a, b) = a < b
    func greater_than(a, b) = b < a
    func greater_than_or_equal(a, b) = b < a
}

type list<'a> = nil | cons of ('a, list<'a>)

interface Equal {
    equal: (self, self) -> bool
}
implement Equal for void {
    func equal(a, b) = true
}
implement Equal for int {
    func equal(a, b) = equal_int(a, b)
}
implement Equal for float {
    func equal(a, b) = false
}
implement Equal for bool {
    func equal(a, b) {
        if a and b {
            true
        } else if a or b {
            false
        } else {
            true
        }
    }
}
implement Equal for string {
    func equal(a, b) = equal_string(a, b)
}

implement Equal for list<'a Equal> {
    func equal(a, b) {
        match (a, b) {
            (nil, nil) -> true
            (cons (~x, ~xs), cons (~y, ~ys)) -> {
                equal(x, y) and equal(xs, ys)
            }
            _ -> false
        }
    }
}

interface ToString {
    to_string: self -> string
}
implement ToString for string {
	func to_string(s) = s
}
implement ToString for void {
	func to_string(s) = "()"
}
implement ToString for int {
	func to_string(n) = int_to_string(n)
}
implement ToString for bool {
	func to_string(b) = if b "true" else "false"
}
implement ToString for float {
    func to_string(f) = float_to_string(f)
}
implement ToString for ('a ToString, 'b ToString) {
    func to_string(p) {
        let (a, b) = p
        "(" & to_string(a) & ", " & to_string(b) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString) {
    func to_string(p) {
        let (a, b, c) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString) {
    func to_string(p) {
        let (a, b, c, d) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString) {
    func to_string(p) {
        let (a, b, c, d, e) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString) {
    func to_string(p) {
        let (a, b, c, d, e, f) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString) {
    func to_string(p) {
        let (a, b, c, d, e, f, g) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ", " & to_string(g) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString) {
    func to_string(p) {
        let (a, b, c, d, e, f, g, h) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ", " & to_string(g) & ", " & to_string(h) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString) {
    func to_string(p) {
        let (a, b, c, d, e, f, g, h, i) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ", " & to_string(g) & ", " & to_string(h) & ", " & to_string(i) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString, 'j ToString) {
    func to_string(p) {
        let (a, b, c, d, e, f, g, h, i, j) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ", " & to_string(g) & ", " & to_string(h) & ", " & to_string(i) & ", " & to_string(j) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString, 'j ToString, 'k ToString) {
    func to_string(p) {
        let (a, b, c, d, e, f, g, h, i, j, k) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ", " & to_string(g) & ", " & to_string(h) & ", " & to_string(i) & ", " & to_string(j) & ", " & to_string(k) & ")"
    }
}
implement ToString for ('a ToString, 'b ToString, 'c ToString, 'd ToString, 'e ToString, 'f ToString, 'g ToString, 'h ToString, 'i ToString, 'j ToString, 'k ToString, 'l ToString) {
    func to_string(p) {
        let (a, b, c, d, e, f, g, h, i, j, k, l) = p
        "(" & to_string(a) & ", " & to_string(b) & ", " & to_string(c) & ", " & to_string(d) & ", " & to_string(e) & ", " & to_string(f) & ", " & to_string(g) & ", " & to_string(h) & ", " & to_string(i) & ", " & to_string(j) & ", " & to_string(k) & ", " & to_string(l) & ")"
    }
}

implement ToString for list<'a ToString> {
    func to_string(xs) {
        func helper(xs) {
            match xs {
                nil -> ""
                cons (~x, nil) -> {
                    to_string(x)
                }
                cons (~x, ~xs) -> {
                    to_string(x) & ", " & helper(xs)
                }
            }
        }
        "[| " & helper(xs) & " |]"
    }
}

implement ToString for array<'a ToString> {
    func to_string(arr) {
        func helper(arr, idx) {
            let l = array_length(arr)
            if idx = l {
                ""
            } else if idx = l - 1 {
                to_string(arr[idx])
            } else {
                to_string(arr[idx]) & ", " & helper(arr, idx + 1)
            }
        }
        "[ " & helper(arr, 0) & " ]"
    }
}

func len(arr: array<'a>) -> int { 
    array_length(arr)
}

func print(x: 'b ToString) { print_string(to_string(x)) }
func println(x: 'b ToString) {
    print_string(to_string(x) & newline)
}

func range(lo: int, hi: int) {
    if lo > hi
        nil
    else
        cons(lo, range(lo + 1, hi))
}

func fold(xs: list<'b>, f: ('a, 'b) -> 'a, acc: 'a) -> 'a {
    match xs {
        nil -> acc
        cons (~head, ~tail) -> fold(tail, f, f(acc, head))
    }
}

func sum(xs: list<int>) -> int { fold(xs, (a, b) -> a + b, 0) }
func sumf(xs: list<float>) -> float { fold(xs, (a, b) -> a + b, 0.0) }

func concat(xs: list<string>, sep: string) -> string {
    match xs {
        nil -> ""
        cons (~head, cons(~last, nil)) -> {
            head & sep & last
        }
        cons (~head, ~tail) -> {
            head & sep & concat(tail, sep)
        }
    }
}

func map(xs: list<'a>, f: 'a -> 'b) -> list<'b> {
    match xs {
        nil -> nil
        cons (~head, ~tail) -> cons(f(head), map(tail, f))
    }
}

func for_each(xs: list<'a>, f: 'a -> 'b) -> void {
    match xs {
        nil -> ()
        cons (~head, ~tail) -> {
            f(head)
            for_each(tail, f)
        }
    }
}

func filter(xs: list<'a>, f: 'a -> bool) -> list<'a> {
    match xs {
        nil -> nil
        cons (~head, ~tail) ->
            if f(head) cons(head, filter(tail, f)) else filter(tail, f)
    }
}

func reverse(xs: list<'c>) -> list<'c> {
    fold(xs, (acc, head) -> cons(head, acc), nil)
}

"#;
