use std::{cell::RefCell, collections::HashMap, rc::Rc};

use environment::Environment;
pub use eval_tree::EffectCode;
pub use side_effects::EffectTrait;

pub mod ast;
pub mod environment;
pub mod eval_tree;
pub mod interpreter;
mod operators;
pub mod side_effects;
pub mod statics;
pub mod translate;

use interpreter::{Interpreter, OverloadedFuncMap};

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

pub fn compile<Effect: EffectTrait>(source_files: Vec<SourceFile>) -> Result<Runtime, String> {
    let mut filename_to_source = HashMap::new();
    let mut filenames = Vec::new();
    for source_file in &source_files {
        filenames.push(source_file.name.clone());
        filename_to_source.insert(source_file.name.clone(), source_file.contents.clone());
    }
    let sources = ast::Sources {
        filename_to_source,
        files: filenames,
    };

    let toplevels = ast::parse_or_err(&source_files)?;

    let mut node_map = ast::NodeMap::new();
    for parse_tree in &toplevels {
        ast::initialize_node_map(&mut node_map, &(parse_tree.clone() as Rc<dyn ast::Node>));
    }

    let mut inference_ctx = statics::InferenceContext::new();
    let tyctx = statics::make_new_gamma();
    for parse_tree in &toplevels {
        statics::gather_definitions_toplevel::<Effect>(
            &mut inference_ctx,
            tyctx.clone(),
            parse_tree.clone(),
        );
    }
    for parse_tree in &toplevels {
        statics::generate_constraints_toplevel(
            tyctx.clone(),
            parse_tree.clone(),
            &mut inference_ctx,
        );
    }

    statics::result_of_constraint_solving(&mut inference_ctx, tyctx.clone(), &node_map, &sources)?;

    statics::result_of_additional_analysis(&mut inference_ctx, &toplevels, &node_map, &sources)?;

    let env: Rc<RefCell<Environment>> = Rc::new(RefCell::new(Environment::new(None)));
    let (eval_tree, overloaded_func_map) =
        translate::translate(&inference_ctx, tyctx, &node_map, &toplevels, env.clone());
    interpreter::add_builtins_and_variants::<Effect>(env.clone(), &inference_ctx);
    Ok(Runtime {
        toplevel_eval_tree: eval_tree,
        toplevel_env: env,
        overloaded_func_map,
    })
}

pub fn run(source: &str) -> Result<(Rc<eval_tree::Expr>, Runtime), String> {
    run_with_handler::<side_effects::DefaultEffects>(
        source,
        Box::new(side_effects::default_effect_handler),
    )
}

pub type EffectHandler<'b> =
    Box<dyn FnMut(eval_tree::EffectCode, Vec<Rc<eval_tree::Expr>>) -> Rc<eval_tree::Expr> + 'b>;

pub fn run_with_handler<Effect: EffectTrait>(
    source: &str,
    mut handler: EffectHandler,
) -> Result<(Rc<eval_tree::Expr>, Runtime), String> {
    let source_file = SourceFile {
        name: "main.abra".to_owned(),
        contents: source.to_owned(),
    };
    let prelude = SourceFile {
        name: "prelude.abra".to_owned(),
        contents: _PRELUDE.to_string(),
    };
    let source_files = vec![prelude, source_file];
    let runtime = compile::<Effect>(source_files)?;
    let mut interpreter = runtime.toplevel_interpreter();
    let mut effect_result = None;
    loop {
        // TODO instead of 10000, need an option for infinite steps
        let status = interpreter.run(10000, effect_result.take());
        match status {
            interpreter::InterpreterStatus::Error(msg) => {
                return Err(msg);
            }
            interpreter::InterpreterStatus::Finished => {
                return Ok((interpreter.get_val().unwrap(), runtime));
            }
            interpreter::InterpreterStatus::OutOfSteps => {}
            interpreter::InterpreterStatus::Effect(code, args) => {
                effect_result = Some(handler(code, args));
            }
        }
    }
}

pub struct Runtime {
    toplevel_eval_tree: Rc<eval_tree::Expr>,
    toplevel_env: Rc<RefCell<Environment>>,
    overloaded_func_map: OverloadedFuncMap,
}

impl Runtime {
    pub fn toplevel_interpreter(&self) -> Interpreter {
        Interpreter::new(
            self.overloaded_func_map.clone(),
            self.toplevel_eval_tree.clone(),
            self.toplevel_env.clone(),
        )
    }

    pub fn func_interpreter(&self, func_name: &str, args: Vec<Rc<eval_tree::Expr>>) -> Interpreter {
        let func = self
            .toplevel_env
            .borrow()
            .lookup(&func_name.to_string())
            .unwrap();
        let func_ap = eval_tree::Expr::FuncAp(func, args, None);
        Interpreter::new(
            self.overloaded_func_map.clone(),
            Rc::new(func_ap),
            self.toplevel_env.clone(),
        )
    }

    pub fn make_int(&self, i: i64) -> Rc<eval_tree::Expr> {
        Rc::new(eval_tree::Expr::Int(i))
    }

    pub fn make_bool(&self, b: bool) -> Rc<eval_tree::Expr> {
        Rc::new(eval_tree::Expr::Bool(b))
    }

    pub fn make_tuple(&self, elems: Vec<Rc<eval_tree::Expr>>) -> Rc<eval_tree::Expr> {
        Rc::new(eval_tree::Expr::Tuple(elems))
    }
}

pub const _PRELUDE: &str = r#"
func not(b: bool) = if b false else true

interface Num {
    add: (self, self) -> self
    minus: (self, self) -> self
    multiply: (self, self) -> self
    divide: (self, self) -> self
    pow: (self, self) -> self
    less_than: (self, self) -> bool
    less_than_or_equal: (self, self) -> bool
    greater_than: (self, self) -> bool
    greater_than_or_equal: (self, self) -> bool
}
implement Num for int {
    func add(a, b) = add_int(a, b)
    func minus(a, b) = minus_int(a, b)
    func multiply(a, b) = multiply_int(a, b)
    func divide(a, b) = divide_int(a, b)
    func pow(a, b) = pow_int(a, b)
    func less_than(a, b) = less_than_int(a, b)
    func less_than_or_equal(a, b) = (a < b) or (a = b)
    func greater_than(a, b) = not(a < b) and not(a = b)
    func greater_than_or_equal(a, b) = not(a < b)
}
implement Num for float {
    func add(a, b) = add_float(a, b)
    func minus(a, b) = minus_float(a, b)
    func multiply(a, b) = multiply_float(a, b)
    func divide(a, b) = divide_float(a, b)
    func pow(a, b) = pow_float(a, b)
    func less_than(a, b) = less_than_float(a, b)
    func less_than_or_equal(a, b) = a < b
    func greater_than(a, b) = b < a
    func greater_than_or_equal(a, b) = b < a
}

type list<'a> = nil | cons of ('a, list<'a>)

interface Equals {
    equals: (self, self) -> bool
}
implement Equals for void {
    func equals(a, b) = true
}
implement Equals for int {
    func equals(a, b) = equals_int(a, b)
}
implement Equals for float {
    func equals(a, b) = false
}
implement Equals for bool {
    func equals(a, b) {
        if a and b {
            true
        } else if a or b {
            false
        } else {
            true
        }
    }
}
implement Equals for string {
    func equals(a, b) = equals_string(a, b)
}
implement Equals for list<'a Equals> {
    func equals(a, b) {
        match (a, b) {
            (nil, nil) -> true
            (cons (~x, ~xs), cons (~y, ~ys)) -> {
                equals(x, y) and equals(xs, ys)
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
        "[ " & helper(xs) & " ]"
    }
}
func print(x: 'b ToString) { print_string(to_string(x)) }
func println(x: 'b ToString) {
    print_string(to_string(x))
    print_string(newline)
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

func max(a: float, b: float) -> float { if a > b a else b }
func min(a: float, b: float) -> float { if a < b a else b }
func clamp(lo: float, hi: float, x: float) -> float { max(lo, min(hi, x)) }
func abs(x: float) -> float { if x < 0.0 (0.0 - x) else x }
func sqrt(x: float) -> float { sqrt_float(x) }

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
