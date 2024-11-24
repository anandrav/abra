use std::{collections::HashMap, rc::Rc};

pub use effects::Effect;
pub use effects::EffectCode;

mod assembly;
pub mod ast;
mod builtin;
pub mod effects;
pub mod environment;
mod parse;
pub mod prelude;
pub mod statics;
mod translate_bytecode;
pub mod vm;

pub type Type = statics::Monotype;

use prelude::_PRELUDE;
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
    effects: Vec<Effect>,
) -> Result<CompiledProgram, String> {
    let mut filename_to_source = HashMap::new();
    let mut filenames = Vec::new();
    for source_file in &source_files {
        filenames.push(source_file.name.clone());
        filename_to_source.insert(source_file.name.clone(), source_file.contents.clone());
    }
    let sources = ast::Sources { filename_to_source };

    let files = parse::parse_or_err(&source_files)?;

    let mut node_map = ast::NodeMap::new();
    for parse_tree in &files {
        ast::initialize_node_map(&mut node_map, &(parse_tree.clone() as Rc<dyn ast::Node>));
    }

    let inference_ctx = statics::analyze(&effects, &files, &node_map, &sources)?;

    // TODO: translator should be immutable
    let mut translator = Translator::new(inference_ctx, node_map, sources, files, effects);
    Ok(translator.translate())
}

// used to be part of prelude, but separated because not all programs need it
pub const _STDLIB: &str = r#"
fn range(lo: int, hi: int) {
    if lo > hi
        nil
    else
        cons(lo, range(lo + 1, hi))
}

fn fold(xs: list<'b>, f: ('a, 'b) -> 'a, acc: 'a) -> 'a {
    match xs {
        nil -> acc
        cons (~head, ~tail) -> fold(tail, f, f(acc, head))
    }
}

fn sum(xs: list<int>) -> int { fold(xs, (a, b) -> a + b, 0) }
fn sumf(xs: list<float>) -> float { fold(xs, (a, b) -> a + b, 0.0) }

fn concat(xs: list<string>, sep: string) -> string {
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

fn map(xs: list<'a>, f: 'a -> 'b) -> list<'b> {
    match xs {
        nil -> nil
        cons (~head, ~tail) -> cons(f(head), map(tail, f))
    }
}

fn for_each(xs: list<'a>, f: 'a -> 'b) -> void {
    match xs {
        nil -> ()
        cons (~head, ~tail) -> {
            f(head)
            for_each(tail, f)
        }
    }
}

fn filter(xs: list<'a>, f: 'a -> bool) -> list<'a> {
    match xs {
        nil -> nil
        cons (~head, ~tail) ->
            if f(head) cons(head, filter(tail, f)) else filter(tail, f)
    }
}

fn reverse(xs: list<'c>) -> list<'c> {
    fold(xs, (acc, head) -> cons(head, acc), nil)
}
"#;
