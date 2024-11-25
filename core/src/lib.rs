use std::{collections::HashMap, rc::Rc};

pub use effects::EffectCode;
pub use effects::EffectDesc;

pub mod addons;
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
    effects: Vec<EffectDesc>,
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
