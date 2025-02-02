use std::rc::Rc;

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

pub use ast::FileData;
pub use prelude::PRELUDE;
use translate_bytecode::CompiledProgram;
use translate_bytecode::Translator;

pub fn abra_hello_world() {
    println!("Hello, world!");
}

pub fn source_files_single(src: &str) -> Vec<FileData> {
    vec![
        FileData::new(
            "prelude.abra".to_owned(),
            "prelude.abra".into(),
            PRELUDE.to_owned(),
        ),
        FileData::new("test.abra".to_owned(), "test.abra".into(), src.to_owned()),
    ]
}

pub fn compile_bytecode(
    source_files: Vec<FileData>,
    effects: Vec<EffectDesc>,
) -> Result<CompiledProgram, String> {
    let mut sources = ast::FileDatabase::new();
    for source_file in source_files {
        // TODO: what are we doing here lol
        sources.add(source_file.name, source_file.path, source_file.source);
    }

    let files = parse::parse_or_err(&sources)?;

    let mut node_map = ast::NodeMap::new();
    for parse_tree in &files {
        ast::initialize_node_map(&mut node_map, &(parse_tree.clone() as Rc<dyn ast::Node>));
    }

    let inference_ctx = statics::analyze(&effects, &files, &node_map, &sources)?;

    // TODO: translator should be immutable
    // NOTE: It's only mutable right now because of ty_fits_impl_ty calls ast_type_to_statics_type...
    let mut translator = Translator::new(inference_ctx, node_map, sources, files, effects);
    Ok(translator.translate())
}
