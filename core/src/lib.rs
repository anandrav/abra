use std::error::Error;
// use std::error::Error;
use std::path::Path;
use std::path::PathBuf;
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
        FileData::new("test.abra".to_owned(), "test.abra".into(), src.to_owned()),
        FileData::new(
            "prelude.abra".to_owned(),
            "prelude.abra".into(),
            PRELUDE.to_owned(),
        ),
    ]
}

// the first file is the "main" file
pub fn compile_bytecode(
    files: Vec<FileData>,
    effects: Vec<EffectDesc>,
    file_provider: impl FileProvider,
) -> Result<CompiledProgram, String> {
    let mut sources = ast::FileDatabase::new();
    for file_data in files {
        sources.add(file_data);
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

pub trait FileProvider {
    /// Given a path, return the contents of the file as a String,
    /// or an error if the file cannot be found.
    fn search_for_file(&self, path: &Path) -> Result<String, Box<dyn Error>>;
}

#[derive(Default)]
pub struct FileProviderDefault {
    // todo
}

impl FileProviderDefault {
    pub fn new() -> Self {
        Self::default()
    }
}

impl FileProvider for FileProviderDefault {
    fn search_for_file(&self, _path: &Path) -> Result<String, Box<dyn Error>> {
        Err("failed".into())
    }
}
