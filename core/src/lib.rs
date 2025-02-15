use core::fmt;
use std::collections::HashSet;
use std::collections::VecDeque;
// use std::error::Error;
use std::path::Path;
use std::path::PathBuf;
use std::rc::Rc;

use ast::FileAst;
use ast::FileId;
use ast::ItemKind;
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
use statics::Error;
use translate_bytecode::CompiledProgram;
use translate_bytecode::Translator;

pub fn abra_hello_world() {
    println!("Hello, world!");
}

pub fn source_files_single(src: &str) -> Vec<FileData> {
    vec![
        FileData::new("test.abra".into(), src.to_owned()),
        FileData::new("prelude.abra".into(), PRELUDE.to_owned()),
    ]
}

// the first file is the "main" file
pub fn compile_bytecode(
    files: Vec<FileData>, // TODO: just pass the main file in the future
    effects: Vec<EffectDesc>,
    file_provider: impl FileProvider,
) -> Result<CompiledProgram, String> {
    let mut errors: Vec<Error> = vec![];

    // this is what's passed to Statics
    let mut file_db = ast::FileDatabase::new();
    let mut node_map = ast::NodeMap::new();
    let mut file_asts: Vec<Rc<FileAst>> = vec![];

    let mut stack: VecDeque<FileId> = VecDeque::new();
    let mut visited = HashSet::<PathBuf>::new();
    for file_data in files {
        visited.insert(file_data.path.clone());
        let id = file_db.add(file_data);
        stack.push_back(id);
    }

    while let Some(file_id) = stack.pop_front() {
        let file_data = file_db.get(file_id).unwrap();
        let file_ast = parse::parse_or_err(file_id, file_data)?;

        file_asts.push(file_ast.clone());

        add_imports(
            file_ast,
            &mut file_db,
            &file_provider,
            &mut stack,
            &mut visited,
            &mut errors,
        );
    }

    for file_ast in file_asts.iter() {
        ast::initialize_node_map(&mut node_map, &(file_ast.clone() as Rc<dyn ast::Node>));
    }

    let inference_ctx = statics::analyze(&effects, &file_asts, &node_map, &file_db)?;

    // TODO: translator should be immutable
    // NOTE: It's only mutable right now because of ty_fits_impl_ty calls ast_type_to_statics_type...
    let mut translator = Translator::new(inference_ctx, node_map, file_db, file_asts, effects);
    Ok(translator.translate())
}

pub trait FileProvider {
    /// Given a path, return the contents of the file as a String,
    /// or an error if the file cannot be found.
    fn search_for_file(&self, path: &Path) -> Result<FileData, Box<dyn std::error::Error>>;
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
    fn search_for_file(&self, path: &Path) -> Result<FileData, Box<dyn std::error::Error>> {
        let home_dir = home::home_dir()
            .expect("Could not determine home directory when looking for ~/.abra/modules");
        let modules_dir = home_dir.join(".abra/modules");

        let desired = modules_dir.join(path);
        // println!("desired: {}", desired.display());
        if let Ok(contents) = std::fs::read_to_string(&desired) {
            return Ok(FileData::new(desired.clone(), contents));
        }

        Err(Box::new(MyError(
            "TODO add a better error message here".to_string(),
        )))
    }
}

#[derive(Debug)]
struct MyError(String);

impl fmt::Display for MyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Display the inner string
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for MyError {}

fn add_imports(
    file_ast: Rc<FileAst>,
    file_db: &mut ast::FileDatabase,
    file_provider: &impl FileProvider,
    stack: &mut VecDeque<FileId>,
    visited: &mut HashSet<PathBuf>,
    errors: &mut Vec<Error>,
) {
    for item in file_ast.items.iter() {
        if let ItemKind::Import(ident) = &*item.kind {
            let path = PathBuf::from(format!("{}.abra", ident.v));
            if !visited.contains(&path) {
                visited.insert(path.clone());

                let file_data = file_provider.search_for_file(&path);
                match file_data {
                    Ok(file_data) => {
                        let file_id = file_db.add(file_data);
                        stack.push_back(file_id);
                    }
                    Err(_) => errors.push(Error::UnresolvedIdentifier { node_id: item.id }),
                }
            }
        }
    }
}
