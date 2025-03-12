use core::fmt;
use std::collections::HashMap;
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
        FileData::new("test.abra".into(), "test.abra".into(), src.to_owned()),
        FileData::new(
            "prelude.abra".into(),
            "prelude.abra".into(),
            PRELUDE.to_owned(),
        ),
    ]
}

// the first file is the "main" file
pub fn compile_bytecode(
    main_file_name: &str,
    effects: Vec<EffectDesc>,
    file_provider: Box<dyn FileProvider>,
) -> Result<CompiledProgram, String> {
    // TODO: these errors aren't actually being used
    let mut errors: Vec<Error> = vec![];

    // this is what's passed to Statics
    let mut file_db = ast::FileDatabase::new();
    let mut file_asts: Vec<Rc<FileAst>> = vec![];

    let mut stack: VecDeque<FileId> = VecDeque::new();
    let mut visited = HashSet::<PathBuf>::new();

    // main file
    {
        let main_file_data = file_provider
            .search_for_file(Path::new(main_file_name))
            .unwrap(); // TODO: don't unwrap. Figure out how to return better errors
        visited.insert(main_file_data.full_path.clone());
        let id = file_db.add(main_file_data);
        stack.push_back(id);
    }

    // prelude
    {
        let prelude_file_data =
            FileData::new("prelude.abra".into(), "prelude.abra".into(), PRELUDE.into());
        visited.insert(prelude_file_data.full_path.clone());
        let id = file_db.add(prelude_file_data);
        stack.push_back(id);
    }

    while let Some(file_id) = stack.pop_front() {
        let file_data = file_db.get(file_id).unwrap();
        let file_ast = parse::parse_or_err(file_id, file_data)?;

        file_asts.push(file_ast.clone());

        add_imports(
            file_ast,
            &mut file_db,
            file_provider.as_ref(),
            &mut stack,
            &mut visited,
            &mut errors,
        );
    }

    // println!("time to analyze");
    let inference_ctx = statics::analyze(&effects, &file_asts, &file_db, file_provider)?;

    // TODO: translator should be immutable
    // NOTE: It's only mutable right now because of ty_fits_impl_ty calls ast_type_to_statics_type...
    // println!("time to translate");
    let mut translator = Translator::new(inference_ctx, file_db, file_asts);
    // println!("successfully translated");
    Ok(translator.translate())
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
    file_provider: &dyn FileProvider,
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
                    Err(_) => errors.push(Error::UnresolvedIdentifier { node: item.node() }),
                }
            }
        }
    }
}

pub trait FileProvider {
    /// Given a path, return the contents of the file as a String,
    /// or an error if the file cannot be found.
    fn search_for_file(&self, path: &Path) -> Result<FileData, Box<dyn std::error::Error>>;

    #[cfg(feature = "ffi")]
    fn shared_objects_dir(&self) -> &PathBuf;
}

#[derive(Default, Debug)]
pub struct OsFileProvider {
    main_file_dir: PathBuf,
    modules: PathBuf,
    #[cfg(feature = "ffi")]
    shared_objects_dir: PathBuf,
}

impl OsFileProvider {
    pub fn todo_get_rid_of_this() -> Box<Self> {
        Box::new(Self {
            main_file_dir: PathBuf::new(),
            modules: PathBuf::new(),
            #[cfg(feature = "ffi")]
            shared_objects_dir: PathBuf::new(),
        })
    }

    pub fn new(
        main_file_dir: PathBuf,
        modules: PathBuf,
        #[cfg(feature = "ffi")] shared_objects_dir: PathBuf,
    ) -> Box<Self> {
        Box::new(Self {
            main_file_dir,
            modules,
            #[cfg(feature = "ffi")]
            shared_objects_dir,
        })
    }
}

impl FileProvider for OsFileProvider {
    fn search_for_file(&self, path: &Path) -> Result<FileData, Box<dyn std::error::Error>> {
        // look in modules first
        {
            let desired = self.modules.join(path);
            if let Ok(contents) = std::fs::read_to_string(&desired) {
                return Ok(FileData::new(path.to_owned(), desired.clone(), contents));
            }
        }

        // then look in dir of main file
        {
            let desired = self.main_file_dir.join(path);
            if let Ok(contents) = std::fs::read_to_string(&desired) {
                return Ok(FileData::new(path.to_owned(), desired.clone(), contents));
            }
        }

        Err(Box::new(MyError(format!(
            "Could not find desired file: {}",
            path.display()
        ))))
    }

    #[cfg(feature = "ffi")]
    fn shared_objects_dir(&self) -> &PathBuf {
        &self.shared_objects_dir
    }
}

#[derive(Default, Debug)]
pub struct MockFileProvider {
    path_to_file: HashMap<PathBuf, String>,
    _shared_objects_dir: PathBuf,
}

impl MockFileProvider {
    pub fn new(mut path_to_file: HashMap<PathBuf, String>) -> Box<Self> {
        path_to_file.insert(Path::new("prelude.abra").to_path_buf(), PRELUDE.into());
        Box::new(Self {
            path_to_file,
            _shared_objects_dir: PathBuf::new(),
        })
    }

    pub fn single_file(contents: &str) -> Box<Self> {
        let mut path_to_file = HashMap::new();
        path_to_file.insert(Path::new("prelude.abra").to_path_buf(), PRELUDE.into());
        path_to_file.insert(Path::new("main.abra").to_path_buf(), contents.into());
        Box::new(Self {
            path_to_file,
            _shared_objects_dir: PathBuf::new(),
        })
    }
}

impl FileProvider for MockFileProvider {
    fn search_for_file(&self, path: &Path) -> Result<FileData, Box<dyn std::error::Error>> {
        match self.path_to_file.get(path) {
            Some(contents) => Ok(FileData::new(path.into(), path.into(), contents.into())),
            None => Err(Box::new(MyError(format!(
                "Could not find desired file: {}",
                path.display()
            )))),
        }
    }

    #[cfg(feature = "ffi")]
    fn shared_objects_dir(&self) -> &PathBuf {
        &self._shared_objects_dir // TODO: this unused and only here to satisfy the Trait, but it doesn't really make sense...
    }
}
