/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
extern crate core;

use ast::FileAst;
use ast::FileDatabase;
use ast::FileId;
use ast::ItemKind;
use core::fmt;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::fmt::{Display, Formatter};
use std::path::Path;
use std::path::PathBuf;
use std::rc::Rc;
pub mod addons;
mod assembly;
pub mod ast;
mod builtin;
pub mod environment;
pub mod host;
mod optimize_bytecode;
mod parse;
mod parse2;
pub mod prelude;
pub mod statics;
mod tokenizer;
mod translate_bytecode;
pub mod vm;

use crate::statics::StaticsContext;
pub use ast::FileData;
pub use host::*;
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

pub fn compile_bytecode(
    main_file_name: &str,
    file_provider: Box<dyn FileProvider>,
) -> Result<CompiledProgram, ErrorSummary> {
    compile_bytecode_(main_file_name, None, file_provider)
}

pub fn compile_and_dump_assembly(
    main_file_name: &str,
    file_provider: Box<dyn FileProvider>,
) -> Result<(), ErrorSummary> {
    let roots = vec![main_file_name];

    let mut ctx = StaticsContext::new(file_provider);
    let file_asts = get_files(&mut ctx, &roots);
    // TODO: this should be parse_then_analyze()
    statics::analyze(&mut ctx, &file_asts)?;

    let translator = Translator::new(ctx, file_asts);
    translator.dump_assembly();
    Ok(())
}

pub fn compile_bytecode_with_host_funcs(
    main_file_name: &str,
    main_host_func_file_name: &str,
    file_provider: Box<dyn FileProvider>,
) -> Result<CompiledProgram, ErrorSummary> {
    compile_bytecode_(
        main_file_name,
        Some(main_host_func_file_name),
        file_provider,
    )
}

fn compile_bytecode_(
    main_file_name: &str,
    main_host_func_file_name: Option<&str>,
    file_provider: Box<dyn FileProvider>,
) -> Result<CompiledProgram, ErrorSummary> {
    let mut roots = vec![main_file_name];
    if let Some(host) = main_host_func_file_name {
        roots.push(host);
    }
    let mut ctx = StaticsContext::new(file_provider);
    let file_asts = get_files(&mut ctx, &roots);
    statics::analyze(&mut ctx, &file_asts)?;

    let translator = Translator::new(ctx, file_asts);
    Ok(translator.translate())
}

#[derive(Debug)]
pub struct ErrorSummary {
    msg: String,
    more: Option<(FileDatabase, Vec<Error>)>,
}

impl ErrorSummary {
    fn msg(msg: String) -> Self {
        Self { msg, more: None }
    }

    pub fn emit(&self) {
        eprintln!("{}", self.msg);
        if let Some((file_db, errors)) = &self.more {
            for error in errors {
                error.emit(file_db);
            }
        }
    }

    pub fn to_string_ansi(&self) -> String {
        let mut s = String::new();
        s.push_str(&self.msg);
        if let Some((file_db, errors)) = &self.more {
            for error in errors {
                s.push_str(&error.to_string(file_db, true));
            }
        }
        s
    }
}

impl Display for ErrorSummary {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.msg)?;
        if let Some((file_db, errors)) = &self.more {
            for error in errors {
                writeln!(f, "{}", error.to_string(file_db, false))?;
            }
        }
        Ok(())
    }
}

impl std::error::Error for ErrorSummary {}

fn get_files(ctx: &mut StaticsContext, roots: &[&str]) -> Vec<Rc<FileAst>> {
    let mut file_asts: Vec<Rc<FileAst>> = vec![];

    let mut stack: VecDeque<FileId> = VecDeque::new();
    let mut visited = HashSet::<PathBuf>::default();

    // main file
    for root in roots {
        let main_file_data = ctx.file_provider.search_for_file(Path::new(root)).unwrap(); // TODO: don't unwrap. Figure out how to return better errors
        visited.insert(main_file_data.full_path.clone());
        let id = ctx.file_db.add(main_file_data);
        stack.push_back(id);
    }

    // prelude
    {
        let prelude_file_data =
            FileData::new("prelude.abra".into(), "prelude.abra".into(), PRELUDE.into());
        visited.insert(prelude_file_data.full_path.clone());
        let id = ctx.file_db.add(prelude_file_data);
        stack.push_back(id);
    }

    while let Some(file_id) = stack.pop_front() {
        let file_data = ctx.file_db.get(file_id).unwrap();

        let file_ast = if file_data.name() == "smol_sieve.abra" {
            parse2::parse_file(ctx, file_id)
        } else {
            match parse::parse_or_err(file_id, file_data) {
                Ok(it) => it,
                Err(e) => {
                    ctx.errors.push(Error::Parse(e));
                    continue;
                }
            }
        };

        file_asts.push(file_ast.clone());

        add_imports(ctx, file_ast, &mut stack, &mut visited);
    }

    file_asts
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
    ctx: &mut StaticsContext,
    file_ast: Rc<FileAst>,
    stack: &mut VecDeque<FileId>,
    visited: &mut HashSet<PathBuf>,
) {
    for item in file_ast.items.iter() {
        if let ItemKind::Import(ident, _) = &*item.kind {
            let path = PathBuf::from(format!("{}.abra", ident.v));
            if !visited.contains(&path) {
                visited.insert(path.clone());

                let file_data = ctx.file_provider.search_for_file(&path);
                match file_data {
                    Ok(file_data) => {
                        let file_id = ctx.file_db.add(file_data);
                        stack.push_back(file_id);
                    }
                    Err(_) => ctx
                        .errors
                        .push(Error::UnresolvedIdentifier { node: item.node() }),
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
    pub fn new(
        main_file_dir: PathBuf,
        modules: PathBuf,
        _shared_objects_dir: PathBuf,
    ) -> Box<Self> {
        Box::new(Self {
            main_file_dir,
            modules,
            #[cfg(feature = "ffi")]
            shared_objects_dir: _shared_objects_dir,
        })
    }
}

impl FileProvider for OsFileProvider {
    fn search_for_file(&self, path: &Path) -> Result<FileData, Box<dyn std::error::Error>> {
        // look in dir of main file
        {
            let desired = self.main_file_dir.join(path);
            if let Ok(contents) = std::fs::read_to_string(&desired) {
                return Ok(FileData::new(path.to_owned(), desired.clone(), contents));
            }
        }

        // TODO: files in dir of main file shadow those in modules. Emit an error if shadowing is detected when searching for a file
        // TODO: let mut found = false; if already_found { report_shadowing_error }
        // look in modules
        {
            let desired = self.modules.join(path);
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

    // TODO: take contents as String not &str
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
        &self._shared_objects_dir
    }
}
