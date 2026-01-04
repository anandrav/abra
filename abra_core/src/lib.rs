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
mod assembly;
pub mod ast;
pub mod environment;
pub mod foreign_bindings;
pub mod host_bindings;
mod intrinsic;
mod optimize_bytecode;
mod parse;
pub mod prelude;
pub mod statics;
mod translate_bytecode;
pub mod vm;

use crate::statics::StaticsContext;
pub use ast::FileData;
pub use host_bindings::*;
pub use prelude::PRELUDE;
use statics::Error;
use translate_bytecode::CompiledProgram;
use translate_bytecode::Translator;

pub fn abra_hello_world() {
    println!("hello from abra_core");
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
    let file_asts = get_files(&mut ctx, &roots)?;
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
    let file_asts = get_files(&mut ctx, &roots)?;
    statics::analyze(&mut ctx, &file_asts)?;

    let translator = Translator::new(ctx, file_asts);
    Ok(translator.translate())
}

#[derive(Debug)]
pub struct ErrorSummary {
    msg: String,
    more: Option<(FileDatabase, Vec<Error>)>,
}

use std::io::IsTerminal;

fn c(code: &str) -> &str {
    let use_color = std::io::stdout().is_terminal();

    if use_color { code } else { "" }
}

impl ErrorSummary {
    pub fn emit(&self) {
        if !self.msg.is_empty() {
            let red = c("\x1B[1;31m");
            let bold = c("\x1b[1m");
            let reset = c("\x1b[0m");
            eprintln!("{red}{bold}error:{reset} {}", self.msg);
        }
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

fn get_files(ctx: &mut StaticsContext, roots: &[&str]) -> Result<Vec<Rc<FileAst>>, ErrorSummary> {
    let mut file_asts: Vec<Rc<FileAst>> = vec![];

    let mut stack: VecDeque<FileId> = VecDeque::new();
    let mut visited = HashSet::<PathBuf>::default();

    // main file
    for root in roots {
        let main_file_data = match ctx.file_provider.search_for_file(Path::new(root), true) {
            Err(e) => {
                return Err(ErrorSummary {
                    msg: e.to_string(),
                    more: None,
                });
            }
            Ok(main_file_data) => main_file_data,
        };
        visited.insert(main_file_data.absolute_path.clone());
        let id = ctx.file_db.add(main_file_data);
        stack.push_back(id);
    }

    // prelude
    {
        let prelude_file_data = FileData::new_simple("prelude.abra".into(), PRELUDE.into());
        visited.insert(prelude_file_data.absolute_path.clone());
        let id = ctx.file_db.add(prelude_file_data);
        stack.push_back(id);
    }

    while let Some(file_id) = stack.pop_front() {
        let file_ast = parse::parse_file(ctx, file_id);

        file_asts.push(file_ast.clone());

        add_imports(ctx, file_ast, &mut stack, &mut visited);
    }

    Ok(file_asts)
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

                let file_data = ctx.file_provider.search_for_file(&path, false);
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
    fn search_for_file(
        &self,
        path: &Path,
        is_root: bool,
    ) -> Result<FileData, Box<dyn std::error::Error>>;
}

#[derive(Default, Debug)]
pub struct OsFileProvider {
    main_file_dir: PathBuf,
    standard_modules_dir: PathBuf,
    import_dirs: Vec<PathBuf>,
}

impl OsFileProvider {
    pub fn single_dir(main_file_dir: PathBuf) -> Box<Self> {
        Self::new(main_file_dir, PathBuf::new(), vec![])
    }
    pub fn new(
        main_file_dir: PathBuf,
        standard_modules_dir: PathBuf,
        import_dirs: Vec<PathBuf>,
    ) -> Box<Self> {
        Box::new(Self {
            main_file_dir,
            standard_modules_dir,
            import_dirs,
        })
    }
}

impl FileProvider for OsFileProvider {
    fn search_for_file(
        &self,
        relative_path: &Path,
        is_root: bool,
    ) -> Result<FileData, Box<dyn std::error::Error>> {
        let mut package_name = relative_path.to_owned();
        package_name.set_extension("");
        // look in dir of main file
        {
            let absolute_path = self.main_file_dir.join(relative_path);
            if let Ok(contents) = std::fs::read_to_string(&absolute_path) {
                return Ok(FileData::new(package_name, absolute_path.clone(), contents));
            }
        }

        if is_root {
            return Err(Box::new(MyError(format!(
                "could not find main file `{}` in `{}`",
                relative_path.display(),
                self.main_file_dir.display()
            ))));
        }

        // TODO: files in dir of main file shadow those in modules. Emit an error if shadowing is detected when searching for a file
        // TODO: let mut found = false; if already_found { report_shadowing_error }
        // look in import dirs
        for dir in &self.import_dirs {
            let desired = dir.join(relative_path);
            if let Ok(contents) = std::fs::read_to_string(&desired) {
                return Ok(FileData::new(package_name, desired.clone(), contents));
            }
        }

        // TODO: files in dir of main file shadow those in modules. Emit an error if shadowing is detected when searching for a file
        // TODO: let mut found = false; if already_found { report_shadowing_error }
        // look in modules
        {
            let desired = self.standard_modules_dir.join(relative_path);
            if let Ok(contents) = std::fs::read_to_string(&desired) {
                return Ok(FileData::new(package_name, desired.clone(), contents));
            }
        }

        Err(Box::new(MyError(format!(
            "could not find file `{}` in main directory, any import directory, or standard modules directory",
            relative_path.display()
        ))))
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
    fn search_for_file(
        &self,
        relative_path: &Path,
        _is_root: bool,
    ) -> Result<FileData, Box<dyn std::error::Error>> {
        let mut package_name = relative_path.to_owned();
        package_name.set_extension("");
        match self.path_to_file.get(relative_path) {
            Some(contents) => Ok(FileData::new(
                package_name,
                relative_path.into(),
                contents.into(),
            )),
            None => Err(Box::new(MyError(format!(
                "could not find file `{}`",
                relative_path.display()
            )))),
        }
    }
}
