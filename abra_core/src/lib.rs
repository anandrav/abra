/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use ast::FileAst;
use ast::FileDatabase;
use ast::FileId;
use ast::ItemKind;
use core::fmt;
use std::collections::VecDeque;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::rc::Rc;
use utils::hash::HashMap;
use utils::hash::HashSet;
pub mod addons;
mod assembly;
pub mod ast;
mod builtin;
pub mod environment;
mod parse;
pub mod prelude;
pub mod statics;
mod translate_bytecode;
pub mod vm;
use crate::ast::{Type, TypeKind};
use addons::*;
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

// TODO: don't use String for error in return type
pub fn compile_bytecode(
    main_file_name: &str,
    file_provider: Box<dyn FileProvider>,
) -> Result<CompiledProgram, String> {
    let (file_asts, file_db) = get_files(main_file_name, &*file_provider)?;
    let inference_ctx = statics::analyze(&file_asts, &file_db, file_provider)?;

    let translator = Translator::new(inference_ctx, file_db, file_asts);
    Ok(translator.translate())
}

fn get_files(
    main_file_name: &str,
    file_provider: &dyn FileProvider,
) -> Result<(Vec<Rc<FileAst>>, FileDatabase), String> {
    // TODO: these errors aren't actually being used
    let mut errors: Vec<Error> = vec![];

    // this is what's passed to Statics
    let mut file_db = FileDatabase::new();
    let mut file_asts: Vec<Rc<FileAst>> = vec![];

    let mut stack: VecDeque<FileId> = VecDeque::new();
    let mut visited = HashSet::<PathBuf>::default();

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
            file_provider,
            &mut stack,
            &mut visited,
            &mut errors,
        );
    }

    Ok((file_asts, file_db))
}

pub fn generate_host_function_enum(
    main_file_name: &str,
    file_provider: Box<dyn FileProvider>,
    destination: &Path,
) -> Result<(), String> {
    let (file_asts, file_db) = get_files(main_file_name, &*file_provider)?;
    let inference_ctx = statics::analyze(&file_asts, &file_db, file_provider)?;

    let mut output = String::new();
    output.push_str(
        r#"// This is an auto-generated file.

use abra_core::vm::*;
use abra_core::addons::*;
use std::ffi::c_void;
"#,
    );

    output.push_str(
        r#"pub enum HostFunctionArgs {
    "#,
    );
    for f in &inference_ctx.host_funcs {
        let camel_name = heck::AsUpperCamelCase(&f.name.v).to_string();
        let args = {
            if f.args.is_empty() {
                "".to_string()
            } else {
                let mut s = "(".to_string();
                for (i, arg) in f.args.iter().enumerate() {
                    let ty = arg.1.clone().unwrap();
                    if i != 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&name_of_ty(&ty));
                }
                s.push(')');
                s
            }
        };
        output.push_str(&format!("{camel_name}{args},"));
    }
    output.push_str(
        r#"
    }
    "#,
    );

    output.push_str(
        r#"impl HostFunctionArgs {
                    "#,
    );
    output.push_str(
        r#"pub(crate) fn from_vm(vm: &mut Vm, pending_host_func: u16) -> Self {
                        "#,
    );
    output.push_str("match pending_host_func {");
    for (i, f) in inference_ctx.host_funcs.iter().enumerate() {
        output.push_str(&format!("{i} => {{"));
        let camel_name = heck::AsUpperCamelCase(&f.name.v).to_string();
        for (i, arg) in f.args.iter().enumerate() {
            let ty = arg.1.clone().unwrap();
            let tyname = name_of_ty(&ty);
            output.push_str(&format!(
                r#"let arg{}: {tyname} = unsafe {{ <{tyname}>::from_vm(vm as *mut Vm as *mut c_void, &ABRA_VM_FUNCS) }};
                            "#, i
            ));
        }
        let mut args = String::new();
        if !f.args.is_empty() {
            args.push('(');
            for i in 0..f.args.len() {
                if i != 0 {
                    args.push_str(", ");
                }
                args.push_str(&format!("arg{}", i));
            }
            args.push(')');
        }
        output.push_str(&format!("HostFunctionArgs::{camel_name}{args}"));
        output.push('}');
    }
    output.push_str(r#"_ => panic!("unexpected tag encountered: {pending_host_func}")"#);
    output.push('}');
    output.push('}');
    output.push('}');

    output.push_str(
        r#"
pub enum HostFunctionRet {
    "#,
    );
    for f in &inference_ctx.host_funcs {
        let camel_name = heck::AsUpperCamelCase(&f.name.v).to_string();
        let out = {
            match &*f.ret_type.kind {
                TypeKind::Void => "".to_string(),
                TypeKind::Tuple(elems) => {
                    let mut s = "(".to_string();
                    for (i, ty) in elems.iter().enumerate() {
                        if i != 0 {
                            s.push_str(", ");
                        }
                        s.push_str(&name_of_ty(ty));
                    }
                    s.push(')');
                    s
                }
                _ => {
                    format!("({})", name_of_ty(&f.ret_type))
                }
            }
        };
        output.push_str(&format!("{camel_name}{out},"));
    }
    output.push_str(
        r#"
    }"#,
    );

    output.push_str(
        r#"impl HostFunctionRet {
                    "#,
    );
    output.push_str(
        r#"pub(crate) fn into_vm(self, vm: &mut Vm,) {
                        "#,
    );
    output.push_str("match self {");
    for f in inference_ctx.host_funcs.iter() {
        let camel_name = heck::AsUpperCamelCase(&f.name.v).to_string();
        let tuple_helper = |elems: &Vec<Rc<Type>>| {
            let mut s = "(".to_string();
            for i in 0..elems.len() {
                if i != 0 {
                    s.push_str(", ");
                }
                s.push_str(&format!("out{}", i));
            }
            s.push(')');
            s
        };
        let out = {
            match &*f.ret_type.kind {
                TypeKind::Void => "".to_string(),
                TypeKind::Tuple(elems) => tuple_helper(elems),
                _ => "(out)".into(),
            }
        };
        output.push_str(&format!("HostFunctionRet::{}{out} => {{", camel_name));
        let out_val = {
            match &*f.ret_type.kind {
                TypeKind::Void => "()".to_string(),
                TypeKind::Tuple(elems) => tuple_helper(elems),
                _ => "out".into(),
            }
        };
        output.push_str(&format!(
            r#"unsafe {{ {out_val}.to_vm(vm as *mut Vm as *mut c_void, &ABRA_VM_FUNCS) }};
                            "#
        ));
        output.push('}');
        output.push(',');
    }
    output.push('}');
    output.push('}');
    output.push('}');

    std::fs::write(destination, output).unwrap();

    Command::new("rustfmt")
        .arg(destination)
        .status()
        .map_err(|e| e.to_string())?;

    Ok(())
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
    file_db: &mut FileDatabase,
    file_provider: &dyn FileProvider,
    stack: &mut VecDeque<FileId>,
    visited: &mut HashSet<PathBuf>,
    errors: &mut Vec<Error>,
) {
    for item in file_ast.items.iter() {
        if let ItemKind::Import(ident, _) = &*item.kind {
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
        let mut path_to_file = HashMap::default();
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
