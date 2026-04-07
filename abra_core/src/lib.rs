/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
extern crate core;

use ast::FileAst;
use ast::FileDatabase;
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
pub use ast::FileId;
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

pub fn check2(
    main_file_name: &str,
    file_provider: Box<dyn FileProvider>,
) -> Result<(), ErrorSummary> {
    let roots = vec![main_file_name];
    let mut ctx = StaticsContext::new(file_provider);
    let file_asts = get_files(&mut ctx, &roots)?;
    statics::analyze(&mut ctx, &file_asts)?;
    Ok(())
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

    let prelude_file_data = match ctx
        .file_provider
        .search_for_file(Path::new("prelude.abra"), false)
    {
        Ok(fd) => FileData::new(fd.package_name, fd.absolute_path, PRELUDE.into()),
        Err(_) => FileData::new_simple("prelude.abra".into(), PRELUDE.into()),
    };

    // main file
    // NOTE: the first file in file_asts is implicitly considered the main file by bytecode translator.
    //       therefore, the main file is first inserted here, even before the prelude.
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
        // if main file is named "prelude.abra", it gets skipped
        // TODO: add an error message if user names the main file prelude.abra?
        if main_file_data.absolute_path == prelude_file_data.absolute_path {
            continue;
        }
        visited.insert(main_file_data.absolute_path.clone());
        let id = ctx.file_db.add(main_file_data);
        stack.push_back(id);
    }

    // prelude
    {
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

// --- LSP / check-only API ---

use std::ops::Range;

pub struct AnalysisResult {
    pub file_db: FileDatabase,
    pub(crate) ctx: StaticsContext,
    pub(crate) file_asts: Vec<Rc<FileAst>>,
}

#[derive(Debug, Clone)]
pub struct AnalysisError {
    pub message: String,
    pub file_id: FileId,
    pub range: Range<usize>,
    pub secondary_labels: Vec<(FileId, Range<usize>, String)>,
}

#[derive(Debug, Clone)]
pub struct DefinitionInfo {
    pub file_id: FileId,
    pub range: Range<usize>,
}

#[derive(Debug, Clone)]
pub struct CompletionCandidate {
    pub label: String,
    pub kind: CompletionCandidateKind,
}

#[derive(Debug, Clone)]
pub enum CompletionCandidateKind {
    Function,
    Field,
    EnumVariant,
    Type,
}

/// Run parse + type checking without bytecode translation.
/// Always returns results, even when there are errors.
pub fn check(main_file_name: &str, file_provider: Box<dyn FileProvider>) -> AnalysisResult {
    let mut ctx = StaticsContext::new(file_provider);
    let file_asts = match get_files(&mut ctx, &[main_file_name]) {
        Ok(asts) => asts,
        Err(e) => {
            // File loading failed — return result with just the error
            ctx.errors.push(Error::Generic {
                msg: e.msg.clone(),
                node: ast::AstNode::Item(Rc::new(ast::Item {
                    kind: Rc::new(ItemKind::Stmt(Rc::new(ast::Stmt {
                        kind: Rc::new(ast::StmtKind::Expr(Rc::new(ast::Expr {
                            kind: Rc::new(ast::ExprKind::Nil),
                            loc: ast::Location {
                                file_id: 0,
                                lo: 0,
                                hi: 0,
                            },
                            id: ast::NodeId::new(),
                        }))),
                        loc: ast::Location {
                            file_id: 0,
                            lo: 0,
                            hi: 0,
                        },
                        id: ast::NodeId::new(),
                    }))),
                    loc: ast::Location {
                        file_id: 0,
                        lo: 0,
                        hi: 0,
                    },
                    id: ast::NodeId::new(),
                })),
            });
            return AnalysisResult {
                file_db: ctx.file_db.clone(),
                ctx,
                file_asts: vec![],
            };
        }
    };

    // Run analysis — ignore the Result, keep ctx regardless
    let _ = statics::analyze(&mut ctx, &file_asts);

    AnalysisResult {
        file_db: ctx.file_db.clone(),
        ctx,
        file_asts,
    }
}

impl AnalysisResult {
    /// Get all errors from the analysis as LSP-friendly structs.
    pub fn errors(&self) -> Vec<AnalysisError> {
        self.ctx
            .errors
            .iter()
            .map(|error| {
                let diagnostic = error.make_diagnostic();
                let (primary_file, primary_range, message) =
                    extract_primary_from_diagnostic(&diagnostic);
                let secondary_labels = diagnostic
                    .labels
                    .iter()
                    .skip(1)
                    .map(|label| (label.file_id, label.range.clone(), label.message.clone()))
                    .collect();
                AnalysisError {
                    message,
                    file_id: primary_file,
                    range: primary_range,
                    secondary_labels,
                }
            })
            .collect()
    }

    /// Find the FileId for a given absolute path.
    pub fn file_id_for_path(&self, path: &Path) -> Option<FileId> {
        self.file_db
            .files
            .iter()
            .position(|f| f.absolute_path == path)
            .map(|i| i as FileId)
    }

    /// Get the definition location for the identifier at the given byte offset.
    pub fn definition_at(&self, file_id: FileId, offset: usize) -> Option<DefinitionInfo> {
        let file_ast = self.file_asts.iter().find(|f| f.loc.file_id == file_id)?;

        let node = ast::find_identifier_at_offset(file_ast, offset)?;
        let node_id = node.id();
        let decl = self.ctx.resolution_map.get(&node_id)?;
        declaration_location(decl)
    }

    /// Get the type of the expression at the given byte offset, as a display string.
    pub fn type_at(&self, file_id: FileId, offset: usize) -> Option<String> {
        let file_ast = self.file_asts.iter().find(|f| f.loc.file_id == file_id)?;

        let node = ast::find_innermost_node_at_offset(file_ast, offset)?;
        let solved = self.ctx.solution_of_node(node)?;
        Some(format!("{}", solved))
    }

    /// Get completion candidates for dot-access at the given byte offset.
    /// `offset` should be the position right after the dot character.
    pub fn completions_at(&self, file_id: FileId, offset: usize) -> Vec<CompletionCandidate> {
        let file_data = match self.file_db.get(file_id) {
            Ok(f) => f,
            Err(_) => return vec![],
        };
        let source = &file_data.source;

        // offset is after the dot
        if offset == 0 {
            return vec![];
        }
        let dot_pos = offset - 1;
        if source.as_bytes().get(dot_pos) != Some(&b'.') {
            return vec![];
        }

        // Extract the identifier before the dot
        let ident_end = dot_pos;
        let mut ident_start = ident_end;
        while ident_start > 0 {
            let b = source.as_bytes()[ident_start - 1];
            if b.is_ascii_alphanumeric() || b == b'_' {
                ident_start -= 1;
            } else {
                break;
            }
        }
        if ident_start >= ident_end {
            return vec![];
        }
        let ident_name = &source[ident_start..ident_end];

        let file_ast = match self.file_asts.iter().find(|f| f.loc.file_id == file_id) {
            Some(f) => f,
            None => return vec![],
        };

        // 1. Check imports for namespace completions
        for item in &file_ast.items {
            if let ItemKind::Import(path, ast::ImportKind::As(alias)) = &*item.kind
                && alias.v == ident_name
                && let Some(ns) = self.ctx.root_namespace.namespaces.get(&path.v)
            {
                return namespace_completions(ns);
            }
        }

        // 2. Search the AST for Variable nodes with this name, get their types
        let var_nodes = ast::find_variables_by_name(file_ast, ident_name);
        for var_node in &var_nodes {
            if let Some(solved_type) = self.ctx.solution_of_node(var_node.clone()) {
                let candidates = self.type_completions(&solved_type);
                if !candidates.is_empty() {
                    return candidates;
                }
            }
        }

        vec![]
    }

    fn type_completions(&self, solved_type: &statics::Type) -> Vec<CompletionCandidate> {
        use statics::typecheck::{Nominal, SolvedType, TypeKey};

        let mut candidates = vec![];
        match solved_type {
            SolvedType::Nominal(Nominal::Struct(struct_def), _) => {
                for field in &struct_def.fields {
                    candidates.push(CompletionCandidate {
                        label: field.name.v.clone(),
                        kind: CompletionCandidateKind::Field,
                    });
                }
                let type_key = TypeKey::TyApp(Nominal::Struct(struct_def.clone()));
                self.add_member_function_completions(&type_key, &mut candidates);
            }
            SolvedType::Nominal(Nominal::Enum(_enum_def), _) => {
                let type_key = TypeKey::TyApp(Nominal::Enum(_enum_def.clone()));
                self.add_member_function_completions(&type_key, &mut candidates);
            }
            SolvedType::Nominal(Nominal::Array, _) => {
                self.add_member_function_completions(
                    &TypeKey::TyApp(Nominal::Array),
                    &mut candidates,
                );
            }
            SolvedType::Int => {
                self.add_member_function_completions(&TypeKey::Int, &mut candidates);
            }
            SolvedType::Float => {
                self.add_member_function_completions(&TypeKey::Float, &mut candidates);
            }
            SolvedType::String => {
                self.add_member_function_completions(&TypeKey::String, &mut candidates);
            }
            _ => {}
        }
        candidates.sort_by(|a, b| a.label.cmp(&b.label));
        candidates
    }

    fn add_member_function_completions(
        &self,
        type_key: &statics::typecheck::TypeKey,
        candidates: &mut Vec<CompletionCandidate>,
    ) {
        for (tk, name) in self.ctx.member_functions.keys() {
            if tk == type_key {
                candidates.push(CompletionCandidate {
                    label: name.clone(),
                    kind: CompletionCandidateKind::Function,
                });
            }
        }
    }
}

fn namespace_completions(ns: &statics::Namespace) -> Vec<CompletionCandidate> {
    use statics::Declaration;

    let mut candidates = vec![];
    for (name, decl) in &ns.declarations {
        let kind = match decl {
            Declaration::FreeFunction(_) | Declaration::MemberFunction(_) => {
                CompletionCandidateKind::Function
            }
            Declaration::EnumVariant { .. } => CompletionCandidateKind::EnumVariant,
            Declaration::Struct(_)
            | Declaration::Enum(_)
            | Declaration::BuiltinType(_)
            | Declaration::InterfaceDef(_) => CompletionCandidateKind::Type,
            _ => CompletionCandidateKind::Function,
        };
        candidates.push(CompletionCandidate {
            label: name.clone(),
            kind,
        });
    }
    candidates.sort_by(|a, b| a.label.cmp(&b.label));
    candidates
}

fn extract_primary_from_diagnostic(
    diagnostic: &codespan_reporting::diagnostic::Diagnostic<FileId>,
) -> (FileId, Range<usize>, String) {
    if let Some(label) = diagnostic.labels.first() {
        (
            label.file_id,
            label.range.clone(),
            diagnostic.message.clone(),
        )
    } else {
        (0, 0..0, diagnostic.message.clone())
    }
}

fn declaration_location(decl: &statics::Declaration) -> Option<DefinitionInfo> {
    use statics::{Declaration, FuncResolutionKind};
    let node = match decl {
        Declaration::FreeFunction(FuncResolutionKind::Ordinary(func_def)) => func_def.name.node(),
        Declaration::FreeFunction(FuncResolutionKind::Host(func_decl)) => func_decl.name.node(),
        Declaration::FreeFunction(FuncResolutionKind::_Foreign { decl, .. }) => decl.name.node(),
        Declaration::MemberFunction(func_def) => func_def.name.node(),
        Declaration::InterfaceDef(iface) => iface.name.node(),
        Declaration::InterfaceMethod {
            iface,
            method_index,
        } => iface.methods[*method_index].name.node(),
        Declaration::InterfaceOutputType { ty, .. } => ty.name.node(),
        Declaration::Enum(e) => e.name.node(),
        Declaration::EnumVariant { e, variant } => e.variants[*variant].node(),
        Declaration::Struct(s) => s.name.node(),
        Declaration::Var(node) => node.clone(),
        Declaration::Polytype(statics::PolytypeDeclaration::Ordinary(p)) => p.name.node(),
        Declaration::Namespace(_, node) => node.clone(),
        Declaration::Intrinsic(_) | Declaration::BuiltinType(_) => return None,
        Declaration::Polytype(
            statics::PolytypeDeclaration::InterfaceSelf(_)
            | statics::PolytypeDeclaration::ArrayArg
            | statics::PolytypeDeclaration::IntrinsicOperation(..),
        ) => return None,
    };
    let loc = node.location();
    Some(DefinitionInfo {
        file_id: loc.file_id,
        range: loc.range(),
    })
}
