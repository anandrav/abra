/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ast::{
    AstNode, EnumDef, FileAst, FileDatabase, FileId, FuncDecl, FuncDef, InterfaceDef,
    InterfaceImpl, InterfaceOutputType, NodeId, Polytype, StructDef, Type as AstType, TypeKind,
};
use crate::builtin::{BuiltinOperation, BuiltinType};
use crate::{ErrorSummary, FileProvider};
use resolve::{resolve, scan_declarations};
use std::fmt::{self, Display, Formatter};
use std::ops::Range;
use std::path::PathBuf;
use std::rc::Rc;
use typecheck::{ConstraintReason, PotentialType, SolvedType, TypeKey, TypeVar, solve_types};
use utils::hash::{HashMap, HashSet};
use utils::id_set::IdSet;
mod error;
mod pat_exhaustiveness;
mod resolve;
pub(crate) mod typecheck;
use codespan_reporting::diagnostic::Diagnostic;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use pat_exhaustiveness::{DeconstructedPat, check_pattern_exhaustiveness_and_usefulness};
pub(crate) use typecheck::Prov as TypeProv;
pub(crate) use typecheck::SolvedType as Type;

pub(crate) struct StaticsContext {
    _files: FileDatabase,
    _file_provider: Box<dyn FileProvider>,

    pub(crate) root_namespace: Namespace,
    // This maps any identifier in the program to the declaration it resolves to.
    pub(crate) resolution_map: HashMap<NodeId, Declaration>,

    // This maps some identifiers to their fully qualified name (FQN).
    // Currently it's only used for functions and types so translate_bytecode can mangle the function names
    // FQNs of types are needed to determine the FQN of a member function
    pub(crate) fully_qualified_names: HashMap<NodeId, String>,

    // This maps from some interface to its namespace. Used to resolve output types, which are
    // declared in the Interface's body, elsewhere in the body such as a function signature, in an
    // order-independent manner.
    pub(crate) interface_namespaces: HashMap<Rc<InterfaceDef>, Rc<Namespace>>,

    // BOOKKEEPING

    // most recent loops while traversing AST
    pub(crate) loop_stack: Vec<Option<NodeId>>,
    // most recent function return type while traversing AST
    pub(crate) func_ret_stack: Vec<TypeProv>,

    // map from interface name to list of its implementations
    pub(crate) interface_impls: HashMap<Rc<InterfaceDef>, Vec<Rc<InterfaceImpl>>>,
    // has interface impl already been type analyzed
    pub(crate) interface_impl_analyzed: HashSet<Rc<InterfaceImpl>>,
    // has interface decl already been type analyzed
    pub(crate) interface_def_analyzed: HashSet<Rc<InterfaceDef>>,
    // map from (type declaration, member function name) -> function declaration
    pub(crate) member_functions: HashMap<(TypeKey, String), Declaration>,

    // for loop function types. used by translator when desugaring for loop to calls
    // of Iterable.make_iterator() and Iterator.next(), which requires knowing the concrete
    // types of the methods
    pub(crate) for_loop_make_iterator_types: HashMap<NodeId, SolvedType>,
    pub(crate) for_loop_next_types: HashMap<NodeId, SolvedType>,

    // dylibs (for bytecode translation)
    pub(crate) dylibs: IdSet<PathBuf>,
    pub(crate) dylib_to_funcs: HashMap<u32, IdSet<String>>,
    // host functions
    pub(crate) host_funcs: IdSet<Rc<FuncDecl>>,

    // TYPE CHECKING

    // unification variables (skolems) which must be solved
    pub(crate) unifvars: HashMap<TypeProv, TypeVar>,

    // ERRORS
    errors: Vec<Error>,
}

impl StaticsContext {
    fn new(files: FileDatabase, file_provider: Box<dyn FileProvider>) -> Self {
        Self {
            _files: files,
            _file_provider: file_provider,

            root_namespace: Default::default(),
            resolution_map: Default::default(),
            fully_qualified_names: Default::default(),
            interface_namespaces: Default::default(),

            loop_stack: Default::default(),
            func_ret_stack: Default::default(),

            interface_impls: Default::default(),
            interface_impl_analyzed: Default::default(),
            interface_def_analyzed: Default::default(),
            member_functions: Default::default(),

            for_loop_make_iterator_types: Default::default(),
            for_loop_next_types: Default::default(),

            // int_constants: Default::default(),
            // float_constants: Default::default(),
            // string_constants: Default::default(),
            dylibs: Default::default(),
            dylib_to_funcs: Default::default(),
            host_funcs: IdSet::new(),

            unifvars: Default::default(),
            errors: Default::default(),
        }
    }

    pub(crate) fn solution_of_node(&self, node: AstNode) -> Option<SolvedType> {
        let prov = TypeProv::Node(node);
        match self.unifvars.get(&prov) {
            Some(unifvar) => unifvar.solution(),
            None => None,
        }
    }

    pub(crate) fn get_interface_declaration(&self, name: &str) -> Rc<InterfaceDef> {
        if let Some(Declaration::InterfaceDef(iface_def)) =
            self.root_namespace.get_declaration(name)
        {
            iface_def.clone()
        } else {
            unreachable!()
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Namespace {
    declarations: HashMap<String, Declaration>,
    namespaces: HashMap<String, Rc<Namespace>>,
}

impl Namespace {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_declaration(&self, path: &str) -> Option<Declaration> {
        let segments: Vec<_> = path.split('.').collect();
        let mut current_namespace: &Namespace = self;
        for segment in &segments[0..segments.len() - 1] {
            if let Some(ns) = current_namespace.namespaces.get(*segment) {
                current_namespace = ns;
            } else {
                return None;
            }
        }

        current_namespace
            .declarations
            .get(*segments.last()?)
            .cloned()
    }
}

impl Display for Namespace {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // indent for each level
        fn fmt_tree(tree: &Namespace, f: &mut Formatter, indent: usize) -> fmt::Result {
            for ident in tree.declarations.keys() {
                writeln!(f, "{:indent$}{}", "", ident)?;
            }
            for (ident, subtree) in &tree.namespaces {
                writeln!(f, "{:indent$}{}", "", ident)?;
                fmt_tree(subtree, f, indent + 2)?;
            }
            Ok(())
        }
        fmt_tree(self, f, 0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Declaration {
    Function(FuncResolutionKind),
    MemberFunction(FuncResolutionKind),
    InterfaceDef(Rc<InterfaceDef>),
    InterfaceMethod {
        iface: Rc<InterfaceDef>,
        method: usize,
    },
    InterfaceOutputType {
        iface: Rc<InterfaceDef>,
        ty: Rc<InterfaceOutputType>,
    },
    Enum(Rc<EnumDef>),
    EnumVariant {
        e: Rc<EnumDef>,
        variant: usize,
    },
    // TODO: maybe combine Enum, Struct, and Array into "Nominal". Easier to know if a declaration is a datatype or not.
    // alternatively, add helper functions to check if it's a data type and to extract the NodeId from the particular declaration
    Struct(Rc<StructDef>),
    Array,
    // BuiltinType(BuiltinType),
    Builtin(BuiltinOperation),
    BuiltinType(BuiltinType),
    Var(AstNode),
    Polytype(PolytypeDeclaration),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum FuncResolutionKind {
    Ordinary(Rc<FuncDef>),
    Host(Rc<FuncDecl>),
    _Foreign {
        decl: Rc<FuncDecl>,
        libname: PathBuf,
        symbol: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum PolytypeDeclaration {
    InterfaceSelf(Rc<InterfaceDef>),   // `Self`
    Ordinary(Rc<Polytype>),            // `a`
    Builtin(BuiltinOperation, String), // `a` in array_push: array<a> -> void
}

// TODO: this is weird
// AstType is used because TypeVar has internal mutability and can't be stored in a hashmap
// SolvedType is used so that Display knows how to display the argument.
type InterfaceArguments = Vec<(Rc<InterfaceOutputType>, Rc<AstType>, SolvedType)>;

impl Declaration {
    pub fn into_type_key(self: Declaration) -> Option<TypeKey> {
        match self {
            Declaration::Function(..)
            | Declaration::InterfaceDef(_)
            | Declaration::InterfaceMethod { .. }
            | Declaration::MemberFunction { .. }
            | Declaration::Builtin(_)
            | Declaration::Var(_)
            | Declaration::Polytype(_)
            | Declaration::EnumVariant { .. } => None,
            Declaration::InterfaceOutputType { .. } => unimplemented!(),
            Declaration::Enum(enum_def) => Some(TypeKey::TyApp(Nominal::Enum(enum_def))),
            Declaration::Struct(struct_def) => Some(TypeKey::TyApp(Nominal::Struct(struct_def))),
            Declaration::Array => Some(TypeKey::TyApp(Nominal::Array)),
            Declaration::BuiltinType(builtin_type) => Some(builtin_type.to_type_key()),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum Error {
    Generic {
        msg: String,
        node: AstNode,
    },
    // resolution phase
    UnresolvedIdentifier {
        node: AstNode,
    },
    UnresolvedMemberFunction {
        receiver_node: AstNode,
        memfn_node: AstNode,
        ty: PotentialType,
    },
    NameClash {
        name: String,
        original: Declaration,
        new: Declaration,
    },
    // typechecking phase
    UnconstrainedUnifvar {
        node: AstNode,
    },
    ConflictingUnifvar {
        types: HashMap<TypeKey, PotentialType>,
    },
    TypeConflict {
        ty1: PotentialType,
        ty2: PotentialType,
        constraint_reason: ConstraintReason,
    },
    MemberAccessNeedsAnnotation {
        node: AstNode,
    },
    MustExtendType {
        node: AstNode,
    },
    MemberFunctionMissingFirstSelfArgument {
        node: AstNode,
    },
    UnqualifiedEnumNeedsAnnotation {
        node: AstNode,
    },
    InterfaceNotImplemented {
        ty: SolvedType,
        iface: Rc<InterfaceDef>,
        node: AstNode,
    },
    InterfaceImplTypeNotGeneric {
        node: AstNode,
    },
    // break and continue
    NotInLoop {
        node: AstNode,
    },
    // return
    CantReturnHere {
        node: AstNode,
    },
    // pattern matching exhaustiveness check
    NonexhaustiveMatch {
        node: AstNode,
        missing: Vec<DeconstructedPat>,
    },
    RedundantArms {
        node: AstNode,
        redundant_arms: Vec<AstNode>,
    },
    #[cfg(not(feature = "ffi"))]
    FfiNotEnabled(AstNode),
}

// main function that performs typechecking (as well as name resolution beforehand)
pub(crate) fn analyze(
    file_asts: &Vec<Rc<FileAst>>,
    files: &FileDatabase,
    file_provider: Box<dyn FileProvider>,
) -> Result<StaticsContext, ErrorSummary> {
    let mut ctx = StaticsContext::new(files.clone(), file_provider);

    // scan declarations across all files
    scan_declarations(&mut ctx, file_asts);

    // resolve all imports and identifiers
    resolve(&mut ctx, file_asts);

    // typechecking
    solve_types(&mut ctx, file_asts);

    // pattern exhaustiveness and usefulness checking
    check_pattern_exhaustiveness_and_usefulness(&mut ctx, file_asts);
    // println!("finished checking pattern exhaustivenss and usefulenss");
    check_errors(&ctx, files)?;
    // println!("finished checking errors");

    Ok(ctx)
}

pub(crate) fn check_errors(ctx: &StaticsContext, files: &FileDatabase) -> Result<(), ErrorSummary> {
    if ctx.errors.is_empty() {
        return Ok(());
    }

    // TODO: don't clone files and errors
    Err(ErrorSummary {
        msg: "".to_string(),
        more: Some((files.clone(), ctx.errors.clone())),
    })
}

use crate::statics::typecheck::Nominal;
use codespan_reporting::diagnostic::Label as CsLabel;

impl AstNode {
    fn get_file_and_range(&self) -> (FileId, Range<usize>) {
        let loc = self.location();
        (loc.file_id, loc.range())
    }
}

pub(crate) fn _print_node(ctx: &StaticsContext, node: AstNode) {
    let (file, range) = node.get_file_and_range();

    let diagnostic = Diagnostic::note().with_labels(vec![CsLabel::secondary(file, range)]);

    let writer = StandardStream::stderr(ColorChoice::Always);
    let config = codespan_reporting::term::Config::default();

    term::emit_to_io_write(&mut writer.lock(), &config, &ctx._files, &diagnostic).unwrap();
}
