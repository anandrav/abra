/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ast::{
    AstNode, EnumDef, FileAst, FileDatabase, FileId, FuncDecl, FuncDef, InterfaceDef,
    InterfaceImpl, InterfaceOutputType, Location, NodeId, Polytype, StructDef, Type as AstType,
    TypeKind,
};
use crate::intrinsic::{BuiltinType, IntrinsicOperation};
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
use pat_exhaustiveness::{DeconstructedPat, check_pattern_exhaustiveness_and_usefulness};
pub(crate) use typecheck::Prov as TypeProv;
pub(crate) use typecheck::SolvedType as Type;

pub(crate) struct StaticsContext {
    pub(crate) file_db: FileDatabase,
    pub(crate) file_provider: Box<dyn FileProvider>,

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
    pub(crate) member_functions: HashMap<(TypeKey, String), (Declaration, AstNode)>,

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
    pub(crate) errors: Vec<Error>,
}

impl StaticsContext {
    pub(crate) fn new(file_provider: Box<dyn FileProvider>) -> Self {
        Self {
            file_db: FileDatabase::new(),
            file_provider,

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

    pub(crate) fn get_iface_decl(&self, name: &str) -> Rc<InterfaceDef> {
        if let Some(Declaration::InterfaceDef(iface_def)) =
            self.root_namespace.get_declaration(name)
        {
            iface_def.clone()
        } else {
            unreachable!() // TODO: this is NOT unreachable if prelude fails to parse. The prelude.abra should always parse properly but don't panic if it doesn't...
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Declaration {
    FreeFunction(FuncResolutionKind),
    MemberFunction(Rc<FuncDef>),
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
    // alternatively, add helper functions to check if it's a data type and to extract the NodeId from the particular declaration
    Struct(Rc<StructDef>),
    BuiltinType(BuiltinType), // TODO: why isn't Array part of BuiltinType
    EnumVariant {
        e: Rc<EnumDef>,
        variant: usize,
    },
    Intrinsic(IntrinsicOperation),
    Var(AstNode),
    Polytype(PolytypeDeclaration),
    Namespace(Rc<Namespace>, AstNode),
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
    InterfaceSelf(Rc<InterfaceDef>),                // `Self`
    Ordinary(Rc<Polytype>),                         // `T` in `struct Car<T>` in source code
    ArrayArg, // `T` in `struct array<T> = ` if that was actually in the source
    IntrinsicOperation(IntrinsicOperation, String), // `T` in `fn array_push(arr: array<T>) -> void` if that was actually in the source
}

impl Display for PolytypeDeclaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            PolytypeDeclaration::InterfaceSelf(_) => {
                write!(f, "Self from iface")
            }
            PolytypeDeclaration::Ordinary(polyty) => {
                write!(f, "{}[{}]", polyty.name.v, polyty.name.id)
            }
            PolytypeDeclaration::ArrayArg => {
                write!(f, "T from array")
            }
            PolytypeDeclaration::IntrinsicOperation(_, _) => {
                write!(f, "intrinsic's poly")
            }
        }
    }
}

// TODO: this is weird
// AstType is used because TypeVar has internal mutability and can't be stored in a hashmap
// SolvedType is used so that Display knows how to display the argument.
type InterfaceArguments = Vec<(Rc<InterfaceOutputType>, Rc<AstType>, SolvedType)>;

impl Declaration {
    pub fn into_type_key(self: Declaration) -> Option<TypeKey> {
        match self {
            Declaration::FreeFunction(..)
            | Declaration::InterfaceDef(_)
            | Declaration::InterfaceMethod { .. }
            | Declaration::MemberFunction { .. }
            | Declaration::Intrinsic(_)
            | Declaration::Var(_)
            | Declaration::Polytype(_)
            | Declaration::EnumVariant { .. }
            | Declaration::Namespace(_, _) => None,
            Declaration::InterfaceOutputType { iface: _, ty } => Some(TypeKey::InterfaceOutput(ty)),
            Declaration::Enum(enum_def) => Some(TypeKey::TyApp(Nominal::Enum(enum_def))),
            Declaration::Struct(struct_def) => Some(TypeKey::TyApp(Nominal::Struct(struct_def))),
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
    // parsing phase
    UnrecognizedToken(FileId, usize),
    UnexpectedToken(String, String, Location),
    ProblematicToken(String, Location),
    UnrecognizedEscapeSequence(FileId, Span),
    EmptyParentheses(Location),
    // resolution phase
    UnresolvedIdentifier {
        node: AstNode,
    },
    #[cfg(feature = "ffi")]
    CantLocateDylib {
        node: AstNode,
        msg: String,
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
    MemberFuncNameClash {
        name: String,
        ty: TypeKey,
        original: AstNode,
        new: AstNode,
    },
    // typechecking phase
    UnconstrainedUnifvar {
        node: AstNode,
    },
    PartiallyUnsolvedType {
        node: AstNode,
        tyvar: TypeVar,
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
    MemberAccessNeedsStruct {
        node: AstNode,
    },
    MustExtendType {
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
    InterfaceImplMissingMethod {
        iface: Rc<InterfaceDef>,
        ty: SolvedType,
        iface_impl_node: AstNode,
        missing_method_index: usize,
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
    ctx: &mut StaticsContext,
    file_asts: &Vec<Rc<FileAst>>,
) -> Result<(), ErrorSummary> {
    // scan declarations across all files
    scan_declarations(ctx, file_asts);

    // resolve all imports and identifiers
    resolve(ctx, file_asts);

    // typechecking
    solve_types(ctx, file_asts);

    // pattern exhaustiveness and usefulness checking
    check_pattern_exhaustiveness_and_usefulness(ctx, file_asts);
    check_errors(ctx)?;

    Ok(())
}

pub(crate) fn check_errors(ctx: &StaticsContext) -> Result<(), ErrorSummary> {
    if ctx.errors.is_empty() {
        return Ok(());
    }

    // TODO: don't clone files and errors
    Err(ErrorSummary {
        msg: "".to_string(),
        more: Some((ctx.file_db.clone(), ctx.errors.clone())),
    })
}

use crate::parse::Span;
use crate::statics::typecheck::Nominal;
use codespan_reporting::diagnostic::Label as CsLabel;
use utils::dlog;

impl AstNode {
    fn get_file_and_range(&self) -> (FileId, Range<usize>) {
        let loc = self.location();
        (loc.file_id, loc.range())
    }
}

pub(crate) fn _print_node(ctx: &StaticsContext, node: AstNode) {
    if cfg!(debug_assertions) {
        let (file, range) = node.get_file_and_range();

        let diagnostic = Diagnostic::note().with_labels(vec![CsLabel::secondary(file, range)]);

        let config = codespan_reporting::term::Config::default();

        let s = term::emit_into_string(&config, &ctx.file_db, &diagnostic).unwrap();
        dlog!("{}", s);
    }
}
