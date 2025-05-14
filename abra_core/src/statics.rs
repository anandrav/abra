/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::FileProvider;
use crate::ast::{
    AstNode, EnumDef, FileAst, FileDatabase, FileId, FuncDecl, FuncDef, InterfaceDecl,
    InterfaceImpl, NodeId, Polytype, StructDef, TypeKind,
};
use crate::builtin::Builtin;
use resolve::{resolve, scan_declarations};
use std::fmt::{self, Display, Formatter};
use std::ops::Range;
use std::path::PathBuf;
use std::rc::Rc;
use typecheck::{
    ConstraintReason, PotentialType, Reason, SolvedType, TypeKey, TypeVar, fmt_conflicting_types,
    solve_types,
};
use utils::hash::HashMap;
use utils::id_set::IdSet;
mod pat_exhaustiveness;
mod resolve;
pub(crate) mod typecheck;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use pat_exhaustiveness::{DeconstructedPat, check_pattern_exhaustiveness_and_usefulness};
pub(crate) use typecheck::Prov as TypeProv;
pub(crate) use typecheck::SolvedType as Type;
pub(crate) use typecheck::ty_fits_impl_ty;

pub(crate) struct StaticsContext {
    _files: FileDatabase,
    _file_provider: Box<dyn FileProvider>,

    pub(crate) root_namespace: Namespace,
    // This maps any identifier in the program to the declaration it resolves to.
    pub(crate) resolution_map: HashMap<NodeId, Declaration>,

    // BOOKKEEPING

    // most recent loops while traversing AST
    pub(crate) loop_stack: Vec<Option<NodeId>>,
    // most recent function return type while traversing AST
    pub(crate) func_ret_stack: Vec<TypeProv>,

    // map from interface name to list of its implementations
    pub(crate) interface_impls: HashMap<Rc<InterfaceDecl>, Vec<Rc<InterfaceImpl>>>,
    // map from type definition to linked member functions
    pub(crate) member_functions: HashMap<NodeId, HashMap<String, Rc<FuncDef>>>,

    // string constants (for bytecode translation)
    pub(crate) string_constants: IdSet<String>,
    // dylibs (for bytecode translation)
    pub(crate) dylibs: IdSet<PathBuf>,
    pub(crate) dylib_to_funcs: HashMap<u32, IdSet<String>>,
    // host functions
    pub(crate) host_funcs: IdSet<String>,

    // TYPE CHECKING

    // unification variables (skolems) which must be solved
    pub(crate) unifvars: HashMap<TypeProv, TypeVar>,
    pub(crate) unifvars_constrained_to_interfaces:
        HashMap<TypeProv, Vec<(Rc<InterfaceDecl>, AstNode)>>,

    // ERRORS
    errors: Vec<Error>,
}

impl StaticsContext {
    fn new(files: FileDatabase, file_provider: Box<dyn FileProvider>) -> Self {
        let mut ctx = Self {
            _files: files,
            _file_provider: file_provider,
            root_namespace: Default::default(),
            resolution_map: Default::default(),
            loop_stack: Default::default(),
            func_ret_stack: Default::default(),
            interface_impls: Default::default(),
            member_functions: Default::default(),
            string_constants: Default::default(),
            dylibs: Default::default(),
            dylib_to_funcs: Default::default(),
            host_funcs: Default::default(),
            unifvars: Default::default(),
            unifvars_constrained_to_interfaces: Default::default(),
            errors: Default::default(),
        };

        ctx.string_constants.insert("\n".to_string());
        ctx
    }

    pub(crate) fn solution_of_node(&self, node: AstNode) -> Option<SolvedType> {
        let prov = TypeProv::Node(node);
        match self.unifvars.get(&prov) {
            Some(unifvar) => unifvar.solution(),
            None => None,
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
    FreeFunction(Rc<FuncDef>, String),
    HostFunction(Rc<FuncDecl>, String),
    _ForeignFunction {
        decl: Rc<FuncDecl>,
        libname: PathBuf,
        symbol: String,
    },
    InterfaceDef(Rc<InterfaceDecl>),
    InterfaceMethod {
        iface_def: Rc<InterfaceDecl>,
        method: u16,
        fully_qualified_name: String,
    },
    MemberFunction {
        func: Rc<FuncDef>,
    },
    Enum(Rc<EnumDef>),
    EnumVariant {
        enum_def: Rc<EnumDef>,
        variant: u16,
    },
    // TODO: maybe combine Enum, Struct, and Array into "Nominal"
    Struct(Rc<StructDef>),
    Array,
    Polytype(Rc<Polytype>),
    Builtin(Builtin),
    Var(AstNode),
}

#[derive(Debug)]
pub(crate) enum Error {
    // resolution phase
    UnresolvedIdentifier {
        node: AstNode,
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
    MemberAccessMustBeStructOrEnum {
        node: AstNode,
        ty: SolvedType,
    },
    MustExtendStructOrEnum {
        node: AstNode,
        name: String,
    },
    UnqualifiedEnumNeedsAnnotation {
        node: AstNode,
    },
    InterfaceNotImplemented {
        ty: SolvedType,
        iface: Rc<InterfaceDecl>,
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
) -> Result<StaticsContext, String> {
    let mut ctx = StaticsContext::new(files.clone(), file_provider);

    // scan declarations across all files
    scan_declarations(&mut ctx, file_asts);

    // resolve all imports and identifiers
    resolve(&mut ctx, file_asts);

    // typechecking
    solve_types(&mut ctx, file_asts);

    // pattern exhaustiveness and usefulness checking
    check_pattern_exhaustiveness_and_usefulness(&mut ctx, file_asts);
    check_errors(&ctx, files)?;

    Ok(ctx)
}

pub(crate) fn check_errors(ctx: &StaticsContext, files: &FileDatabase) -> Result<(), String> {
    if ctx.errors.is_empty() {
        return Ok(());
    }

    for error in &ctx.errors {
        error.show(ctx, files);
    }

    Err("Failed to compile.".to_string())
}

// TODO: reduce code duplication for displaying error messages, types
impl Error {
    fn show(&self, _ctx: &StaticsContext, files: &FileDatabase) {
        // dbg!(self);
        let mut diagnostic = Diagnostic::error();
        let mut labels = Vec::new();
        let mut notes = Vec::new();

        // get rid of this after making our own file database
        let get_file_and_range = |node: &AstNode| {
            let span = node.location();
            (span.file_id, span.range())
        };

        match self {
            Error::NameClash {
                name,
                original,
                new,
            } => {
                diagnostic =
                    diagnostic.with_message(format!("`{}` was declared more than once", name));
                add_detail_for_decl(
                    _ctx,
                    &mut labels,
                    &mut notes,
                    original,
                    "first declared here",
                );
                add_detail_for_decl(_ctx, &mut labels, &mut notes, new, "then declared here");
            }
            Error::UnresolvedIdentifier { node } => {
                let (file, range) = node.get_file_and_range();
                diagnostic = diagnostic.with_message("Could not resolve identifier");
                labels.push(Label::secondary(file, range))
            }
            Error::UnconstrainedUnifvar { node } => {
                let (file, range) = node.get_file_and_range();
                diagnostic = diagnostic.with_message("Can't solve type. Try adding an annotation");
                labels.push(Label::secondary(file, range))
            }
            Error::ConflictingUnifvar { types } => {
                diagnostic = diagnostic.with_message("Conflicting types during inference");

                let mut type_conflict: Vec<PotentialType> = types.values().cloned().collect();
                type_conflict.sort_by_key(|ty| ty.reasons().borrow().len());

                let mut conflicting_types_str = String::new();
                fmt_conflicting_types(&type_conflict, &mut conflicting_types_str).unwrap();
                notes.push(conflicting_types_str);
                for ty in type_conflict {
                    let reasons = ty.reasons().borrow();
                    for reason in reasons.iter() {
                        handle_reason(&ty, reason, &mut labels, &mut notes);
                    }
                }
            }
            Error::TypeConflict {
                ty1,
                ty2,
                constraint_reason,
            } => match constraint_reason {
                ConstraintReason::None => {
                    diagnostic = diagnostic
                        .with_message(format!("Conflicting types `{}` and `{}`", ty2, ty1));

                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::BinaryOperandsMustMatch(node) => {
                    diagnostic = diagnostic.with_message("Operands must have the same type");
                    let (file, range) = node.get_file_and_range();
                    labels.push(Label::secondary(file, range).with_message("operator"));

                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::IfElseBodies => {
                    diagnostic =
                        diagnostic.with_message("Branches of if-else expression do not match");
                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::LetStmtAnnotation => {
                    diagnostic = diagnostic.with_message("Variable and annotation do not match");
                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::LetSetLhsRhs => {
                    diagnostic = diagnostic.with_message("Variable and assignment do not match");
                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::MatchScrutinyAndPattern => {
                    diagnostic = diagnostic.with_message(format!(
                        "Match expression input has type `{}`, but case has type `{}`",
                        ty1, ty2
                    ));
                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::FuncCall(node) => {
                    diagnostic = diagnostic.with_message("Wrong argument type");
                    let (file, range) = node.get_file_and_range();
                    labels.push(Label::secondary(file, range).with_message("function call"));

                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::ReturnValue => {
                    diagnostic = diagnostic.with_message("Return value has wrong type");

                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::Condition => {
                    diagnostic = diagnostic
                        .with_message(format!("Condition must be a `bool` but got `{}`\n", ty1));

                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::BinaryOperandBool(node) => {
                    diagnostic = diagnostic
                        .with_message(format!("Operand must be `bool` but got `{}`\n", ty1));
                    let (file, range) = node.get_file_and_range();
                    labels.push(Label::secondary(file, range).with_message("boolean operator"));

                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::IndexAccess => {
                    notes.push("type conflict due to array index is int".to_string());
                }
            },
            Error::MemberAccessNeedsAnnotation { node } => {
                diagnostic = diagnostic
                    .with_message("Can't perform member access without knowing type. Try adding a type annotation.");
                let (file, range) = node.get_file_and_range();
                labels.push(Label::secondary(file, range));
            }
            Error::MemberAccessMustBeStructOrEnum { node, ty } => {
                diagnostic = diagnostic.with_message(format!(
                    "Can't perform member access on type which isn't a struct or enum: `{}`",
                    ty
                ));
                let (file, range) = node.get_file_and_range();
                labels.push(Label::secondary(file, range));
            }
            Error::MustExtendStructOrEnum { node, name } => {
                diagnostic = diagnostic.with_message(format!(
                    "Can't extend a type which isn't a struct or enum: `{}`",
                    name
                ));
                let (file, range) = node.get_file_and_range();
                labels.push(Label::secondary(file, range));
            }
            Error::UnqualifiedEnumNeedsAnnotation { node } => {
                diagnostic = diagnostic.with_message(
                    "Can't infer which enum this variant belongs to. Try adding an annotation.",
                );
                let (file, range) = node.get_file_and_range();
                labels.push(Label::secondary(file, range));
            }
            Error::InterfaceNotImplemented { ty, iface, node } => {
                diagnostic = diagnostic.with_message(format!(
                    "Interface `{}` is not implemented for type `{}`",
                    iface.name.v, ty
                ));
                let (file, range) = node.get_file_and_range();
                labels.push(Label::secondary(file, range));
            }
            Error::InterfaceImplTypeNotGeneric { node } => {
                diagnostic = diagnostic.with_message(
                    "Interface cannot be implemented for this type unless it is fully generic.",
                );
                let (file, range) = node.get_file_and_range();
                labels.push(Label::secondary(file, range));
            }
            Error::NotInLoop { node } => {
                diagnostic = diagnostic.with_message("This statement must be in a loop");
                let (file, range) = node.get_file_and_range();
                labels.push(Label::secondary(file, range));
            }
            Error::CantReturnHere { node } => {
                diagnostic = diagnostic.with_message("Can't put a return statement here");
                let (file, range) = node.get_file_and_range();
                labels.push(Label::secondary(file, range));
            }
            Error::NonexhaustiveMatch { node, missing } => {
                diagnostic =
                    diagnostic.with_message("This match expression doesn't cover every case");
                let (file, range) = node.get_file_and_range();
                labels.push(Label::secondary(file, range));

                notes.push("The following cases are missing:".to_string());
                for pat in missing {
                    notes.push(format!("\t`{pat}`\n"));
                }
            }
            Error::RedundantArms {
                node,
                redundant_arms,
            } => {
                diagnostic = diagnostic.with_message("This match expression has redundant cases");
                let (file, range) = node.get_file_and_range();
                labels.push(Label::secondary(file, range));

                notes.push("Try removing these cases:".to_string());
                for pat_id in redundant_arms {
                    let (file, range) = get_file_and_range(pat_id);
                    labels.push(Label::secondary(file, range));
                }
            }
            #[cfg(not(feature = "ffi"))]
            Error::FfiNotEnabled(node) => {
                let (file, range) = node.get_file_and_range();
                diagnostic = diagnostic.with_message("Foreign functions are not enabled");
                labels.push(Label::secondary(file, range))
            }
        };

        diagnostic = diagnostic.with_labels(labels);
        diagnostic = diagnostic.with_notes(notes);

        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();

        term::emit(&mut writer.lock(), &config, files, &diagnostic).unwrap();
    }
}

fn handle_reason(
    ty: &PotentialType,
    reason: &Reason,
    labels: &mut Vec<Label<FileId>>,
    notes: &mut Vec<String>,
) {
    match reason {
        Reason::Builtin(builtin) => {
            notes.push(format!("the builtin function `{}`", builtin.name()));
        }
        Reason::Node(node) => {
            let (file, range) = node.get_file_and_range();
            labels.push(Label::secondary(file, range).with_message("the term"));
        }
        Reason::Annotation(node) => {
            let (file, range) = node.get_file_and_range();
            labels.push(Label::secondary(file, range).with_message("this type annotation"));
        }
        Reason::Literal(node) => {
            let (file, range) = node.get_file_and_range();
            labels.push(Label::secondary(file, range).with_message(format!("`{}` literal", ty)));
        }
        Reason::BinopLeft(node) => {
            let (file, range) = node.get_file_and_range();
            labels.push(Label::secondary(file, range).with_message("the left operand of operator"));
        }
        Reason::BinopRight(node) => {
            let (file, range) = node.get_file_and_range();
            labels
                .push(Label::secondary(file, range).with_message("the right operand of operator"));
        }
        Reason::BinopOut(node) => {
            let (file, range) = node.get_file_and_range();
            labels.push(Label::secondary(file, range).with_message("the output of operator"));
        }
        Reason::VariantNoData(_prov) => {
            notes.push("the data of some enum variant".to_string());
        }
        Reason::WhileLoopBody(node) => {
            let (file, range) = node.get_file_and_range();
            labels.push(Label::secondary(file, range).with_message("the body of this while loop"));
        }
        Reason::IfWithoutElse(node) => {
            let (file, range) = node.get_file_and_range();
            labels.push(Label::secondary(file, range).with_message("this if expression"));
        }
        Reason::IndexAccess => {
            notes.push("array index access".to_string());
        }
    }
}

fn add_detail_for_decl(
    ctx: &StaticsContext,
    labels: &mut Vec<Label<u32>>,
    notes: &mut Vec<String>,
    decl: &Declaration,
    message: &str,
) {
    // TODO: this is hacky
    if add_detail_for_decl_node(ctx, labels, decl, message) {
        return;
    }
    match decl {
        Declaration::FreeFunction(..)
        | Declaration::HostFunction(..)
        | Declaration::_ForeignFunction { .. }
        | Declaration::InterfaceDef(..)
        | Declaration::InterfaceMethod { .. }
        | Declaration::MemberFunction { .. }
        | Declaration::Enum(_)
        | Declaration::EnumVariant { .. }
        | Declaration::Struct(..)
        | Declaration::Polytype(..)
        | Declaration::Var(..) => {}
        Declaration::Builtin(builtin) => notes.push(format!(
            "`{}` is a builtin operation and cannot be re-declared",
            builtin.name()
        )),
        Declaration::Array => {
            notes.push("`array` is a builtin type and cannot be re-declared".to_string())
        }
    };
}

fn add_detail_for_decl_node(
    _ctx: &StaticsContext,
    labels: &mut Vec<Label<u32>>,
    decl: &Declaration,
    message: &str,
) -> bool {
    let node = match decl {
        Declaration::FreeFunction(func_def, _) => func_def.name.node(),
        Declaration::HostFunction(func_decl, _) => func_decl.name.node(),
        Declaration::_ForeignFunction { decl, .. } => decl.name.node(),
        Declaration::InterfaceDef(interface_decl) => interface_decl.name.node(),
        Declaration::InterfaceMethod { iface_def, .. } => iface_def.name.node(),
        Declaration::MemberFunction { func } => func.name.node(),
        Declaration::Enum(enum_def) => enum_def.name.node(),
        Declaration::EnumVariant { enum_def, variant } => {
            enum_def.variants[*variant as usize].node()
        }
        Declaration::Struct(struct_def) => struct_def.name.node(),
        Declaration::Polytype(polytype) => polytype.name.node(),

        Declaration::Var(ast_node) => ast_node.clone(),
        Declaration::Builtin(_) | Declaration::Array => return false,
    };
    let (file, range) = node.get_file_and_range();
    labels.push(Label::secondary(file, range).with_message(message));
    true
}

impl AstNode {
    fn get_file_and_range(&self) -> (FileId, Range<usize>) {
        let loc = self.location();
        (loc.file_id, loc.range())
    }
}

use codespan_reporting::diagnostic::Label as CsLabel;
pub(crate) fn _print_node(ctx: &StaticsContext, node: AstNode) {
    let (file, range) = node.get_file_and_range();

    let diagnostic = Diagnostic::note().with_labels(vec![CsLabel::secondary(file, range)]);

    let writer = StandardStream::stderr(ColorChoice::Always);
    let config = codespan_reporting::term::Config::default();

    term::emit(&mut writer.lock(), &config, &ctx._files, &diagnostic).unwrap();
}
