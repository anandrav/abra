use crate::FileProvider;
use crate::ast::{
    AstNode, EnumDef, FileAst, FileDatabase, FileId, FuncDecl, FuncDef, InterfaceDecl,
    InterfaceImpl, NodeId, Polytype, StructDef, TypeKind,
};
use crate::builtin::Builtin;
use resolve::{resolve, scan_declarations};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Display, Formatter};
use std::path::PathBuf;
use std::rc::Rc;
use typecheck::{
    ConstraintReason, PotentialType, Reason, SolvedType, TypeKey, TypeVar, fmt_conflicting_types,
    solve_types,
};
mod pat_exhaustiveness;
mod resolve;
pub(crate) mod typecheck;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use pat_exhaustiveness::{DeconstructedPat, check_pattern_exhaustiveness_and_usefulness};
pub use typecheck::Monotype;
pub(crate) use typecheck::Prov as TypeProv;
pub(crate) use typecheck::SolvedType as Type;
pub(crate) use typecheck::ty_fits_impl_ty;

pub(crate) struct StaticsContext {
    // effects
    _files: FileDatabase,
    _file_provider: Box<dyn FileProvider>,

    pub(crate) global_namespace: Namespace,
    // This maps any identifier in the program to the declaration it resolves to.
    pub(crate) resolution_map: HashMap<NodeId, Declaration>,

    // BOOKKEEPING

    // most recent loops while traversing AST
    pub(crate) loop_stack: Vec<Option<NodeId>>,
    // most recent function return type while traversing AST
    pub(crate) func_ret_stack: Vec<TypeProv>,

    // map from interface name to list of its implementations
    pub(crate) interface_impls: HashMap<Rc<InterfaceDecl>, Vec<Rc<InterfaceImpl>>>,

    // string constants (for bytecode translation)
    pub(crate) string_constants: HashMap<String, usize>,
    // dylibs (for bytecode translation)
    pub(crate) dylib_to_funcs: BTreeMap<PathBuf, BTreeSet<String>>, // TODO: don't use a BTreeMap just sort at the end
    // host functions
    pub(crate) host_funcs: BTreeMap<String, u16>, // TODO: don't use a BTreeMap

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
            global_namespace: Default::default(),
            resolution_map: Default::default(),
            loop_stack: Default::default(),
            func_ret_stack: Default::default(),
            interface_impls: Default::default(),
            string_constants: Default::default(),
            dylib_to_funcs: Default::default(),
            host_funcs: Default::default(),
            unifvars: Default::default(),
            unifvars_constrained_to_interfaces: Default::default(),
            errors: Default::default(),
        };

        ctx.string_constants.entry("\n".into()).or_insert(0);
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
    pub(crate) declarations: HashMap<String, Declaration>,
    pub(crate) namespaces: HashMap<String, Rc<Namespace>>,
}

impl Namespace {
    pub fn new() -> Self {
        Self::default()
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
    Enum(Rc<EnumDef>),
    EnumVariant {
        enum_def: Rc<EnumDef>,
        variant: u16,
    },
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
    // pattern matching exhaustiveness check
    NonexhaustiveMatch {
        node: AstNode,
        missing: Vec<DeconstructedPat>,
    },
    RedundantArms {
        node: AstNode,
        redundant_arms: Vec<AstNode>,
    },
}

// main function that performs typechecking (as well as name resolution beforehand)
pub(crate) fn analyze(
    file_asts: &Vec<Rc<FileAst>>,
    files: &FileDatabase,
    file_provider: Box<dyn FileProvider>,
) -> Result<StaticsContext, String> {
    let mut ctx = StaticsContext::new(files.clone(), file_provider); // TODO: to_owned necessary?

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
            Error::UnresolvedIdentifier { node } => {
                let (file, range) = get_file_and_range(node);
                diagnostic = diagnostic.with_message("Could not resolve identifier");
                labels.push(Label::secondary(file, range))
            }
            Error::UnconstrainedUnifvar { node } => {
                let (file, range) = get_file_and_range(node);
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
                    let (file, range) = get_file_and_range(node);
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
                    let (file, range) = get_file_and_range(node);
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
                    let (file, range) = get_file_and_range(node);
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
                diagnostic = diagnostic.with_message("Can't perform member access without knowing type. Try adding a type annotation.");
                let (file, range) = get_file_and_range(node);
                labels.push(Label::secondary(file, range));
            }
            Error::UnqualifiedEnumNeedsAnnotation { node } => {
                diagnostic = diagnostic.with_message(
                    "Can't infer which enum this variant belongs to. Try adding an annotation.",
                );
                let (file, range) = get_file_and_range(node);
                labels.push(Label::secondary(file, range));
            }
            Error::InterfaceNotImplemented { ty, iface, node } => {
                diagnostic = diagnostic.with_message(format!(
                    "Interface `{}` is not implemented for type `{}`",
                    iface.name.v, ty
                ));
                let (file, range) = get_file_and_range(node);
                labels.push(Label::secondary(file, range));
            }
            Error::InterfaceImplTypeNotGeneric { node } => {
                diagnostic = diagnostic.with_message(
                    "Interface cannot be implemented for this type unless it is fully generic.",
                );
                let (file, range) = get_file_and_range(node);
                labels.push(Label::secondary(file, range));
            }
            Error::NotInLoop { node } => {
                diagnostic = diagnostic.with_message("This statement must be in a loop");
                let (file, range) = get_file_and_range(node);
                labels.push(Label::secondary(file, range));
            }
            Error::NonexhaustiveMatch { node, missing } => {
                diagnostic =
                    diagnostic.with_message("This match expression doesn't cover every case");
                let (file, range) = get_file_and_range(node);
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
                let (file, range) = get_file_and_range(node);
                labels.push(Label::secondary(file, range));

                notes.push("Try removing these cases:".to_string());
                for pat_id in redundant_arms {
                    let (file, range) = get_file_and_range(pat_id);
                    labels.push(Label::secondary(file, range));
                }
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
    // TODO: this is duplicated
    let get_file_and_range = |node: &AstNode| {
        // dbg!(id);
        let span = node.location();
        (span.file_id, span.range())
    };
    match reason {
        Reason::Builtin(builtin) => {
            notes.push(format!("the builtin function `{}`", builtin.name()));
        }
        Reason::Node(id) => {
            let (file, range) = get_file_and_range(id);
            labels.push(Label::secondary(file, range).with_message("the term"));
        }
        Reason::Annotation(id) => {
            let (file, range) = get_file_and_range(id);
            labels.push(Label::secondary(file, range).with_message("this type annotation"));
        }
        Reason::Literal(id) => {
            let (file, range) = get_file_and_range(id);
            labels.push(Label::secondary(file, range).with_message(format!("`{}` literal", ty)));
        }
        Reason::BinopLeft(id) => {
            let (file, range) = get_file_and_range(id);
            labels.push(Label::secondary(file, range).with_message("the left operand of operator"));
        }
        Reason::BinopRight(id) => {
            let (file, range) = get_file_and_range(id);
            labels
                .push(Label::secondary(file, range).with_message("the right operand of operator"));
        }
        Reason::BinopOut(id) => {
            let (file, range) = get_file_and_range(id);
            labels.push(Label::secondary(file, range).with_message("the output of operator"));
        }
        Reason::VariantNoData(_prov) => {
            notes.push("the data of some enum variant".to_string());
        }
        Reason::WhileLoopBody(id) => {
            let (file, range) = get_file_and_range(id);
            labels.push(Label::secondary(file, range).with_message("the body of this while loop"));
        }
        Reason::IfWithoutElse(id) => {
            let (file, range) = get_file_and_range(id);
            labels.push(Label::secondary(file, range).with_message("this if expression"));
        }
        Reason::IndexAccess => {
            notes.push("array index access".to_string());
        }
    }
}

use codespan_reporting::diagnostic::Label as CsLabel;
// TODO: This is duplicated
pub(crate) fn _print_node(ctx: &StaticsContext, node: AstNode) {
    let get_file_and_range = |node: &AstNode| {
        let span = node.location();
        (span.file_id, span.range())
    };

    let (file, range) = get_file_and_range(&node);

    let diagnostic = Diagnostic::note().with_labels(vec![CsLabel::secondary(file, range)]);

    let writer = StandardStream::stderr(ColorChoice::Always);
    let config = codespan_reporting::term::Config::default();

    term::emit(&mut writer.lock(), &config, &ctx._files, &diagnostic).unwrap();
}
