use crate::ast::{
    EnumDef, FileAst, ForeignFuncDecl, FuncDef, Identifier, InterfaceDecl, InterfaceImpl, NodeId,
    NodeMap, Polytype, Sources, StructDef, TypeKind,
};
use crate::builtin::Builtin;
use crate::effects::EffectDesc;
use codespan_reporting::term;
use resolve::{resolve, scan_declarations};
use std::collections::{BTreeSet, HashMap};
use std::fmt::{self, Display, Formatter, Write};
use std::path::PathBuf;
use std::rc::Rc;
use typecheck::{
    fmt_conflicting_types, generate_constraints_file, result_of_constraint_solving,
    ConstraintReason, PotentialType, Reason, SolvedType, TypeKey, TypeVar,
};
mod pat_exhaustiveness;
mod resolve;
pub(crate) mod typecheck;
pub(crate) use typecheck::ty_fits_impl_ty;
// TODO: Provs are an implementation detail, they should NOT be exported
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::{SimpleFile, SimpleFiles};
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use pat_exhaustiveness::{check_pattern_exhaustiveness_and_usefulness, DeconstructedPat};
pub use typecheck::Monotype;
pub(crate) use typecheck::Prov as TypeProv;
pub(crate) use typecheck::SolvedType as Type;

#[derive(Default, Debug)]
pub(crate) struct StaticsContext {
    // effects
    effects: Vec<EffectDesc>,
    _node_map: NodeMap,
    _sources: Sources,

    pub(crate) global_namespace: Namespace,
    // This maps any identifier in the program to the declaration it resolves to.
    pub(crate) resolution_map: HashMap<NodeId, Declaration>,

    // BOOKKEEPING

    // map from interface name to list of its implementations
    pub(crate) interface_impls: HashMap<Rc<InterfaceDecl>, Vec<Rc<InterfaceImpl>>>,

    // string constants (for bytecode translation)
    pub(crate) string_constants: HashMap<String, usize>,
    // dylibs (for bytecode translation)
    // pub(crate) dylibs: BTreeSet<PathBuf>,
    pub(crate) dylib_to_funcs: HashMap<PathBuf, BTreeSet<String>>,

    // TYPE CHECKING

    // unification variables (skolems) which must be solved
    pub(crate) unifvars: HashMap<TypeProv, TypeVar>,

    // ERRORS
    errors: Vec<Error>,
}

impl StaticsContext {
    fn new(effects: Vec<EffectDesc>, node_map: NodeMap, sources: Sources) -> Self {
        let mut ctx = Self {
            effects,
            _node_map: node_map,
            _sources: sources,
            ..Default::default()
        };

        // TODO: this string constant needs to come from builtins, not be hardcoded
        ctx.string_constants.entry("\n".into()).or_insert(0);
        ctx
    }

    pub(crate) fn solution_of_node(&self, id: NodeId) -> Option<SolvedType> {
        let prov = TypeProv::Node(id);
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Declaration {
    FreeFunction(Rc<FuncDef>, String),
    ForeignFunction {
        decl: Rc<ForeignFuncDecl>,
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
    ForeignType(Identifier),
    Array,
    Polytype(Rc<Polytype>),
    Builtin(Builtin),
    Effect(u16),
    Var(NodeId),
}

#[derive(Debug)]
pub(crate) enum Error {
    // resolution phase
    UnboundVariable {
        node_id: NodeId,
    },
    // typechecking phase
    UnconstrainedUnifvar {
        node_id: NodeId,
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
        node_id: NodeId,
    },
    // pattern matching exhaustiveness check
    NonexhaustiveMatch {
        expr_id: NodeId,
        missing: Vec<DeconstructedPat>,
    },
    RedundantArms {
        expr_id: NodeId,
        redundant_arms: Vec<NodeId>,
    },
}

// main function that performs typechecking (as well as name resolution beforehand)
pub(crate) fn analyze(
    effects: &[EffectDesc],
    files: &Vec<Rc<FileAst>>,
    node_map: &NodeMap,
    sources: &Sources,
) -> Result<StaticsContext, String> {
    let mut ctx = StaticsContext::new(effects.to_owned(), node_map.clone(), sources.clone()); // TODO: to_owned necessary?

    // scan declarations across all files
    scan_declarations(&mut ctx, files.clone());

    // resolve all imports and identifiers
    resolve(&mut ctx, files.clone());

    // typechecking
    for file in files {
        generate_constraints_file(file.clone(), &mut ctx);
    }
    result_of_constraint_solving(&mut ctx);

    // pattern exhaustiveness and usefulness checking
    check_pattern_exhaustiveness_and_usefulness(&mut ctx, files);
    check_errors(&ctx, node_map, sources)?;

    Ok(ctx)
}

pub(crate) fn check_errors(
    ctx: &StaticsContext,
    node_map: &NodeMap,
    sources: &Sources,
) -> Result<(), String> {
    if ctx.errors.is_empty() {
        return Ok(());
    }

    for error in &ctx.errors {
        error.show(ctx, node_map, sources);
    }

    Err("Failed to compile.".to_string())
}

// TODO: reduce code duplication for displaying error messages, types
impl Error {
    fn show(&self, ctx: &StaticsContext, node_map: &NodeMap, sources: &Sources) {
        // TODO: Make your own files database. Make it implement the Files trait from codespan-reporting
        let mut files = SimpleFiles::new();
        let mut filename_to_id = HashMap::<String, usize>::new();
        for (filename, source) in sources.filename_to_source.iter() {
            let id = files.add(filename, source);
            filename_to_id.insert(filename.clone(), id);
        }

        let mut diagnostic = Diagnostic::error();
        let mut labels = Vec::new();
        let mut notes = Vec::new();

        // get rid of this after making our own file database
        let get_file_and_range = |id: &NodeId| {
            let span = node_map.get(id).unwrap().span();
            (filename_to_id[&span.filename], span.range())
        };

        match self {
            Error::UnboundVariable { node_id } => {
                let (file, range) = get_file_and_range(node_id);
                diagnostic = diagnostic.with_message("This variable is unbound");
                labels.push(Label::secondary(file, range))
            }
            Error::UnconstrainedUnifvar { node_id } => {
                let (file, range) = get_file_and_range(node_id);
                diagnostic = diagnostic.with_message("Can't solve type. Try adding an annotation");
                labels.push(Label::secondary(file, range))
            }
            Error::ConflictingUnifvar { types } => {
                diagnostic = diagnostic.with_message("Conflicting types");

                let mut type_conflict: Vec<PotentialType> = types.values().cloned().collect();
                type_conflict.sort_by_key(|ty| ty.reasons().borrow().len());

                let mut conflicting_types_str = String::new();
                fmt_conflicting_types(&type_conflict, &mut conflicting_types_str).unwrap();
                notes.push(conflicting_types_str);
                for ty in type_conflict {
                    let reasons = ty.reasons().borrow();
                    for reason in reasons.iter() {
                        handle_reason(
                            &ty,
                            reason,
                            node_map,
                            &filename_to_id,
                            &mut labels,
                            &mut notes,
                        );
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
                        .with_message(format!("conflicting types `{}` and `{}`", ty2, ty1));

                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(
                        ty2,
                        reason2,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(
                        ty1,
                        reason1,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                }
                ConstraintReason::BinaryOperandsMustMatch => {
                    diagnostic = diagnostic.with_message("Operands must have the same type");
                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(
                        ty2,
                        reason2,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(
                        ty1,
                        reason1,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                }
                ConstraintReason::IfElseBodies => {
                    diagnostic =
                        diagnostic.with_message("Branches of if-else expression do not match");
                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(
                        ty2,
                        reason2,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(
                        ty1,
                        reason1,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                }
                ConstraintReason::LetStmtAnnotation => {
                    diagnostic = diagnostic.with_message("Variable and annotation do not match");
                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(
                        ty2,
                        reason2,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(
                        ty1,
                        reason1,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                }
                ConstraintReason::LetStmtLhsRhs => {
                    diagnostic = diagnostic.with_message("Variable and assignment do not match");
                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(
                        ty2,
                        reason2,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(
                        ty1,
                        reason1,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                }
                ConstraintReason::MatchScrutinyAndPattern => {
                    notes.push("type conflict due to empty block is void".to_string());
                }
                ConstraintReason::FuncCall => {
                    diagnostic = diagnostic.with_message("Wrong argument type");
                    let provs2 = ty2.reasons().borrow();
                    let reason2 = provs2.iter().next().unwrap();
                    handle_reason(
                        ty2,
                        reason2,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(
                        ty1,
                        reason1,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                }
                ConstraintReason::Condition => {
                    diagnostic = diagnostic.with_message(format!(
                        "Type conflict: condition must be a `bool` but got `{}`\n",
                        ty1
                    ));

                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(
                        ty1,
                        reason1,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                }
                ConstraintReason::BinaryOperandBool => {
                    diagnostic = diagnostic.with_message(format!(
                        "Type conflict: Operand must be `bool` but got `{}`\n",
                        ty1
                    ));

                    let provs1 = ty1.reasons().borrow();
                    let reason1 = provs1.iter().next().unwrap();
                    handle_reason(
                        ty1,
                        reason1,
                        node_map,
                        &filename_to_id,
                        &mut labels,
                        &mut notes,
                    );
                }
                ConstraintReason::EmptyBlock => {
                    notes.push("type conflict due to empty block is void".to_string());
                }
                ConstraintReason::IndexAccess => {
                    notes.push("type conflict due to array index is int".to_string());
                }
            },
            Error::MemberAccessNeedsAnnotation { node_id } => {
                diagnostic = diagnostic.with_message("Can't perform member access without knowing type. Try adding a type annotation.");
                let (file, range) = get_file_and_range(node_id);
                labels.push(Label::secondary(file, range));
            }
            Error::NonexhaustiveMatch { expr_id, missing } => {
                diagnostic =
                    diagnostic.with_message("This match expression doesn't cover every case");
                let (file, range) = get_file_and_range(expr_id);
                labels.push(Label::secondary(file, range));

                notes.push("The following cases are missing:".to_string());
                for pat in missing {
                    notes.push(format!("\t`{pat}`\n"));
                }
            }
            Error::RedundantArms {
                expr_id,
                redundant_arms,
            } => {
                diagnostic = diagnostic.with_message("This match expression has redundant cases");
                let (file, range) = get_file_and_range(expr_id);
                labels.push(Label::secondary(file, range));

                notes.push("Try removing these cases:".to_string());
                for pat_id in redundant_arms {
                    let (file, range) = get_file_and_range(pat_id);
                    labels.push(Label::secondary(file, range));
                }
            }
        };

        diagnostic = diagnostic.with_labels(labels);

        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();

        term::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();
    }
}

fn handle_reason(
    ty: &PotentialType,
    reason: &Reason,
    node_map: &NodeMap,
    filename_to_id: &HashMap<String, usize>,
    labels: &mut Vec<Label<usize>>,
    notes: &mut Vec<String>,
) {
    // get rid of this after making our own file database
    let get_file_and_range = |id: &NodeId| {
        let span = node_map.get(id).unwrap().span();
        (filename_to_id[&span.filename], span.range())
    };
    match reason {
        Reason::Builtin(builtin) => {
            notes.push(format!("the builtin function `{}`", builtin.name()));
        }
        Reason::Effect(id) => {
            notes.push(format!("the effect `{}`", id));
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
            labels.push(
                Label::secondary(file, range).with_message(format!("`{}` literal", ty.to_string())),
            );
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
