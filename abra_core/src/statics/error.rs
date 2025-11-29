use super::Error;
use super::PolytypeDeclaration;
use super::{Declaration, FuncResolutionKind};
use crate::ast::{AstNode, FileDatabase, FileId};
use crate::statics::typecheck::{ConstraintReason, PotentialType, Reason, fmt_conflicting_types};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{Buffer, ColorChoice, StandardStream};

impl Error {
    fn make_diagnostic(&self) -> Diagnostic<FileId> {
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
            Error::Generic { msg, node } => {
                let (file, range) = node.get_file_and_range();
                diagnostic = diagnostic.with_message(msg);
                labels.push(Label::secondary(file, range))
            }
            Error::UnrecognizedToken(file, index) => {
                diagnostic = diagnostic.with_message("Unrecognized token");
                labels.push(Label::secondary(*file, *index..index + 1).with_message("here"));
            }
            Error::UnexpectedToken(file, expected, found, found_span) => {
                diagnostic = diagnostic.with_message("Unexpected token");
                labels.push(
                    Label::secondary(*file, found_span.lo..found_span.hi)
                        .with_message(format!("Found `{found}` when expecting `{expected}`")),
                );
            }
            Error::RanOutOfTokens(file) => {
                diagnostic = diagnostic.with_message("Ran out of tokens while parsing"); // TODO: while parsing what? Which file? Need more context.
            }
            Error::Parse(msg) => {
                diagnostic = diagnostic.with_message(msg);
            }
            Error::NameClash {
                name,
                original,
                new,
            } => {
                diagnostic =
                    diagnostic.with_message(format!("`{name}` was declared more than once"));
                add_detail_for_decl(&mut labels, &mut notes, original, "first declared here");
                add_detail_for_decl(&mut labels, &mut notes, new, "then declared here");
            }
            Error::UnresolvedIdentifier { node } => {
                let (file, range) = node.get_file_and_range();
                diagnostic = diagnostic.with_message("Could not resolve identifier");
                labels.push(Label::secondary(file, range))
            }
            Error::UnresolvedMemberFunction {
                receiver_node,
                memfn_node,
                ty,
            } => {
                diagnostic = diagnostic
                    .with_message(format!("Could not resolve member function for type: {ty}"));
                let (file, range) = receiver_node.get_file_and_range();
                labels.push(Label::secondary(file, range));
                let (file, range) = memfn_node.get_file_and_range();
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
                type_conflict.sort_by_key(|ty| ty.reasons().len());

                let mut conflicting_types_str = String::new();
                fmt_conflicting_types(&type_conflict, &mut conflicting_types_str).unwrap();
                notes.push(conflicting_types_str);
                for ty in type_conflict {
                    let reasons = ty.reasons().inner.borrow();
                    for reason in reasons.iter() {
                        handle_reason(&ty, reason.clone(), &mut labels, &mut notes);
                    }
                }
            }
            Error::TypeConflict {
                ty1,
                ty2,
                constraint_reason,
            } => match constraint_reason {
                ConstraintReason::None => {
                    diagnostic =
                        diagnostic.with_message(format!("Conflicting types `{ty2}` and `{ty1}`"));

                    let reason2 = ty2.reasons().first();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let reason1 = ty1.reasons().first();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::BinaryOperandsMustMatch(node) => {
                    diagnostic = diagnostic.with_message("Operands must have the same type");
                    let (file, range) = node.get_file_and_range();
                    labels.push(Label::secondary(file, range).with_message("operator"));

                    let reason2 = ty2.reasons().first();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let reason1 = ty1.reasons().first();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::IfElseBodies => {
                    diagnostic =
                        diagnostic.with_message("Branches of if-else expression do not match");
                    let reason2 = ty2.reasons().first();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let reason1 = ty1.reasons().first();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::LetStmtAnnotation => {
                    diagnostic = diagnostic.with_message("Variable and annotation do not match");
                    let reason2 = ty2.reasons().first();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let reason1 = ty1.reasons().first();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::LetSetLhsRhs => {
                    diagnostic = diagnostic.with_message("Variable and assignment do not match");
                    let reason2 = ty2.reasons().first();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let reason1 = ty1.reasons().first();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::MatchScrutinyAndPattern => {
                    diagnostic = diagnostic.with_message(format!(
                        "Match expression input has type `{ty1}`, but case has type `{ty2}`"
                    ));
                    let reason2 = ty2.reasons().first();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let reason1 = ty1.reasons().first();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::FuncCall(node) => {
                    diagnostic = diagnostic.with_message("Wrong argument type");
                    let (file, range) = node.get_file_and_range();
                    labels.push(Label::secondary(file, range).with_message("function call"));

                    let reason2 = ty2.reasons().first();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let reason1 = ty1.reasons().first();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::ReturnValue => {
                    diagnostic = diagnostic.with_message("Return value has wrong type");

                    let reason2 = ty2.reasons().first();
                    handle_reason(ty2, reason2, &mut labels, &mut notes);
                    let reason1 = ty1.reasons().first();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::Condition => {
                    diagnostic = diagnostic
                        .with_message(format!("Condition must be a `bool` but got `{ty1}`\n"));

                    let reason1 = ty1.reasons().first();
                    handle_reason(ty1, reason1, &mut labels, &mut notes);
                }
                ConstraintReason::BinaryOperandBool(node) => {
                    diagnostic = diagnostic
                        .with_message(format!("Operand must be `bool` but got `{ty1}`\n"));
                    let (file, range) = node.get_file_and_range();
                    labels.push(Label::secondary(file, range).with_message("boolean operator"));

                    let reason1 = ty1.reasons().first();
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
            Error::MustExtendType { node } => {
                diagnostic = diagnostic.with_message("Must extend a type.".to_string());
                let (file, range) = node.get_file_and_range();
                labels.push(Label::secondary(file, range));
            }
            Error::MemberFunctionMissingFirstSelfArgument { node } => {
                diagnostic = diagnostic
                    .with_message("First argument of member function must be `self`".to_string());
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

        diagnostic
    }

    pub fn emit(&self, files: &FileDatabase) {
        let diagnostic = self.make_diagnostic();
        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = term::Config::default();

        term::emit_to_write_style(&mut writer.lock(), &config, files, &diagnostic).unwrap();
    }

    pub fn to_string(&self, files: &FileDatabase, ansi: bool) -> String {
        let diagnostic = self.make_diagnostic();
        let mut buffer = if ansi {
            Buffer::ansi()
        } else {
            Buffer::no_color()
        };
        let config = term::Config::default();

        term::emit_to_write_style(&mut buffer, &config, files, &diagnostic).unwrap();
        String::from_utf8(buffer.into_inner()).unwrap()
    }
}

fn handle_reason(
    ty: &PotentialType,
    reason: Reason,
    labels: &mut Vec<Label<FileId>>,
    notes: &mut Vec<String>,
) {
    match reason {
        Reason::Builtin(builtin) => {
            notes.push(format!("the builtin function `{}`", builtin.name()));
        }
        Reason::Node(node) => {
            let (file, range) = node.get_file_and_range();
            labels.push(Label::secondary(file, range).with_message(format!("`{ty}`")));
        }
        Reason::Annotation(node) => {
            let (file, range) = node.get_file_and_range();
            labels.push(Label::secondary(file, range).with_message("this type annotation"));
        }
        Reason::Literal(node) => {
            let (file, range) = node.get_file_and_range();
            labels.push(Label::secondary(file, range).with_message(format!("`{ty}` literal")));
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
        Reason::IndexAccess => {
            notes.push("array index access".to_string());
        }
    }
}

fn add_detail_for_decl(
    labels: &mut Vec<Label<u32>>,
    notes: &mut Vec<String>,
    decl: &Declaration,
    message: &str,
) {
    // TODO: this is hacky
    if add_detail_for_decl_node(labels, decl, message) {
        return;
    }
    match decl {
        Declaration::FreeFunction { .. }
        | Declaration::InterfaceDef(..)
        | Declaration::InterfaceMethod { .. }
        | Declaration::MemberFunction { .. }
        | Declaration::Enum(_)
        | Declaration::EnumVariant { .. }
        | Declaration::Struct(..)
        | Declaration::Polytype(..)
        | Declaration::Var(..) => {}
        Declaration::InterfaceOutputType { .. } => unimplemented!(),
        Declaration::Builtin(builtin) => notes.push(format!(
            "`{}` is a builtin operation and cannot be re-declared",
            builtin.name()
        )),
        Declaration::Array | Declaration::BuiltinType(_) => {
            notes.push("cannot redeclare a builtin type".to_string())
        }
    };
}

fn add_detail_for_decl_node(
    labels: &mut Vec<Label<u32>>,
    decl: &Declaration,
    message: &str,
) -> bool {
    let node = match decl {
        Declaration::FreeFunction(FuncResolutionKind::Ordinary(func_def)) => func_def.name.node(),
        Declaration::FreeFunction(FuncResolutionKind::Host(func_decl)) => func_decl.name.node(),
        Declaration::FreeFunction(FuncResolutionKind::_Foreign { decl, .. }) => decl.name.node(),
        Declaration::InterfaceDef(interface_decl) => interface_decl.name.node(),
        Declaration::InterfaceMethod {
            iface: iface_def, ..
        } => iface_def.name.node(),
        Declaration::MemberFunction(func_def) => func_def.name.node(),
        Declaration::Enum(enum_def) => enum_def.name.node(),
        Declaration::EnumVariant {
            e: enum_def,
            variant,
        } => enum_def.variants[*variant].node(),
        Declaration::Struct(struct_def) => struct_def.name.node(),
        Declaration::Polytype(polytype_decl) => match polytype_decl {
            PolytypeDeclaration::Ordinary(polyty) => polyty.name.node(),
            PolytypeDeclaration::Builtin(..) => return false,
            PolytypeDeclaration::InterfaceSelf(iface_def) => iface_def.name.node(), // TODO: this will not result in a good error message
        },

        Declaration::Var(ast_node) => ast_node.clone(),
        Declaration::InterfaceOutputType { .. } => unimplemented!(),
        Declaration::Builtin(_) | Declaration::BuiltinType(_) | Declaration::Array => return false,
    };
    let (file, range) = node.get_file_and_range();
    labels.push(Label::secondary(file, range).with_message(message));
    true
}
