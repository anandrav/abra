use std::rc::Rc;

use pest::Parser;
use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};
use pest_derive::Parser;

use crate::ast::*;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct MyParser;

// TODO: modify this to just take a single file
pub(crate) fn parse_or_err(file_id: FileId, file_data: &FileData) -> Result<Rc<FileAst>, String> {
    let pairs = get_pairs(&file_data.source)?;

    let file_ast = parse_file(pairs, file_data, file_id);
    Ok(file_ast)
}

pub(crate) fn parse_file(pairs: Pairs<Rule>, file_data: &FileData, file_id: FileId) -> Rc<FileAst> {
    let mut items = Vec::new();
    let pairs: Vec<_> = pairs.into_iter().collect();
    for pair in &pairs {
        if pair.as_rule() == Rule::EOI {
            break;
        }
        let stmt = parse_item(pair.clone(), file_id);
        items.push(stmt)
    }
    let span1: Location = Location::new(file_id, pairs.first().unwrap().as_span());
    let span2: Location = Location::new(file_id, pairs.last().unwrap().as_span());
    Rc::new(FileAst {
        items,
        // remove the .abra suffix from filename
        name: file_data.nominal_path.to_str().unwrap()
            [..file_data.nominal_path.to_str().unwrap().len() - 5]
            .to_string(),
        path: file_data.full_path.clone(),
        loc: Location {
            file_id,
            lo: span1.lo,
            hi: span2.hi,
        },
        id: NodeId::new(),
    })
}

pub(crate) fn parse_expr_pratt(pairs: Pairs<Rule>, file_id: FileId) -> Rc<Expr> {
    let pratt = PrattParser::new()
        .op(Op::infix(Rule::op_eq, Assoc::Left))
        .op(Op::infix(Rule::op_concat, Assoc::Right))
        .op(Op::infix(Rule::op_and, Assoc::Left) | Op::infix(Rule::op_or, Assoc::Left))
        .op(Op::infix(Rule::op_lt, Assoc::Left)
            | Op::infix(Rule::op_gt, Assoc::Left)
            | Op::infix(Rule::op_lte, Assoc::Left)
            | Op::infix(Rule::op_gte, Assoc::Left))
        .op(Op::infix(Rule::op_addition, Assoc::Left)
            | Op::infix(Rule::op_subtraction, Assoc::Left))
        .op(Op::infix(Rule::op_multiplication, Assoc::Left)
            | Op::infix(Rule::op_division, Assoc::Left)
            | Op::infix(Rule::op_mod, Assoc::Left))
        .op(Op::infix(Rule::op_pow, Assoc::Left))
        .op(Op::postfix(Rule::member_access)
            | Op::postfix(Rule::index_access)
            | Op::postfix(Rule::func_call));
    pratt
        .map_primary(|t| parse_expr_term(t, file_id))
        .map_prefix(|_op, _rhs| panic!("prefix operator encountered"))
        .map_postfix(|lhs, op| match op.as_rule() {
            Rule::index_access => {
                let span = Location::new(file_id, op.as_span());
                let inner: Vec<_> = op.into_inner().collect();
                let index = parse_expr_pratt(Pairs::single(inner[0].clone()), file_id);
                Rc::new(Expr {
                    kind: Rc::new(ExprKind::IndexAccess(lhs, index)),
                    loc: span,
                    id: NodeId::new(),
                })
            }
            Rule::member_access => {
                let loc = Location::new(file_id, op.as_span());
                let inner: Vec<_> = op.into_inner().collect();
                let ident = Identifier {
                    v: inner[0].as_str().to_string(),
                    loc: Location::new(file_id, inner[0].as_span()),
                    id: NodeId::new(),
                }
                .into();

                Rc::new(Expr {
                    kind: Rc::new(ExprKind::MemberAccess(lhs.clone(), ident)),
                    loc,
                    id: NodeId::new(),
                })
            }
            Rule::func_call => {
                let f = lhs;
                let span = Location::new(file_id, op.as_span());
                let inner: Vec<_> = op.into_inner().collect();
                let mut args = vec![];
                for p in &inner[0..] {
                    args.push(parse_expr_pratt(Pairs::single(p.clone()), file_id));
                }
                Rc::new(Expr {
                    kind: Rc::new(ExprKind::FuncAp(f, args)),
                    loc: span,
                    id: NodeId::new(),
                })
            }
            _ => unreachable!(),
        })
        .map_infix(|lhs, op, rhs| {
            let opcode = match op.as_rule() {
                Rule::op_eq => Some(BinaryOperator::Equal),
                Rule::op_gt => Some(BinaryOperator::GreaterThan),
                Rule::op_lt => Some(BinaryOperator::LessThan),
                Rule::op_gte => Some(BinaryOperator::GreaterThanOrEqual),
                Rule::op_lte => Some(BinaryOperator::LessThanOrEqual),
                Rule::op_addition => Some(BinaryOperator::Add),
                Rule::op_subtraction => Some(BinaryOperator::Subtract),
                Rule::op_multiplication => Some(BinaryOperator::Multiply),
                Rule::op_division => Some(BinaryOperator::Divide),
                Rule::op_pow => Some(BinaryOperator::Pow),
                Rule::op_mod => Some(BinaryOperator::Mod),
                Rule::op_and => Some(BinaryOperator::And),
                Rule::op_or => Some(BinaryOperator::Or),
                Rule::op_concat => Some(BinaryOperator::Format),
                _ => None,
            };
            match opcode {
                Some(opcode) => Rc::new(Expr {
                    kind: Rc::new(ExprKind::BinOp(lhs.clone(), opcode, rhs.clone())),
                    loc: Location::new(file_id, op.as_span()),
                    id: NodeId::new(),
                }),
                None => panic!(),
            }
        })
        .parse(pairs)
}

pub(crate) fn get_pairs(source: &str) -> Result<Pairs<Rule>, String> {
    MyParser::parse(Rule::file, source).map_err(|e| e.to_string())
}

pub(crate) fn parse_func_arg_annotation(pair: Pair<Rule>, file_id: FileId) -> ArgMaybeAnnotated {
    let rule = pair.as_rule();
    match rule {
        Rule::func_arg => {
            let inner: Vec<_> = pair.into_inner().collect();
            let name: Pair<'_, Rule> = inner[0].clone();
            let ident = Identifier {
                v: name.as_str().to_string(),
                loc: Location::new(file_id, name.as_span()),
                id: NodeId::new(),
            }
            .into();
            let annot = inner
                .get(1)
                .map(|type_pair| parse_type_term(type_pair.clone(), file_id));
            (ident, annot)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

// TODO: RENAME
pub(crate) fn parse_func_arg_annotation_mandatory(
    pair: Pair<Rule>,
    file_id: FileId,
) -> ArgAnnotated {
    let rule = pair.as_rule();
    match rule {
        Rule::func_arg_annotated => {
            let inner: Vec<_> = pair.into_inner().collect();
            let name: Pair<'_, Rule> = inner[0].clone();
            let ident = Identifier {
                v: name.as_str().to_string(),
                loc: Location::new(file_id, name.as_span()),
                id: NodeId::new(),
            }
            .into();
            let annot = parse_type_term(inner[1].clone(), file_id);
            (ident, annot)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_annotated_let_pattern(pair: Pair<Rule>, file_id: FileId) -> PatAnnotated {
    let rule = pair.as_rule();
    match rule {
        Rule::let_pattern_annotated => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pat_pair = inner[0].clone();
            let pat = parse_let_pattern(pat_pair, file_id);
            let ty = inner
                .get(1)
                .map(|type_pair| parse_type_term(type_pair.clone(), file_id));
            (pat, ty)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_func_out_annotation(pair: Pair<Rule>, file_id: FileId) -> Rc<Type> {
    let rule = pair.as_rule();
    match rule {
        Rule::func_out_annotation => {
            let inner: Vec<_> = pair.into_inner().collect();
            let type_pair = inner[0].clone();
            parse_type_term(type_pair, file_id)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_let_pattern(pair: Pair<Rule>, file_id: FileId) -> Rc<Pat> {
    let span = Location::new(file_id, pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pair = inner.first().unwrap().clone();
            parse_let_pattern(pair, file_id)
        }
        Rule::identifier => Rc::new(Pat {
            kind: Rc::new(PatKind::Binding(pair.as_str().to_owned())),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::wildcard => Rc::new(Pat {
            kind: Rc::new(PatKind::Wildcard),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::let_pattern_tuple => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pats = inner
                .iter()
                .map(|pair| parse_let_pattern(pair.clone(), file_id))
                .collect();
            Rc::new(Pat {
                kind: Rc::new(PatKind::Tuple(pats)),
                loc: span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_match_pattern(pair: Pair<Rule>, file_id: FileId) -> Rc<Pat> {
    let span = Location::new(file_id, pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::match_pattern => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pair = inner.first().unwrap().clone();
            parse_match_pattern(pair, file_id)
        }
        Rule::match_pattern_variable => Rc::new(Pat {
            kind: Rc::new(PatKind::Binding(pair.as_str()[1..].to_owned())),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::match_pattern_tuple => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pats = inner
                .iter()
                .map(|pair| parse_match_pattern(pair.clone(), file_id))
                .collect();
            Rc::new(Pat {
                kind: Rc::new(PatKind::Tuple(pats)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::match_pattern_variant_qualified => {
            let inner: Vec<_> = pair.into_inner().collect();

            let mut n = 0;
            let mut ident_segments = vec![];
            loop {
                if n < inner.len() {
                    if let Rule::identifier = inner[n].as_rule() {
                        ident_segments.push(Rc::new(Identifier {
                            v: inner[n].as_str().to_string(),
                            loc: Location::new(file_id, inner[n].as_span()),
                            id: NodeId::new(),
                        }));
                        n += 1;
                        continue;
                    }
                }
                break;
            }
            let last_ident = ident_segments.pop().unwrap();

            let pat = inner
                .get(n)
                .map(|pair| parse_match_pattern(pair.clone(), file_id));
            Rc::new(Pat {
                kind: Rc::new(PatKind::Variant(ident_segments, last_ident, pat)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::match_pattern_variant_inferred => {
            let inner: Vec<_> = pair.into_inner().collect();

            let ident = Rc::new(Identifier {
                v: inner[0].as_str().to_string(),
                loc: Location::new(file_id, inner[0].as_span()),
                id: NodeId::new(),
            });

            let pat = inner
                .get(1)
                .map(|pair| parse_match_pattern(pair.clone(), file_id));
            Rc::new(Pat {
                kind: Rc::new(PatKind::Variant(vec![], ident, pat)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::wildcard => Rc::new(Pat {
            kind: Rc::new(PatKind::Wildcard),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::literal_unit => Rc::new(Pat {
            kind: Rc::new(PatKind::Unit),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::literal_int => Rc::new(Pat {
            kind: Rc::new(PatKind::Int(pair.as_str().parse().unwrap())),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::literal_float => Rc::new(Pat {
            kind: Rc::new(PatKind::Float(pair.as_str().parse().unwrap())),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::literal_bool => Rc::new(Pat {
            kind: Rc::new(PatKind::Bool(pair.as_str().parse().unwrap())),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::literal_string => Rc::new(Pat {
            kind: Rc::new(PatKind::Str({
                let s = pair.as_str();
                // remove quotes
                s[1..s.len() - 1].to_owned()
            })),
            loc: span,
            id: NodeId::new(),
        }),
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_type_term(pair: Pair<Rule>, file_id: FileId) -> Rc<Type> {
    let span = Location::new(file_id, pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::type_poly => Rc::new(Type {
            kind: TypeKind::Poly(parse_type_poly(pair, file_id)).into(),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::identifier => {
            let ident = pair.as_str().to_owned();
            Rc::new(Type {
                kind: Rc::new(TypeKind::Named(ident)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::type_literal_unit => Rc::new(Type {
            kind: Rc::new(TypeKind::Unit),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::type_literal_int => Rc::new(Type {
            kind: Rc::new(TypeKind::Int),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::type_literal_float => Rc::new(Type {
            kind: Rc::new(TypeKind::Float),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::type_literal_bool => Rc::new(Type {
            kind: Rc::new(TypeKind::Bool),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::type_literal_string => Rc::new(Type {
            kind: Rc::new(TypeKind::Str),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::tuple_type => {
            let inner: Vec<_> = pair.into_inner().collect();
            let types = inner
                .into_iter()
                .map(|t| parse_type_term(t, file_id))
                .collect();
            Rc::new(Type {
                kind: Rc::new(TypeKind::Tuple(types)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::type_ap => {
            let inner: Vec<_> = pair.into_inner().collect();
            let name = inner[0].as_str().to_owned();
            let ident_span = Location::new(file_id, inner[0].as_span());
            let types = inner
                .into_iter()
                .skip(1)
                .map(|t| parse_type_term(t, file_id))
                .collect();
            Rc::new(Type {
                kind: Rc::new(TypeKind::NamedWithParams(
                    Identifier {
                        v: name,
                        loc: ident_span,
                        id: NodeId::new(),
                    }
                    .into(),
                    types,
                )),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::func_type => {
            let inner: Vec<_> = pair.into_inner().collect();
            let len = inner.len();
            let args: Vec<_> = inner
                .clone()
                .into_iter()
                .take(len - 1)
                .map(|t| parse_type_term(t, file_id))
                .collect();
            let ret = parse_type_term(inner.last().unwrap().clone(), file_id);
            Rc::new(Type {
                kind: Rc::new(TypeKind::Function(args, ret)),
                loc: span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", pair),
    }
}

pub(crate) fn parse_type_poly(pair: Pair<Rule>, file_id: FileId) -> Rc<Polytype> {
    let rule = pair.as_rule();
    match rule {
        Rule::type_poly => {
            let inner: Vec<_> = pair.into_inner().collect();
            let ty_name = inner[0].as_str()[1..].to_owned();
            let ty_span = Location::new(file_id, inner[0].as_span());
            let mut interfaces: Vec<Rc<Identifier>> = vec![];
            for (i, pair) in inner.iter().enumerate() {
                if i == 0 {
                    continue;
                }
                let interface = Identifier {
                    v: pair.as_str().to_owned(),
                    loc: Location::new(file_id, pair.as_span()),
                    id: NodeId::new(),
                }
                .into();
                interfaces.push(interface);
            }

            Polytype {
                name: Identifier {
                    v: ty_name,
                    loc: ty_span,
                    id: NodeId::new(),
                }
                .into(),
                iface_names: interfaces,
            }
            .into()
        }
        _ => panic!("unreachable rule {:#?}", pair),
    }
}

pub(crate) fn parse_item(pair: Pair<Rule>, file_id: FileId) -> Rc<Item> {
    let span = Location::new(file_id, pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.clone().into_inner().collect();
    match rule {
        Rule::func_def => {
            let func_def = parse_func_def(inner, file_id);
            Rc::new(Item {
                kind: Rc::new(ItemKind::FuncDef(func_def.into())),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::foreign_func_decl => {
            let mut n = 0;
            let mut args = vec![];
            let name = Identifier {
                v: inner[0].as_str().to_string(),
                loc: Location::new(file_id, inner[0].as_span()),
                id: NodeId::new(),
            }
            .into();
            n += 1;
            while let Rule::func_arg_annotated = inner[n].as_rule() {
                let pat_annotated = parse_func_arg_annotation_mandatory(inner[n].clone(), file_id);
                args.push(pat_annotated);
                n += 1;
            }

            let maybe_func_out = &inner[n];
            let ret_type = parse_func_out_annotation(maybe_func_out.clone(), file_id);

            Rc::new(Item {
                kind: Rc::new(ItemKind::ForeignFuncDecl(
                    ForeignFuncDecl {
                        name,
                        args,
                        ret_type,
                    }
                    .into(),
                )),
                loc: span,
                id: NodeId::new(),
            })
        }
        // Rule::typealias => {
        //     let ident = inner[0].as_str().to_string();
        //     let definition = parse_type_term(inner[1].clone(), file_id);
        //     Rc::new(Stmt {
        //         kind: Rc::new(StmtKind::TypeDef(Rc::new(TypeDefKind::Alias(
        //             ident, definition,
        //         )))),
        //         span,
        //         id: NodeId::new(),
        //     })
        // }
        Rule::enum_declaration => {
            let name = inner[0].as_str().to_string();
            let mut n = 1;
            let mut ty_args = vec![];
            while let Rule::type_poly = inner[n].as_rule() {
                ty_args.push(parse_type_poly(inner[n].clone(), file_id));
                n += 1;
            }
            let mut variants = vec![];
            while let Some(pair) = inner.get(n) {
                let variant = parse_variant(pair.clone(), file_id);
                variants.push(variant);
                n += 1;
            }
            Rc::new(Item {
                kind: Rc::new(ItemKind::TypeDef(Rc::new(TypeDefKind::Enum(
                    EnumDef {
                        name: Identifier {
                            v: name,
                            loc: span.clone(),
                            id: NodeId::new(),
                        }
                        .into(),
                        ty_args,
                        variants,
                    }
                    .into(),
                )))),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::struct_declaration => {
            let name = inner[0].as_str().to_string();
            let mut n = 1;
            let mut ty_args = vec![];
            while let Rule::type_poly = inner[n].as_rule() {
                ty_args.push(parse_type_poly(inner[n].clone(), file_id));
                n += 1;
            }
            let mut fields = vec![];
            while let Some(pair) = inner.get(n) {
                let field = parse_struct_field(pair.clone(), file_id);
                fields.push(Rc::new(field));
                n += 1;
            }

            let id = NodeId::new();
            Rc::new(Item {
                kind: Rc::new(ItemKind::TypeDef(Rc::new(TypeDefKind::Struct(
                    StructDef {
                        name: Identifier {
                            v: name,
                            loc: span.clone(),
                            id: NodeId::new(),
                        }
                        .into(),
                        ty_args,
                        fields,
                        id,
                    }
                    .into(),
                )))),
                loc: span,
                id,
            })
        }
        Rule::foreign_type_decl => {
            let name: String = inner[0].as_str().to_string();
            let id = NodeId::new();
            Rc::new(Item {
                kind: Rc::new(ItemKind::TypeDef(Rc::new(TypeDefKind::Foreign(
                    Identifier {
                        v: name,
                        loc: span.clone(),
                        id: NodeId::new(),
                    }
                    .into(),
                )))),
                loc: span,
                id,
            })
        }
        Rule::interface_declaration => {
            let name: String = inner[0].as_str().to_string();
            let mut n = 1;
            let mut props = vec![];
            while let Some(pair) = inner.get(n) {
                let method = parse_interface_method(pair.clone(), file_id);
                props.push(Rc::new(method));
                n += 1;
            }
            Rc::new(Item {
                kind: ItemKind::InterfaceDef(
                    InterfaceDecl {
                        name: Identifier {
                            v: name,
                            loc: span.clone(),
                            id: NodeId::new(),
                        }
                        .into(),
                        methods: props,
                    }
                    .into(),
                )
                .into(),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::interface_implementation => {
            let name = inner[0].as_str().to_string();
            let name_span = Location::new(file_id, inner[0].as_span());
            let typ = parse_type_term(inner[1].clone(), file_id);
            let mut n = 2;
            let mut func_defs = vec![];
            while let Some(pair) = inner.get(n) {
                let inner: Vec<_> = pair.clone().into_inner().collect();
                let func_def: Rc<FuncDef> = parse_func_def(inner, file_id).into();
                func_defs.push(func_def);
                n += 1;
            }
            let impl_id = NodeId::new();
            Rc::new(Item {
                kind: ItemKind::InterfaceImpl(
                    InterfaceImpl {
                        iface: Identifier {
                            v: name,
                            loc: name_span,
                            id: NodeId::new(),
                        }
                        .into(),
                        typ,
                        methods: func_defs,

                        id: impl_id,
                    }
                    .into(),
                )
                .into(),
                loc: span,
                id: impl_id,
            })
        }
        Rule::import => {
            let name = inner[0].as_str().to_string();
            Rc::new(Item {
                kind: ItemKind::Import(
                    Identifier {
                        v: name,
                        loc: span.clone(),
                        id: NodeId::new(),
                    }
                    .into(),
                )
                .into(),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::let_statement
        | Rule::var_statement
        | Rule::set_statement
        | Rule::expression_statement => {
            let stmt = parse_stmt(pair, file_id);
            Rc::new(Item {
                kind: ItemKind::Stmt(stmt).into(),
                loc: span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

fn parse_func_def(inner: Vec<Pair<'_, Rule>>, file_id: FileId) -> FuncDef {
    let mut n = 0;
    let mut args = vec![];
    let name = Identifier {
        v: inner[0].as_str().to_string(),
        loc: Location::new(file_id, inner[0].as_span()),
        id: NodeId::new(),
    }
    .into();
    n += 1;
    while let Rule::func_arg = inner[n].as_rule() {
        let pat_annotated = parse_func_arg_annotation(inner[n].clone(), file_id);
        args.push(pat_annotated);
        n += 1;
    }

    let maybe_func_out = &inner[n];
    let ret_type = match maybe_func_out.as_rule() {
        Rule::func_out_annotation => {
            // n += 1;
            Some(parse_func_out_annotation(maybe_func_out.clone(), file_id))
        }
        _ => None,
    };
    let body = parse_expr_pratt(Pairs::single(inner.last().unwrap().clone()), file_id);

    FuncDef {
        name,
        args,
        ret_type,
        body,
    }
}

pub(crate) fn parse_stmt(pair: Pair<Rule>, file_id: FileId) -> Rc<Stmt> {
    let span = Location::new(file_id, pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::func_def => {
            let func_def = parse_func_def(inner, file_id);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::FuncDef(func_def.into())),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::let_statement => {
            let offset = 0;
            let pat_annotated = parse_annotated_let_pattern(inner[offset].clone(), file_id);
            let expr = parse_expr_pratt(Pairs::single(inner[offset + 1].clone()), file_id);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::Let(false, pat_annotated, expr)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::var_statement => {
            let offset = 0;
            let pat_annotated = parse_annotated_let_pattern(inner[offset].clone(), file_id);
            let expr = parse_expr_pratt(Pairs::single(inner[offset + 1].clone()), file_id);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::Let(true, pat_annotated, expr)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::set_statement => {
            let expr1 = parse_expr_pratt(Pairs::single(inner[0].clone()), file_id);
            let expr2 = parse_expr_pratt(Pairs::single(inner[1].clone()), file_id);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::Set(expr1, expr2)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::expression_statement => {
            let expr = parse_expr_pratt(Pairs::single(inner[0].clone()), file_id);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::Expr(expr)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::break_statement => Rc::new(Stmt {
            kind: Rc::new(StmtKind::Break),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::continue_statement => Rc::new(Stmt {
            kind: Rc::new(StmtKind::Continue),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::return_statement => {
            let expr = parse_expr_pratt(Pairs::single(inner[0].clone()), file_id);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::Return(expr)),
                loc: span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_interface_method(pair: Pair<Rule>, file_id: FileId) -> InterfaceMethodDecl {
    let rule = pair.as_rule();
    let span = pair.as_span();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::interface_property => {
            let name = inner[0].as_str().to_string();
            let inner_loc = Location::new(file_id, inner[0].as_span());
            let ty = parse_type_term(inner[1].clone(), file_id);
            InterfaceMethodDecl {
                name: Identifier {
                    v: name,
                    loc: inner_loc,
                    id: NodeId::new(),
                }
                .into(),
                ty,
                id: NodeId::new(),
                loc: Location::new(file_id, span),
            }
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_variant(pair: Pair<Rule>, file_id: FileId) -> Rc<Variant> {
    let span = Location::new(file_id, pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::variant => {
            let name = inner[0].as_str().to_string();
            let span_ctor = Location::new(file_id, inner[0].as_span());
            let n = 1;
            // while let Rule::type_poly = inner[n].as_rule() {
            //     type_params.push(inner[n].as_str().to_string());
            //     n += 1;
            // }
            let data = if let Some(pair) = inner.get(n) {
                let data = parse_type_term(pair.clone(), file_id);
                Some(data)
            } else {
                None
            };
            Rc::new(Variant {
                ctor: Identifier {
                    v: name,
                    loc: span_ctor,
                    id: NodeId::new(),
                }
                .into(),
                data,
                loc: span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_struct_field(pair: Pair<Rule>, file_id: FileId) -> StructField {
    let span = Location::new(file_id, pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::struct_field => {
            let name = inner[0].as_str().to_string();
            let span_field = Location::new(file_id, inner[0].as_span());
            let ty = parse_type_term(inner[1].clone(), file_id);
            StructField {
                name: Identifier {
                    v: name,
                    loc: span_field,
                    id: NodeId::new(),
                }
                .into(),
                ty,
                loc: span,
                id: NodeId::new(),
            }
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_expr_term(pair: Pair<Rule>, file_id: FileId) -> Rc<Expr> {
    let span = Location::new(file_id, pair.as_span());
    let rule = pair.as_rule();
    match rule {
        /* emitting Pairs for expression and then re-running on its inner pairs is
         * necessary to be able to distinguish its inner pairs from the pairs of an adjacent,
         * but different, expression.
         * For instance, in the expression
         *          if n == 0 { 2 } else { 3 }
         * (n == 0) would be parsed as a Rule::expression, followed by two Rule::block_expressions
         * If 'n' '==' and '0' were not grouped under a Rule::expression, it would be difficult
         * to run the pratt parser on just them.
         */
        Rule::expression => parse_expr_pratt(pair.into_inner(), file_id),
        // All rules listed below should be non-operator expressions
        Rule::block_expression => {
            let inner = pair.into_inner();
            let mut statements: Vec<Rc<Stmt>> = Vec::new();
            for pair in inner {
                statements.push(parse_stmt(pair, file_id));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Block(statements)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::if_else_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let cond = parse_expr_pratt(Pairs::single(inner[0].clone()), file_id);
            let e1 = parse_expr_pratt(Pairs::single(inner[1].clone()), file_id);
            let e2 = if inner.len() == 3 {
                Some(parse_expr_pratt(Pairs::single(inner[2].clone()), file_id))
            } else {
                None
            };
            Rc::new(Expr {
                kind: Rc::new(ExprKind::If(cond, e1, e2)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::while_loop_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let cond = parse_expr_pratt(Pairs::single(inner[0].clone()), file_id);
            let e = parse_expr_pratt(Pairs::single(inner[1].clone()), file_id);
            Rc::new(Expr {
                kind: Rc::new(ExprKind::WhileLoop(cond, e)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::match_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let expr = parse_expr_pratt(Pairs::single(inner[0].clone()), file_id);
            let mut arms = vec![];
            fn parse_match_arm(pair: &Pair<Rule>, file_id: FileId) -> Rc<MatchArm> {
                let span = pair.as_span();
                let inner: Vec<_> = pair.clone().into_inner().collect();
                let pat = parse_match_pattern(inner[0].clone(), file_id);
                let expr = parse_expr_pratt(Pairs::single(inner[1].clone()), file_id);
                MatchArm {
                    pat,
                    expr,
                    loc: Location::new(file_id, span),
                    id: NodeId::new(),
                }
                .into()
            }
            for pair in &inner[1..] {
                arms.push(parse_match_arm(pair, file_id));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Match(expr, arms)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::func_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut n = 0;
            let mut args = vec![];
            while let Rule::func_arg = inner[n].as_rule() {
                let pat_annotated = parse_func_arg_annotation(inner[n].clone(), file_id);
                args.push(pat_annotated);
                n += 1;
            }

            let maybe_func_out = &inner[n];
            let ty_out = match maybe_func_out.as_rule() {
                Rule::func_out_annotation => {
                    // n += 1;
                    Some(parse_func_out_annotation(maybe_func_out.clone(), file_id))
                }
                _ => None,
            };
            let body = parse_expr_pratt(Pairs::single(inner.last().unwrap().clone()), file_id);
            Rc::new(Expr {
                kind: Rc::new(ExprKind::AnonymousFunction(args, ty_out, body)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::tuple_expr => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut exprs = vec![];
            for p in inner {
                exprs.push(parse_expr_pratt(Pairs::single(p), file_id));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Tuple(exprs)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::literal_unit => Rc::new(Expr {
            kind: Rc::new(ExprKind::Unit),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::literal_int => Rc::new(Expr {
            kind: Rc::new(ExprKind::Int(pair.as_str().parse().unwrap())),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::literal_float => Rc::new(Expr {
            kind: Rc::new(ExprKind::Float(pair.as_str().parse().unwrap())),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::literal_bool => Rc::new(Expr {
            kind: Rc::new(ExprKind::Bool(pair.as_str().parse().unwrap())),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::literal_string => Rc::new(Expr {
            kind: Rc::new(ExprKind::Str({
                let s = pair.as_str();
                // remove quotes
                s[1..s.len() - 1].to_owned()
            })),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::literal_list => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut exprs = vec![];
            for p in inner {
                exprs.push(parse_expr_pratt(Pairs::single(p), file_id));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::List(exprs)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::literal_array => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut exprs = vec![];
            for p in inner {
                exprs.push(parse_expr_pratt(Pairs::single(p), file_id));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Array(exprs)),
                loc: span,
                id: NodeId::new(),
            })
        }
        Rule::identifier => Rc::new(Expr {
            kind: Rc::new(ExprKind::Variable(pair.as_str().to_owned())),
            loc: span,
            id: NodeId::new(),
        }),
        Rule::member_access_inferred => {
            let inner: Vec<_> = pair.into_inner().collect();
            let ident = Identifier {
                v: inner[0].as_str().to_string(),
                loc: Location::new(file_id, inner[0].as_span()),
                id: NodeId::new(),
            }
            .into();
            Rc::new(Expr {
                kind: Rc::new(ExprKind::MemberAccessInferred(ident)),
                loc: span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}
