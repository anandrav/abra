use std::rc::Rc;

use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};
use pest::Parser;
use pest_derive::Parser;

use crate::SourceFile;

use crate::ast::*;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct MyParser; // TODO: move all parsing-related functions and structs to a file called parse.rs
pub(crate) fn parse_or_err(sources: &Vec<SourceFile>) -> Result<Vec<Rc<FileAst>>, String> {
    let mut files = vec![];
    for sf in sources {
        let pairs = get_pairs(&sf.contents)?;

        let file = parse_file(pairs, &sf.name);
        files.push(file);
    }
    Ok(files)
}

pub(crate) fn parse_file(pairs: Pairs<Rule>, filename: &str) -> Rc<FileAst> {
    let mut items = Vec::new();
    let pairs: Vec<_> = pairs.into_iter().collect();
    for pair in &pairs {
        if pair.as_rule() == Rule::EOI {
            break;
        }
        let stmt = parse_item(pair.clone(), filename);
        items.push(stmt)
    }
    let span1: Span = Span::new(filename, pairs.first().unwrap().as_span());
    let span2: Span = Span::new(filename, pairs.last().unwrap().as_span());
    Rc::new(FileAst {
        items,
        // remove the .abra suffix from filename
        name: filename.to_string()[..filename.len() - 5].to_string(),
        span: Span {
            filename: filename.to_string(),
            lo: span1.lo,
            hi: span2.hi,
        },
        id: NodeId::new(),
    })
}

pub(crate) fn parse_expr_pratt(pairs: Pairs<Rule>, filename: &str) -> Rc<Expr> {
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
        .op(Op::infix(Rule::op_access, Assoc::Left))
        .op(Op::postfix(Rule::index_access));
    pratt
        .map_primary(|t| parse_expr_term(t, filename))
        .map_prefix(|_op, _rhs| panic!("prefix operator encountered"))
        .map_postfix(|lhs, op| match op.as_rule() {
            Rule::index_access => {
                let span = Span::new(filename, op.as_span());
                let inner: Vec<_> = op.into_inner().collect();
                let index = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
                Rc::new(Expr {
                    kind: Rc::new(ExprKind::IndexAccess(lhs, index)),
                    span,
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
                    kind: Rc::new(ExprKind::BinOp(lhs, opcode, rhs)),
                    span: Span::new(filename, op.as_span()),
                    id: NodeId::new(),
                }),
                None => Rc::new(Expr {
                    kind: Rc::new(ExprKind::MemberAccess(lhs, rhs)),
                    span: Span::new(filename, op.as_span()),
                    id: NodeId::new(),
                }),
            }
        })
        .parse(pairs)
}

pub(crate) fn get_pairs(source: &str) -> Result<Pairs<Rule>, String> {
    MyParser::parse(Rule::file, source).map_err(|e| e.to_string())
}

pub(crate) fn parse_func_arg_annotation(pair: Pair<Rule>, filename: &str) -> ArgAnnotated {
    let rule = pair.as_rule();
    match rule {
        Rule::func_arg => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pat_pair = inner[0].clone();
            let pat = parse_let_pattern(pat_pair, filename);
            let annot = inner
                .get(1)
                .map(|type_pair| parse_type_term(type_pair.clone(), filename));
            (pat, annot)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_annotated_let_pattern(pair: Pair<Rule>, filename: &str) -> PatAnnotated {
    let rule = pair.as_rule();
    match rule {
        Rule::let_pattern_annotated => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pat_pair = inner[0].clone();
            let pat = parse_let_pattern(pat_pair, filename);
            let ty = inner
                .get(1)
                .map(|type_pair| parse_type_term(type_pair.clone(), filename));
            (pat, ty)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_func_out_annotation(pair: Pair<Rule>, filename: &str) -> Rc<Type> {
    let rule = pair.as_rule();
    match rule {
        Rule::func_out_annotation => {
            let inner: Vec<_> = pair.into_inner().collect();
            let type_pair = inner[0].clone();
            parse_type_term(type_pair, filename)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_let_pattern(pair: Pair<Rule>, filename: &str) -> Rc<Pat> {
    let span = Span::new(filename, pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pair = inner.first().unwrap().clone();
            parse_let_pattern(pair, filename)
        }
        Rule::identifier => Rc::new(Pat {
            kind: Rc::new(PatKind::Binding(pair.as_str().to_owned())),
            span,
            id: NodeId::new(),
        }),
        Rule::wildcard => Rc::new(Pat {
            kind: Rc::new(PatKind::Wildcard),
            span,
            id: NodeId::new(),
        }),
        Rule::let_pattern_tuple => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pats = inner
                .iter()
                .map(|pair| parse_let_pattern(pair.clone(), filename))
                .collect();
            Rc::new(Pat {
                kind: Rc::new(PatKind::Tuple(pats)),
                span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_match_pattern(pair: Pair<Rule>, filename: &str) -> Rc<Pat> {
    let span = Span::new(filename, pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::match_pattern => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pair = inner.first().unwrap().clone();
            parse_match_pattern(pair, filename)
        }
        Rule::match_pattern_variable => Rc::new(Pat {
            kind: Rc::new(PatKind::Binding(pair.as_str()[1..].to_owned())),
            span,
            id: NodeId::new(),
        }),
        Rule::match_pattern_tuple => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pats = inner
                .iter()
                .map(|pair| parse_match_pattern(pair.clone(), filename))
                .collect();
            Rc::new(Pat {
                kind: Rc::new(PatKind::Tuple(pats)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::match_pattern_variant => {
            let inner: Vec<_> = pair.into_inner().collect();
            let name = inner[0].as_str().to_owned();
            let span_variant_ctor = Span::new(filename, inner[0].as_span());
            let pat = inner
                .get(1)
                .map(|pair| parse_match_pattern(pair.clone(), filename));
            Rc::new(Pat {
                kind: Rc::new(PatKind::Variant(
                    Identifier {
                        v: name,
                        span: span_variant_ctor,
                        id: NodeId::new(),
                    },
                    pat,
                )),
                span,
                id: NodeId::new(),
            })
        }
        Rule::wildcard => Rc::new(Pat {
            kind: Rc::new(PatKind::Wildcard),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_unit => Rc::new(Pat {
            kind: Rc::new(PatKind::Unit),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_int => Rc::new(Pat {
            kind: Rc::new(PatKind::Int(pair.as_str().parse().unwrap())),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_float => Rc::new(Pat {
            kind: Rc::new(PatKind::Float(pair.as_str().parse().unwrap())),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_bool => Rc::new(Pat {
            kind: Rc::new(PatKind::Bool(pair.as_str().parse().unwrap())),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_string => Rc::new(Pat {
            kind: Rc::new(PatKind::Str({
                let s = pair.as_str();
                // remove quotes
                s[1..s.len() - 1].to_owned()
            })),
            span,
            id: NodeId::new(),
        }),
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_type_term(pair: Pair<Rule>, filename: &str) -> Rc<Type> {
    let span = Span::new(filename, pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::type_poly => {
            let inner: Vec<_> = pair.into_inner().collect();
            let ty_name = inner[0].as_str()[1..].to_owned();
            let ty_span = Span::new(filename, inner[0].as_span());
            let mut interfaces = vec![];
            for (i, pair) in inner.iter().enumerate() {
                if i == 0 {
                    continue;
                }
                let interface = Identifier {
                    v: pair.as_str().to_owned(),
                    span: Span::new(filename, pair.as_span()),
                    id: NodeId::new(),
                };
                interfaces.push(interface);
            }
            Rc::new(Type {
                kind: Rc::new(TypeKind::Poly(
                    Identifier {
                        v: ty_name,
                        span: ty_span,
                        id: NodeId::new(),
                    },
                    interfaces,
                )),
                span,
                id: NodeId::new(),
            })
        }
        Rule::identifier => {
            let ident = pair.as_str().to_owned();
            Rc::new(Type {
                kind: Rc::new(TypeKind::Identifier(ident)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::type_literal_unit => Rc::new(Type {
            kind: Rc::new(TypeKind::Unit),
            span,
            id: NodeId::new(),
        }),
        Rule::type_literal_int => Rc::new(Type {
            kind: Rc::new(TypeKind::Int),
            span,
            id: NodeId::new(),
        }),
        Rule::type_literal_float => Rc::new(Type {
            kind: Rc::new(TypeKind::Float),
            span,
            id: NodeId::new(),
        }),
        Rule::type_literal_bool => Rc::new(Type {
            kind: Rc::new(TypeKind::Bool),
            span,
            id: NodeId::new(),
        }),
        Rule::type_literal_string => Rc::new(Type {
            kind: Rc::new(TypeKind::Str),
            span,
            id: NodeId::new(),
        }),
        Rule::tuple_type => {
            let inner: Vec<_> = pair.into_inner().collect();
            let types = inner
                .into_iter()
                .map(|t| parse_type_term(t, filename))
                .collect();
            Rc::new(Type {
                kind: Rc::new(TypeKind::Tuple(types)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::type_ap => {
            let inner: Vec<_> = pair.into_inner().collect();
            let name = inner[0].as_str().to_owned();
            let ident_span = Span::new(filename, inner[0].as_span());
            let types = inner
                .into_iter()
                .skip(1)
                .map(|t| parse_type_term(t, filename))
                .collect();
            Rc::new(Type {
                kind: Rc::new(TypeKind::Ap(
                    Identifier {
                        v: name,
                        span: ident_span,
                        id: NodeId::new(),
                    },
                    types,
                )),
                span,
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
                .map(|t| parse_type_term(t, filename))
                .collect();
            let ret = parse_type_term(inner.last().unwrap().clone(), filename);
            Rc::new(Type {
                kind: Rc::new(TypeKind::Function(args, ret)),
                span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", pair),
    }
}

pub(crate) fn parse_item(pair: Pair<Rule>, filename: &str) -> Rc<Item> {
    let span = Span::new(filename, pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.clone().into_inner().collect();
    match rule {
        Rule::func_def => {
            let mut n = 0;
            let mut args = vec![];
            let name = Identifier {
                v: inner[0].as_str().to_string(),
                span: Span::new(filename, inner[0].as_span()),
                id: NodeId::new(),
            };
            n += 1;
            while let Rule::func_arg = inner[n].as_rule() {
                let pat_annotated = parse_func_arg_annotation(inner[n].clone(), filename);
                args.push(pat_annotated);
                n += 1;
            }

            let maybe_func_out = &inner[n];
            let ret_type = match maybe_func_out.as_rule() {
                Rule::func_out_annotation => {
                    // n += 1;
                    Some(parse_func_out_annotation(maybe_func_out.clone(), filename))
                }
                _ => None,
            };
            let body = parse_expr_pratt(Pairs::single(inner.last().unwrap().clone()), filename);
            Rc::new(Item {
                kind: Rc::new(ItemKind::FuncDef(
                    FuncDef {
                        name,
                        args,
                        ret_type,
                        body,
                    }
                    .into(),
                )),
                span,
                id: NodeId::new(),
            })
        }
        Rule::extern_func_decl => {
            let mut n = 0;
            let mut args = vec![];
            let name = Identifier {
                v: inner[0].as_str().to_string(),
                span: Span::new(filename, inner[0].as_span()),
                id: NodeId::new(),
            };
            n += 1;
            while let Rule::func_arg = inner[n].as_rule() {
                let pat_annotated = parse_func_arg_annotation(inner[n].clone(), filename);
                args.push(pat_annotated);
                n += 1;
            }

            let maybe_func_out = &inner[n];
            let ret_type = parse_func_out_annotation(maybe_func_out.clone(), filename);

            Rc::new(Item {
                kind: Rc::new(ItemKind::ExternFuncDecl(
                    ForeignFuncDecl {
                        name,
                        args,
                        ret_type,
                    }
                    .into(),
                )),
                span,
                id: NodeId::new(),
            })
        }
        // Rule::typealias => {
        //     let ident = inner[0].as_str().to_string();
        //     let definition = parse_type_term(inner[1].clone(), filename);
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
                ty_args.push(parse_type_term(inner[n].clone(), filename));
                n += 1;
            }
            let mut variants = vec![];
            while let Some(pair) = inner.get(n) {
                let variant = parse_variant(pair.clone(), filename);
                variants.push(variant);
                n += 1;
            }
            Rc::new(Item {
                kind: Rc::new(ItemKind::TypeDef(Rc::new(TypeDefKind::Enum(
                    EnumDef {
                        name: Identifier {
                            v: name,
                            span: span.clone(),
                            id: NodeId::new(),
                        },
                        ty_args,
                        variants,
                    }
                    .into(),
                )))),
                span,
                id: NodeId::new(),
            })
        }
        Rule::struct_declaration => {
            let name = inner[0].as_str().to_string();
            let mut n = 1;
            let mut ty_args = vec![];
            while let Rule::type_poly = inner[n].as_rule() {
                ty_args.push(parse_type_term(inner[n].clone(), filename));
                n += 1;
            }
            let mut fields = vec![];
            while let Some(pair) = inner.get(n) {
                let field = parse_struct_field(pair.clone(), filename);
                fields.push(Rc::new(field));
                n += 1;
            }

            let id = NodeId::new();
            Rc::new(Item {
                kind: Rc::new(ItemKind::TypeDef(Rc::new(TypeDefKind::Struct(
                    StructDef {
                        name: Identifier {
                            v: name,
                            span: span.clone(),
                            id: NodeId::new(),
                        },
                        ty_args,
                        fields,
                        id,
                    }
                    .into(),
                )))),
                span,
                id,
            })
        }
        Rule::interface_declaration => {
            let name = inner[0].as_str().to_string();
            let mut n = 1;
            let mut props = vec![];
            while let Some(pair) = inner.get(n) {
                let method = parse_interface_method(pair.clone(), filename);
                props.push(Rc::new(method));
                n += 1;
            }
            Rc::new(Item {
                kind: ItemKind::InterfaceDef(
                    InterfaceDef {
                        name: Identifier {
                            v: name,
                            span: span.clone(),
                            id: NodeId::new(),
                        },
                        props,
                    }
                    .into(),
                )
                .into(),
                span,
                id: NodeId::new(),
            })
        }
        Rule::interface_implementation => {
            let name = inner[0].as_str().to_string();
            let name_span = Span::new(filename, inner[0].as_span());
            let typ = parse_type_term(inner[1].clone(), filename);
            let mut n = 2;
            let mut stmts = vec![];
            while let Some(pair) = inner.get(n) {
                let stmt = parse_stmt(pair.clone(), filename);
                stmts.push(stmt);
                n += 1;
            }
            let impl_id = NodeId::new();
            Rc::new(Item {
                kind: ItemKind::InterfaceImpl(
                    InterfaceImpl {
                        iface: Identifier {
                            v: name,
                            span: name_span,
                            id: NodeId::new(),
                        },
                        typ,
                        stmts,

                        id: impl_id,
                    }
                    .into(),
                )
                .into(),
                span,
                id: impl_id,
            })
        }
        Rule::import => {
            let name = inner[0].as_str().to_string();
            Rc::new(Item {
                kind: ItemKind::Import(Identifier {
                    v: name,
                    span: span.clone(),
                    id: NodeId::new(),
                })
                .into(),
                span,
                id: NodeId::new(),
            })
        }
        Rule::let_statement
        | Rule::var_statement
        | Rule::set_statement
        | Rule::expression_statement => {
            let stmt = parse_stmt(pair, filename);
            Rc::new(Item {
                kind: ItemKind::Stmt(stmt).into(),
                span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_stmt(pair: Pair<Rule>, filename: &str) -> Rc<Stmt> {
    let span = Span::new(filename, pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::func_def => {
            let mut n = 0;
            let mut args = vec![];
            let name = Identifier {
                v: inner[0].as_str().to_string(),
                span: Span::new(filename, inner[0].as_span()),
                id: NodeId::new(),
            };
            n += 1;
            while let Rule::func_arg = inner[n].as_rule() {
                let pat_annotated = parse_func_arg_annotation(inner[n].clone(), filename);
                args.push(pat_annotated);
                n += 1;
            }

            let maybe_func_out = &inner[n];
            let ret_type = match maybe_func_out.as_rule() {
                Rule::func_out_annotation => {
                    // n += 1;
                    Some(parse_func_out_annotation(maybe_func_out.clone(), filename))
                }
                _ => None,
            };
            let body = parse_expr_pratt(Pairs::single(inner.last().unwrap().clone()), filename);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::FuncDef(
                    FuncDef {
                        name,
                        args,
                        ret_type,
                        body,
                    }
                    .into(),
                )),
                span,
                id: NodeId::new(),
            })
        }
        Rule::let_statement => {
            let offset = 0;
            let pat_annotated = parse_annotated_let_pattern(inner[offset].clone(), filename);
            let expr = parse_expr_pratt(Pairs::single(inner[offset + 1].clone()), filename);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::Let(false, pat_annotated, expr)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::var_statement => {
            let offset = 0;
            let pat_annotated = parse_annotated_let_pattern(inner[offset].clone(), filename);
            let expr = parse_expr_pratt(Pairs::single(inner[offset + 1].clone()), filename);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::Let(true, pat_annotated, expr)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::set_statement => {
            let expr1 = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
            let expr2 = parse_expr_pratt(Pairs::single(inner[1].clone()), filename);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::Set(expr1, expr2)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::expression_statement => {
            let expr = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::Expr(expr)),
                span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_interface_method(pair: Pair<Rule>, filename: &str) -> InterfaceProperty {
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::interface_property => {
            let name = inner[0].as_str().to_string();
            let span = Span::new(filename, inner[0].as_span());
            let ty = parse_type_term(inner[1].clone(), filename);
            InterfaceProperty {
                name: Identifier {
                    v: name,
                    span,
                    id: NodeId::new(),
                },
                ty,
            }
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_variant(pair: Pair<Rule>, filename: &str) -> Rc<Variant> {
    let span = Span::new(filename, pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::variant => {
            let name = inner[0].as_str().to_string();
            let span_ctor = Span::new(filename, inner[0].as_span());
            let n = 1;
            // while let Rule::type_poly = inner[n].as_rule() {
            //     type_params.push(inner[n].as_str().to_string());
            //     n += 1;
            // }
            let data = if let Some(pair) = inner.get(n) {
                let data = parse_type_term(pair.clone(), filename);
                Some(data)
            } else {
                None
            };
            Rc::new(Variant {
                ctor: Identifier {
                    v: name,
                    span: span_ctor,
                    id: NodeId::new(),
                },
                data,
                span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_struct_field(pair: Pair<Rule>, filename: &str) -> StructField {
    let span = Span::new(filename, pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::struct_field => {
            let name = inner[0].as_str().to_string();
            let span_field = Span::new(filename, inner[0].as_span());
            let ty = parse_type_term(inner[1].clone(), filename);
            StructField {
                name: Identifier {
                    v: name,
                    span: span_field,
                    id: NodeId::new(),
                },
                ty,
                span,
                id: NodeId::new(),
            }
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_expr_term(pair: Pair<Rule>, filename: &str) -> Rc<Expr> {
    let span = Span::new(filename, pair.as_span());
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
        Rule::expression => parse_expr_pratt(pair.into_inner(), filename),
        // All rules listed below should be non-operator expressions
        Rule::block_expression => {
            let inner = pair.into_inner();
            let mut statements: Vec<Rc<Stmt>> = Vec::new();
            for pair in inner {
                statements.push(parse_stmt(pair, filename));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Block(statements)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::if_else_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let cond = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
            let e1 = parse_expr_pratt(Pairs::single(inner[1].clone()), filename);
            let e2 = if inner.len() == 3 {
                Some(parse_expr_pratt(Pairs::single(inner[2].clone()), filename))
            } else {
                None
            };
            Rc::new(Expr {
                kind: Rc::new(ExprKind::If(cond, e1, e2)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::while_loop_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let cond = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
            let e = parse_expr_pratt(Pairs::single(inner[1].clone()), filename);
            Rc::new(Expr {
                kind: Rc::new(ExprKind::WhileLoop(cond, e)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::match_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let expr = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
            let mut arms = vec![];
            fn parse_match_arm(pair: &Pair<Rule>, filename: &str) -> MatchArm {
                let inner: Vec<_> = pair.clone().into_inner().collect();
                let pat = parse_match_pattern(inner[0].clone(), filename);
                let expr = parse_expr_pratt(Pairs::single(inner[1].clone()), filename);
                MatchArm { pat, expr }
            }
            for pair in &inner[1..] {
                arms.push(parse_match_arm(pair, filename));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Match(expr, arms)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::func_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut n = 0;
            let mut args = vec![];
            while let Rule::func_arg = inner[n].as_rule() {
                let pat_annotated = parse_func_arg_annotation(inner[n].clone(), filename);
                args.push(pat_annotated);
                n += 1;
            }

            let maybe_func_out = &inner[n];
            let ty_out = match maybe_func_out.as_rule() {
                Rule::func_out_annotation => {
                    // n += 1;
                    Some(parse_func_out_annotation(maybe_func_out.clone(), filename))
                }
                _ => None,
            };
            let body = parse_expr_pratt(Pairs::single(inner.last().unwrap().clone()), filename);
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Func(args, ty_out, body)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::func_call_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let f = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
            let inner: Vec<_> = inner[1].clone().into_inner().collect();
            let mut args = vec![];
            for p in &inner[0..] {
                args.push(parse_expr_pratt(Pairs::single(p.clone()), filename));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::FuncAp(f, args)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::tuple_expr => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut exprs = vec![];
            for p in inner {
                exprs.push(parse_expr_pratt(Pairs::single(p), filename));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Tuple(exprs)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::literal_unit => Rc::new(Expr {
            kind: Rc::new(ExprKind::Unit),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_int => Rc::new(Expr {
            kind: Rc::new(ExprKind::Int(pair.as_str().parse().unwrap())),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_float => Rc::new(Expr {
            kind: Rc::new(ExprKind::Float(pair.as_str().parse().unwrap())),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_bool => Rc::new(Expr {
            kind: Rc::new(ExprKind::Bool(pair.as_str().parse().unwrap())),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_string => Rc::new(Expr {
            kind: Rc::new(ExprKind::Str({
                let s = pair.as_str();
                // remove quotes
                s[1..s.len() - 1].to_owned()
            })),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_list => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut exprs = vec![];
            for p in inner {
                exprs.push(parse_expr_pratt(Pairs::single(p), filename));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::List(exprs)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::literal_array => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut exprs = vec![];
            for p in inner {
                exprs.push(parse_expr_pratt(Pairs::single(p), filename));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Array(exprs)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::identifier => Rc::new(Expr {
            kind: Rc::new(ExprKind::Identifier(pair.as_str().to_owned())),
            span,
            id: NodeId::new(),
        }),
        _ => panic!("unreachable rule {:#?}", rule),
    }
}
