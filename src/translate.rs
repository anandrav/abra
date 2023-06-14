use crate::ast;
use crate::ast::NodeMap;
use crate::eval_tree;
use crate::statics::Gamma;
use crate::statics::InferenceContext;
use crate::statics::Prov;
use std::cell::RefCell;
use std::rc::Rc;

type ASTek = ast::ExprKind;
type Ete = eval_tree::Expr;

type ASTpk = ast::PatKind;
type Etp = eval_tree::Pat;

pub fn translate_pat(parse_tree: Rc<ast::Pat>) -> Rc<Etp> {
    match &*parse_tree.patkind {
        ASTpk::Wildcard => Rc::new(Etp::Wildcard),
        ASTpk::Var(id) => Rc::new(Etp::Var(id.clone())),
        ASTpk::Variant(id, pat) => Rc::new(Etp::TaggedVariant(
            id.clone(),
            pat.clone().map(translate_pat),
        )),
        ASTpk::Tuple(pats) => Rc::new(Etp::Tuple(
            pats.iter().map(|pat| translate_pat(pat.clone())).collect(),
        )),
        ASTpk::Unit => Rc::new(Etp::Unit),
        ASTpk::Int(i) => Rc::new(Etp::Int(*i)),
        ASTpk::Bool(b) => Rc::new(Etp::Bool(*b)),
        ASTpk::Str(s) => Rc::new(Etp::Str(s.clone())),
    }
}

pub fn translate_expr_block(
    inf_ctx: &InferenceContext,
    gamma: Rc<RefCell<Gamma>>,
    node_map: &NodeMap,
    stmts: Vec<Rc<ast::Stmt>>,
) -> Rc<Ete> {
    if stmts.is_empty() {
        return Rc::new(Ete::Unit);
    }
    let statement = &stmts[0];
    match &*statement.stmtkind {
        ast::StmtKind::InterfaceDef(..)
        | ast::StmtKind::InterfaceImpl(..)
        | ast::StmtKind::TypeDef(_) => {
            translate_expr_block(inf_ctx, gamma.clone(), node_map, stmts[1..].to_vec())
        }
        ast::StmtKind::LetFunc(pat, func_args, _, body) => {
            let id = pat.patkind.get_identifier_of_variable();
            let func = translate_expr_func(
                inf_ctx,
                gamma.clone(),
                node_map,
                func_args.clone(),
                body.clone(),
            );
            Rc::new(Ete::Let(
                Rc::new(Etp::Var(id)),
                func,
                translate_expr_block(inf_ctx, gamma.clone(), node_map, stmts[1..].to_vec()),
            ))
        }
        ast::StmtKind::Let((pat, _), expr) => Rc::new(Ete::Let(
            translate_pat(pat.clone()),
            translate_expr(
                inf_ctx,
                gamma.clone(),
                node_map,
                expr.exprkind.clone(),
                expr.id,
            ),
            translate_expr_block(inf_ctx, gamma.clone(), node_map, stmts[1..].to_vec()),
        )),
        ast::StmtKind::Expr(e) if stmts.len() == 1 => {
            translate_expr(inf_ctx, gamma.clone(), node_map, e.exprkind.clone(), e.id)
        }
        ast::StmtKind::Expr(expr) => Rc::new(Ete::Let(
            Rc::new(eval_tree::Pat::Var("_".to_string())), // TODO anandduk: add actual wildcard
            translate_expr(
                inf_ctx,
                gamma.clone(),
                node_map,
                expr.exprkind.clone(),
                expr.id,
            ),
            translate_expr_block(inf_ctx, gamma.clone(), node_map, stmts[1..].to_vec()),
        )),
    }
}

pub fn translate_expr_func(
    inf_ctx: &InferenceContext,
    gamma: Rc<RefCell<Gamma>>,
    node_map: &NodeMap,
    func_args: Vec<ast::ArgAnnotated>,
    body: Rc<ast::Expr>,
) -> Rc<Ete> {
    let id = func_args[0].0.patkind.get_identifier_of_variable(); // TODO: allow function arguments to be patterns
    if func_args.len() == 1 {
        Rc::new(Ete::Func(
            id,
            translate_expr(
                inf_ctx,
                gamma.clone(),
                node_map,
                body.exprkind.clone(),
                body.id,
            ),
            None,
        ))
    } else {
        // currying
        let rest_of_function = translate_expr_func(
            inf_ctx,
            gamma.clone(),
            node_map,
            func_args[1..].to_vec(),
            body,
        );
        Rc::new(Ete::Func(id, rest_of_function, None))
    }
}

pub fn translate_expr_ap(
    inf_ctx: &InferenceContext,
    gamma: Rc<RefCell<Gamma>>,
    node_map: &NodeMap,
    expr1: Rc<ast::Expr>,
    expr2: Rc<ast::Expr>,
    exprs: Vec<Rc<ast::Expr>>,
) -> Rc<Ete> {
    if exprs.is_empty() {
        Rc::new(Ete::FuncAp(
            translate_expr(
                inf_ctx,
                gamma.clone(),
                node_map,
                expr1.exprkind.clone(),
                expr1.id,
            ),
            translate_expr(
                inf_ctx,
                gamma.clone(),
                node_map,
                expr2.exprkind.clone(),
                expr2.id,
            ),
            None,
        ))
    } else {
        // currying
        let rest_of_arguments_applied = translate_expr_ap(
            inf_ctx,
            gamma.clone(),
            node_map,
            expr1,
            expr2,
            exprs[..exprs.len() - 1].to_vec(),
        );
        let last = exprs.last().unwrap();
        Rc::new(Ete::FuncAp(
            rest_of_arguments_applied,
            translate_expr(
                inf_ctx,
                gamma.clone(),
                node_map,
                last.exprkind.clone(),
                last.id,
            ),
            None,
        ))
    }
}

pub fn translate_expr(
    inf_ctx: &InferenceContext,
    gamma: Rc<RefCell<Gamma>>,
    node_map: &NodeMap,
    parse_tree: Rc<ASTek>,
    ast_id: ast::Id,
) -> Rc<Ete> {
    match &*parse_tree {
        ASTek::Var(id) => {
            // println!("id: {:?}", id);
            // if gamma.borrow().vars.contains_key(id) {
            //     println!("it's in the gamma");
            //     let unifvar = inf_ctx.vars.get(&Prov::Node(ast_id)).unwrap();
            //     let solved_ty = unifvar.clone_data().solution().unwrap();
            //     println!("solved_ty: {:?}", solved_ty);
            //     if let Some(named_ty) = solved_ty.named_type() {
            //         println!("named_ty: {:?}", named_ty);
            //         if let Some(interface_name) = inf_ctx.method_to_interface.get(&id.clone()) {
            //             println!("interface_name: {:?}", interface_name);
            //             let impl_list = inf_ctx.interface_impls.get(interface_name).unwrap();
            //             // find an impl that matches
            //             dbg!(impl_list);

            //             for imp in impl_list {
            //                 println!("interface_impl: {:?}", imp);
            //                 for method in &imp.methods {
            //                     println!("method name: {:?}", method.name);
            //                     println!("id: {:?}", id);
            //                     if method.name == *id {
            //                         let method_identifier_node =
            //                             node_map.get(&method.identifier_location).unwrap();
            //                         println!("func_node: {:?}", method_identifier_node);
            //                         let func_id = method_identifier_node.id();
            //                         let unifvar = inf_ctx.vars.get(&Prov::Node(func_id)).unwrap();
            //                         let solved_ty = unifvar.clone_data().solution().unwrap();
            //                         if let Some(named_ty_impl) = solved_ty.named_type() {
            //                             println!("named_ty_impl: {:?}", named_ty_impl);
            //                             if (named_ty == named_ty_impl) {
            //                                 println!("THEY ARE EQUAL!!!!!!!!");
            //                                 let method_node =
            //                                     node_map.get(&method.method_location).unwrap();
            //                                 let method_node_id = method_node.id();
            //                                 let method_node =
            //                                     Rc::new(method_node.into_stmt().unwrap());
            //                                 if let ast::StmtKind::LetFunc(_, args, _, body) =
            //                                     &*method_node.stmtkind
            //                                 {
            //                                     println!("it's a let func");
            //                                     return translate_expr_func(
            //                                         inf_ctx,
            //                                         gamma,
            //                                         node_map,
            //                                         args.clone(),
            //                                         body.clone(),
            //                                     );
            //                                 }
            //                                 return translate_expr_block(
            //                                     inf_ctx,
            //                                     gamma,
            //                                     node_map,
            //                                     vec![method_node],
            //                                 );
            //                             }
            //                         }

            //                         ()
            //                         // return translation of whatever function impl is located here
            //                     }
            //                 }
            //             }
            //         }
            //     }
            // }
            return Rc::new(Ete::Var(id.clone()));
        }
        ASTek::Unit => Rc::new(Ete::Unit),
        ASTek::Int(i) => Rc::new(Ete::Int(*i)),
        ASTek::Bool(b) => Rc::new(Ete::Bool(*b)),
        ASTek::Str(s) => Rc::new(Ete::Str(s.clone())),
        ASTek::Tuple(exprs) => {
            let mut translated_exprs = Vec::new();
            for expr in exprs {
                translated_exprs.push(translate_expr(
                    inf_ctx,
                    gamma.clone(),
                    node_map,
                    expr.exprkind.clone(),
                    expr.id,
                ));
            }
            Rc::new(Ete::Tuple(translated_exprs))
        }
        ASTek::BinOp(expr1, op, expr2) => Rc::new(Ete::BinOp(
            translate_expr(
                inf_ctx,
                gamma.clone(),
                node_map,
                expr1.exprkind.clone(),
                expr1.id,
            ),
            *op,
            translate_expr(
                inf_ctx,
                gamma.clone(),
                node_map,
                expr2.exprkind.clone(),
                expr2.id,
            ),
        )),
        ASTek::Block(stmts) => {
            translate_expr_block(inf_ctx, gamma.clone(), node_map, stmts.clone())
        }
        ASTek::Func(func_args, _, body) => translate_expr_func(
            inf_ctx,
            gamma.clone(),
            node_map,
            func_args.clone(),
            body.clone(),
        ),
        ASTek::FuncAp(expr1, exprs) => translate_expr_ap(
            inf_ctx,
            gamma.clone(),
            node_map,
            expr1.clone(),
            exprs[0].clone(),
            exprs[1..].iter().map(|expr| expr.clone()).collect(),
        ),
        ASTek::MethodAp(receiver, method, args) => Rc::new(Ete::Unit),
        ASTek::If(expr1, expr2, expr3) => match expr3 {
            // if-else
            Some(expr3) => Rc::new(Ete::If(
                translate_expr(
                    inf_ctx,
                    gamma.clone(),
                    node_map,
                    expr1.exprkind.clone(),
                    expr1.id,
                ),
                translate_expr(
                    inf_ctx,
                    gamma.clone(),
                    node_map,
                    expr2.exprkind.clone(),
                    expr2.id,
                ),
                translate_expr(
                    inf_ctx,
                    gamma.clone(),
                    node_map,
                    expr3.exprkind.clone(),
                    expr3.id,
                ),
            )),
            // just
            None => Rc::new(Ete::If(
                translate_expr(
                    inf_ctx,
                    gamma.clone(),
                    node_map,
                    expr1.exprkind.clone(),
                    expr1.id,
                ),
                translate_expr(
                    inf_ctx,
                    gamma.clone(),
                    node_map,
                    expr2.exprkind.clone(),
                    expr2.id,
                ),
                Rc::new(Ete::Unit),
            )),
        },
        ASTek::Match(expr, arms) => {
            let mut translated_arms = Vec::new();
            for arm in arms {
                translated_arms.push((
                    translate_pat(arm.pat.clone()),
                    translate_expr(
                        inf_ctx,
                        gamma.clone(),
                        node_map,
                        arm.expr.exprkind.clone(),
                        arm.expr.id,
                    ),
                ));
            }
            Rc::new(Ete::Match(
                translate_expr(
                    inf_ctx,
                    gamma.clone(),
                    node_map,
                    expr.exprkind.clone(),
                    expr.id,
                ),
                translated_arms,
            ))
        }
    }
}

pub fn translate(
    inf_ctx: &InferenceContext,
    gamma: Rc<RefCell<Gamma>>,
    node_map: &NodeMap,
    toplevel: Rc<ast::Toplevel>,
) -> Rc<Ete> {
    translate_expr_block(
        inf_ctx,
        gamma.clone(),
        node_map,
        toplevel.statements.clone(),
    )
}
