use crate::ast;
use crate::ast::Node;
use crate::ast::NodeMap;
use crate::environment::Environment;
use crate::environment::EvalEnv;
use crate::eval_tree;
use crate::interpreter;
use crate::operators::BinOpcode;
use crate::statics;
use crate::statics::Gamma;
use crate::statics::InferenceContext;
use crate::statics::Monotype;
use crate::statics::Prov;
use crate::statics::SolvedType;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

type ASTek = ast::ExprKind;
type Ete = eval_tree::Expr;
type Etl = eval_tree::PlaceExpr;

type ASTpk = ast::PatKind;
type Etp = eval_tree::Pat;

type MonomorphEnv = Environment<ast::Symbol, SolvedType>;

fn translate_pat(parse_tree: Rc<ast::Pat>) -> Rc<Etp> {
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
        ASTpk::Float(f) => Rc::new(Etp::Float(*f)),
        ASTpk::Bool(b) => Rc::new(Etp::Bool(*b)),
        ASTpk::Str(s) => Rc::new(Etp::Str(s.clone())),
    }
}

fn translate_expr_block(
    inf_ctx: &InferenceContext,
    monomorphenv: MonomorphEnv,
    gamma: Gamma,
    node_map: &NodeMap,
    overloaded_func_map: &mut OverloadedFuncMapTemp,
    stmts: Vec<Rc<ast::Stmt>>,
    env: Option<EvalEnv>,
) -> Rc<Ete> {
    if stmts.is_empty() {
        return Rc::new(Ete::Unit);
    }
    let statement = &stmts[0];
    match &*statement.stmtkind {
        ast::StmtKind::InterfaceDef(..)
        | ast::StmtKind::InterfaceImpl(..)
        | ast::StmtKind::TypeDef(_) => translate_expr_block(
            inf_ctx,
            monomorphenv,
            gamma,
            node_map,
            overloaded_func_map,
            stmts[1..].to_vec(),
            env.clone(),
        ),
        ast::StmtKind::FuncDef(pat, func_args, _, body) => {
            let ty = inf_ctx.solution_of_node(pat.id).unwrap();
            if ty.is_overloaded_MUST_DEPRECATE() {
                // if function is overloaded, don't translate its body
                return translate_expr_block(
                    inf_ctx,
                    monomorphenv,
                    gamma,
                    node_map,
                    overloaded_func_map,
                    stmts[1..].to_vec(),
                    env.clone(),
                );
            }
            let id = pat.patkind.get_identifier_of_variable();

            let func = translate_expr_func(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                overloaded_func_map,
                func_args.clone(),
                body.clone(),
            );
            if let Some(env) = &env {
                env.extend(id.clone(), func.clone());
            }
            Rc::new(Ete::Let(
                Rc::new(Etp::Var(id)),
                func,
                translate_expr_block(
                    inf_ctx,
                    monomorphenv,
                    gamma,
                    node_map,
                    overloaded_func_map,
                    stmts[1..].to_vec(),
                    env.clone(),
                ),
            ))
        }
        ast::StmtKind::Let(_mutable, (pat, _), expr) => Rc::new(Ete::Let(
            translate_pat(pat.clone()),
            translate_expr(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                overloaded_func_map,
                expr.exprkind.clone(),
                expr.id,
            ),
            translate_expr_block(
                inf_ctx,
                monomorphenv,
                gamma,
                node_map,
                overloaded_func_map,
                stmts[1..].to_vec(),
                env.clone(),
            ),
        )),
        ast::StmtKind::Set(expr1, expr2) => Rc::new(Ete::Set(
            make_place_expr(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                overloaded_func_map,
                expr1.clone(),
            ),
            translate_expr(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                overloaded_func_map,
                expr2.exprkind.clone(),
                expr2.id,
            ),
            translate_expr_block(
                inf_ctx,
                monomorphenv,
                gamma,
                node_map,
                overloaded_func_map,
                stmts[1..].to_vec(),
                env.clone(),
            ),
        )),
        ast::StmtKind::Expr(e) if stmts.len() == 1 => translate_expr(
            inf_ctx,
            monomorphenv,
            gamma,
            node_map,
            overloaded_func_map,
            e.exprkind.clone(),
            e.id,
        ),
        ast::StmtKind::Expr(expr) => Rc::new(Ete::Let(
            Rc::new(eval_tree::Pat::Wildcard),
            translate_expr(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                overloaded_func_map,
                expr.exprkind.clone(),
                expr.id,
            ),
            translate_expr_block(
                inf_ctx,
                monomorphenv,
                gamma,
                node_map,
                overloaded_func_map,
                stmts[1..].to_vec(),
                env.clone(),
            ),
        )),
    }
}

fn make_place_expr(
    inf_ctx: &InferenceContext,
    monomorphenv: MonomorphEnv,
    gamma: Gamma,
    node_map: &NodeMap,
    overloaded_func_map: &mut OverloadedFuncMapTemp,
    expr: Rc<ast::Expr>,
) -> Rc<Etl> {
    match &*expr.exprkind {
        ast::ExprKind::Var(id) => Rc::new(Etl::Var(id.clone())),
        ast::ExprKind::FieldAccess(expr, field) => {
            let ASTek::Var(field_ident) = &*field.exprkind else {
                panic!()
            };
            Rc::new(Etl::FieldAccess(
                translate_expr(
                    inf_ctx,
                    monomorphenv,
                    gamma,
                    node_map,
                    overloaded_func_map,
                    expr.exprkind.clone(),
                    expr.id,
                ),
                field_ident.clone(),
            ))
        }
        ast::ExprKind::IndexAccess(expr1, expr2) => Rc::new(Etl::IndexAccess(
            translate_expr(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                overloaded_func_map,
                expr1.exprkind.clone(),
                expr1.id,
            ),
            translate_expr(
                inf_ctx,
                monomorphenv,
                gamma,
                node_map,
                overloaded_func_map,
                expr2.exprkind.clone(),
                expr2.id,
            ),
        )),
        _ => panic!("invalid place expression"),
    }
}

fn translate_expr_func(
    inf_ctx: &InferenceContext,
    monomorphenv: MonomorphEnv,
    gamma: Gamma,
    node_map: &NodeMap,
    overloaded_func_map: &mut OverloadedFuncMapTemp,
    func_args: Vec<ast::ArgAnnotated>,
    body: Rc<ast::Expr>,
) -> Rc<Ete> {
    let args = func_args
        .iter()
        .map(|arg| arg.0.patkind.get_identifier_of_variable())
        .collect();
    Rc::new(Ete::Func(
        args,
        translate_expr(
            inf_ctx,
            monomorphenv,
            gamma,
            node_map,
            overloaded_func_map,
            body.exprkind.clone(),
            body.id,
        ),
        None,
    ))
}

fn translate_expr_ap(
    inf_ctx: &InferenceContext,
    monomorphenv: MonomorphEnv,
    gamma: Gamma,
    node_map: &NodeMap,
    overloaded_func_map: &mut OverloadedFuncMapTemp,
    expr1: Rc<ast::Expr>,
    exprs: Vec<Rc<ast::Expr>>,
) -> Rc<Ete> {
    Rc::new(Ete::FuncAp(
        translate_expr(
            inf_ctx,
            monomorphenv.clone(),
            gamma.clone(),
            node_map,
            overloaded_func_map,
            expr1.exprkind.clone(),
            expr1.id,
        ),
        exprs
            .iter()
            .map(|e| {
                translate_expr(
                    inf_ctx,
                    monomorphenv.clone(),
                    gamma.clone(),
                    node_map,
                    overloaded_func_map,
                    e.exprkind.clone(),
                    e.id,
                )
            })
            .collect(),
        None,
    ))
}

fn ty_of_global_ident(gamma: Gamma, ident: &ast::Symbol) -> Option<SolvedType> {
    let ty = gamma.lookup(ident)?; // TODO: This is the only place gamma is used, and InferenceContext could be used instead
    ty.solution()
}

fn update_monomorphenv(
    monomorphenv: MonomorphEnv,
    overloaded_ty: SolvedType,
    monomorphic_ty: SolvedType,
) {
    match (overloaded_ty, monomorphic_ty.clone()) {
        // recurse
        (SolvedType::Function(args, out), SolvedType::Function(args2, out2)) => {
            for i in 0..args.len() {
                update_monomorphenv(monomorphenv.clone(), args[i].clone(), args2[i].clone());
            }
            update_monomorphenv(monomorphenv, *out, *out2);
        }
        (SolvedType::UdtInstance(ident, params), SolvedType::UdtInstance(ident2, params2)) => {
            assert_eq!(ident, ident2);
            for i in 0..params.len() {
                update_monomorphenv(monomorphenv.clone(), params[i].clone(), params2[i].clone());
            }
        }
        (SolvedType::Poly(ident, _), _) => {
            monomorphenv.extend(ident, monomorphic_ty);
        }
        (SolvedType::Tuple(elems1), SolvedType::Tuple(elems2)) => {
            for i in 0..elems1.len() {
                update_monomorphenv(monomorphenv.clone(), elems1[i].clone(), elems2[i].clone());
            }
        }
        _ => {}
    }
}

fn subst_with_monomorphic_env(monomorphic_env: MonomorphEnv, ty: SolvedType) -> SolvedType {
    match ty {
        SolvedType::Function(args, out) => {
            let new_args = args
                .iter()
                .map(|arg| subst_with_monomorphic_env(monomorphic_env.clone(), arg.clone()))
                .collect();
            let new_out = subst_with_monomorphic_env(monomorphic_env, *out);
            SolvedType::Function(new_args, Box::new(new_out))
        }
        SolvedType::UdtInstance(ident, params) => {
            let new_params = params
                .iter()
                .map(|param| subst_with_monomorphic_env(monomorphic_env.clone(), param.clone()))
                .collect();
            SolvedType::UdtInstance(ident, new_params)
        }
        SolvedType::Poly(ref ident, _) => {
            if let Some(monomorphic_ty) = monomorphic_env.lookup(ident) {
                monomorphic_ty
            } else {
                ty
            }
        }
        SolvedType::Tuple(elems) => {
            let new_elems = elems
                .iter()
                .map(|elem| subst_with_monomorphic_env(monomorphic_env.clone(), elem.clone()))
                .collect();
            SolvedType::Tuple(new_elems)
        }
        _ => ty,
    }
}

fn get_func_definition_node(
    inf_ctx: &InferenceContext,
    node_map: &NodeMap,
    ident: &ast::Symbol,
    desired_interface_impl: SolvedType,
) -> Rc<dyn ast::Node> {
    if let Some(interface_name) = inf_ctx.method_to_interface.get(&ident.clone()) {
        let impl_list = inf_ctx.interface_impls.get(interface_name).unwrap();
        // TODO just because the variable is the same name as an overloaded function doesn't mean the overloaded function is actually being used here.
        // use the type of the variable to determine if it's the same as the overloaded function?

        // find an impl that matches
        // dbg!(impl_list);

        for imp in impl_list {
            for method in &imp.methods {
                if method.name == *ident {
                    let method_identifier_node = node_map.get(&method.identifier_location).unwrap();

                    let func_id = method_identifier_node.id();
                    let unifvar = inf_ctx.vars.get(&Prov::Node(func_id)).unwrap();
                    let interface_impl_ty = unifvar.solution().unwrap();

                    if statics::ty_fits_impl_ty(
                        inf_ctx,
                        desired_interface_impl.clone(),
                        interface_impl_ty,
                    )
                    .is_ok()
                    {
                        // if desired_interface_impl.clone() == interface_impl_ty {

                        let method_node = node_map.get(&method.method_location).unwrap();
                        return method_node.clone();
                    }
                }
            }
        }
        panic!("couldn't find impl for method");
    } else {
        return inf_ctx.fun_defs.get(ident).unwrap().clone();
    }
}

fn monomorphize_overloaded_var(
    inf_ctx: &InferenceContext,
    monomorphenv: MonomorphEnv,
    gamma: Gamma,
    node_map: &NodeMap,
    overloaded_func_map: &mut OverloadedFuncMapTemp,
    ident: &ast::Symbol,
    node_ty: SolvedType,
) -> Option<Monotype> {
    if let Some(global_ty) = ty_of_global_ident(gamma.clone(), ident) {
        if global_ty.is_overloaded_MUST_DEPRECATE() {
            let substituted_ty = subst_with_monomorphic_env(monomorphenv, node_ty);

            let instance_ty = substituted_ty.monotype().unwrap();
            if let Some(_overloaded_func) =
                overloaded_func_map.get(&(ident.clone(), instance_ty.clone()))
            {
                return Some(instance_ty);
            }
            let func_def_node =
                get_func_definition_node(inf_ctx, node_map, ident, substituted_ty.clone())
                    .to_stmt()
                    .unwrap();
            let ast::StmtKind::FuncDef(pat, args, _, body) = &*func_def_node.stmtkind else {
                panic!()
            };

            let overloaded_func_ty = inf_ctx.solution_of_node(pat.id()).unwrap();
            let monomorphenv = MonomorphEnv::empty();
            update_monomorphenv(monomorphenv.clone(), overloaded_func_ty, substituted_ty);

            overloaded_func_map.insert((ident.clone(), instance_ty.clone()), None);
            let overloaded_func = translate_expr_func(
                inf_ctx,
                monomorphenv,
                gamma,
                node_map,
                overloaded_func_map,
                args.clone(),
                body.clone(),
            );
            overloaded_func_map.insert((ident.clone(), instance_ty.clone()), Some(overloaded_func));
            return Some(instance_ty);
        }
    }
    None
}

fn translate_expr(
    inf_ctx: &InferenceContext,
    monomorphenv: MonomorphEnv,
    gamma: Gamma,
    node_map: &NodeMap,
    overloaded_func_map: &mut OverloadedFuncMapTemp,
    parse_tree: Rc<ASTek>,
    ast_id: ast::NodeId,
) -> Rc<Ete> {
    match &*parse_tree {
        ASTek::Var(ident) => {
            if let Some(node_ty) = inf_ctx.solution_of_node(ast_id) {
                if let Some(instance_ty) = monomorphize_overloaded_var(
                    inf_ctx,
                    monomorphenv,
                    gamma,
                    node_map,
                    overloaded_func_map,
                    ident,
                    node_ty,
                ) {
                    return Rc::new(Ete::VarOverloaded(ident.clone(), instance_ty));
                }
            }
            Rc::new(Ete::Var(ident.clone()))
        }
        ASTek::Unit => Rc::new(Ete::Unit),
        ASTek::Int(i) => Rc::new(Ete::Int(*i)),
        ASTek::Float(f) => Rc::new(Ete::Float(*f)),
        ASTek::Bool(b) => Rc::new(Ete::Bool(*b)),
        ASTek::Str(s) => Rc::new(Ete::Str(s.clone())),
        ASTek::List(exprs) => {
            let mut result = Rc::new(Ete::Var("nil".to_owned()));
            for expr in exprs.iter().rev() {
                let translated_expr = translate_expr(
                    inf_ctx,
                    monomorphenv.clone(),
                    gamma.clone(),
                    node_map,
                    overloaded_func_map,
                    expr.exprkind.clone(),
                    expr.id,
                );
                result = Rc::new(Ete::FuncAp(
                    Rc::new(Ete::Var("cons".to_owned())),
                    vec![translated_expr, result],
                    None,
                ));
            }
            result
        }
        ASTek::Array(exprs) => Rc::new(Ete::Array(Rc::new(RefCell::new(
            exprs
                .iter()
                .map(|e| {
                    translate_expr(
                        inf_ctx,
                        monomorphenv.clone(),
                        gamma.clone(),
                        node_map,
                        overloaded_func_map,
                        e.exprkind.clone(),
                        e.id,
                    )
                })
                .collect(),
        )))),
        ASTek::Tuple(exprs) => {
            let mut translated_exprs = Vec::new();
            for expr in exprs {
                translated_exprs.push(translate_expr(
                    inf_ctx,
                    monomorphenv.clone(),
                    gamma.clone(),
                    node_map,
                    overloaded_func_map,
                    expr.exprkind.clone(),
                    expr.id,
                ));
            }
            Rc::new(Ete::Tuple(translated_exprs))
        }
        ASTek::BinOp(
            expr1,
            opcode @ (BinOpcode::Equals
            | BinOpcode::LessThan
            | BinOpcode::LessThanOrEqual
            | BinOpcode::GreaterThan
            | BinOpcode::GreaterThanOrEqual),
            expr2,
        ) => {
            let ty1 = inf_ctx.solution_of_node(expr1.id()).unwrap();
            let ty2 = inf_ctx.solution_of_node(expr2.id()).unwrap();
            let ty = SolvedType::Function(vec![ty1, ty2], SolvedType::Bool.into());
            let func_name = match opcode {
                BinOpcode::Equals => "equals",
                BinOpcode::LessThan => "less_than",
                BinOpcode::LessThanOrEqual => "less_than_or_equal",
                BinOpcode::GreaterThan => "greater_than",
                BinOpcode::GreaterThanOrEqual => "greater_than_or_equal",
                _ => unreachable!(),
            }
            .to_owned();
            let ty = monomorphize_overloaded_var(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                overloaded_func_map,
                &func_name,
                ty,
            )
            .expect("could not overload equals operator");

            Rc::new(Ete::FuncAp(
                Rc::new(Ete::VarOverloaded(func_name, ty)),
                vec![
                    translate_expr(
                        inf_ctx,
                        monomorphenv.clone(),
                        gamma.clone(),
                        node_map,
                        overloaded_func_map,
                        expr1.exprkind.clone(),
                        expr1.id,
                    ),
                    translate_expr(
                        inf_ctx,
                        monomorphenv,
                        gamma,
                        node_map,
                        overloaded_func_map,
                        expr2.exprkind.clone(),
                        expr2.id,
                    ),
                ],
                None,
            ))
        }
        ASTek::BinOp(
            expr1,
            opcode @ (BinOpcode::Add
            | BinOpcode::Subtract
            | BinOpcode::Multiply
            | BinOpcode::Divide
            | BinOpcode::Pow),
            expr2,
        ) => {
            let ty1 = inf_ctx.solution_of_node(expr1.id()).unwrap();
            let ty2 = inf_ctx.solution_of_node(expr2.id()).unwrap();
            let ty = SolvedType::Function(vec![ty1.clone(), ty2], ty1.into());
            let func_name = match opcode {
                BinOpcode::Add => "add",
                BinOpcode::Subtract => "minus",
                BinOpcode::Multiply => "multiply",
                BinOpcode::Divide => "divide",
                BinOpcode::Pow => "pow",
                _ => unreachable!(),
            }
            .to_owned();
            let ty = monomorphize_overloaded_var(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                overloaded_func_map,
                &func_name,
                ty,
            )
            .unwrap_or_else(|| panic!("could not overload {func_name} operator"));

            Rc::new(Ete::FuncAp(
                Rc::new(Ete::VarOverloaded(func_name, ty)),
                vec![
                    translate_expr(
                        inf_ctx,
                        monomorphenv.clone(),
                        gamma.clone(),
                        node_map,
                        overloaded_func_map,
                        expr1.exprkind.clone(),
                        expr1.id,
                    ),
                    translate_expr(
                        inf_ctx,
                        monomorphenv,
                        gamma,
                        node_map,
                        overloaded_func_map,
                        expr2.exprkind.clone(),
                        expr2.id,
                    ),
                ],
                None,
            ))
        }
        ASTek::BinOp(expr1, op, expr2) => Rc::new(Ete::BinOp(
            translate_expr(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                overloaded_func_map,
                expr1.exprkind.clone(),
                expr1.id,
            ),
            *op,
            translate_expr(
                inf_ctx,
                monomorphenv,
                gamma,
                node_map,
                overloaded_func_map,
                expr2.exprkind.clone(),
                expr2.id,
            ),
        )),
        ASTek::Block(stmts) => translate_expr_block(
            inf_ctx,
            monomorphenv,
            gamma,
            node_map,
            overloaded_func_map,
            stmts.clone(),
            None,
        ),
        ASTek::Func(func_args, _, body) => translate_expr_func(
            inf_ctx,
            monomorphenv,
            gamma,
            node_map,
            overloaded_func_map,
            func_args.clone(),
            body.clone(),
        ),
        ASTek::FuncAp(expr1, exprs) => translate_expr_ap(
            inf_ctx,
            monomorphenv,
            gamma,
            node_map,
            overloaded_func_map,
            expr1.clone(),
            exprs.clone(),
        ),
        ASTek::If(expr1, expr2, expr3) => match expr3 {
            // if-else
            Some(expr3) => Rc::new(Ete::If(
                translate_expr(
                    inf_ctx,
                    monomorphenv.clone(),
                    gamma.clone(),
                    node_map,
                    overloaded_func_map,
                    expr1.exprkind.clone(),
                    expr1.id,
                ),
                translate_expr(
                    inf_ctx,
                    monomorphenv.clone(),
                    gamma.clone(),
                    node_map,
                    overloaded_func_map,
                    expr2.exprkind.clone(),
                    expr2.id,
                ),
                translate_expr(
                    inf_ctx,
                    monomorphenv,
                    gamma,
                    node_map,
                    overloaded_func_map,
                    expr3.exprkind.clone(),
                    expr3.id,
                ),
            )),
            // just
            None => Rc::new(Ete::If(
                translate_expr(
                    inf_ctx,
                    monomorphenv.clone(),
                    gamma.clone(),
                    node_map,
                    overloaded_func_map,
                    expr1.exprkind.clone(),
                    expr1.id,
                ),
                translate_expr(
                    inf_ctx,
                    monomorphenv,
                    gamma,
                    node_map,
                    overloaded_func_map,
                    expr2.exprkind.clone(),
                    expr2.id,
                ),
                Rc::new(Ete::Unit),
            )),
        },
        ASTek::WhileLoop(cond, expr) => {
            let body = translate_expr(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                overloaded_func_map,
                expr.exprkind.clone(),
                expr.id,
            );
            let cond = translate_expr(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                overloaded_func_map,
                cond.exprkind.clone(),
                cond.id,
            );
            Rc::new(Ete::WhileLoop(cond.clone(), cond, body.clone(), body))
        }
        ASTek::Match(expr, arms) => {
            let mut translated_arms = Vec::new();
            for arm in arms {
                translated_arms.push((
                    translate_pat(arm.pat.clone()),
                    translate_expr(
                        inf_ctx,
                        monomorphenv.clone(),
                        gamma.clone(),
                        node_map,
                        overloaded_func_map,
                        arm.expr.exprkind.clone(),
                        arm.expr.id,
                    ),
                ));
            }
            Rc::new(Ete::Match(
                translate_expr(
                    inf_ctx,
                    monomorphenv,
                    gamma,
                    node_map,
                    overloaded_func_map,
                    expr.exprkind.clone(),
                    expr.id,
                ),
                translated_arms,
            ))
        }
        ASTek::FieldAccess(accessed, field) => {
            let accessed = translate_expr(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                overloaded_func_map,
                accessed.exprkind.clone(),
                accessed.id,
            );
            let ASTek::Var(field_ident) = &*field.exprkind else {
                panic!()
            };
            Rc::new(Ete::FieldAccess(accessed, field_ident.clone()))
        }
        ASTek::IndexAccess(expr, index) => {
            let expr = translate_expr(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                overloaded_func_map,
                expr.exprkind.clone(),
                expr.id,
            );
            let index = translate_expr(
                inf_ctx,
                monomorphenv,
                gamma,
                node_map,
                overloaded_func_map,
                index.exprkind.clone(),
                index.id,
            );
            Rc::new(Ete::IndexAccess(expr, index))
        }
    }
}

type OverloadedFuncMapTemp = HashMap<(eval_tree::Identifier, Monotype), Option<Rc<Ete>>>;

fn strip_temp_overloaded_func_map(
    overloaded_func_map_temp: &OverloadedFuncMapTemp,
) -> interpreter::OverloadedFuncMap {
    let mut overloaded_func_map = HashMap::new();
    for ((ident, interface_instance), ete) in overloaded_func_map_temp.iter() {
        overloaded_func_map.insert(
            (ident.clone(), interface_instance.clone()),
            ete.clone().unwrap(),
        );
    }
    overloaded_func_map
}

pub(crate) fn translate(
    inf_ctx: &InferenceContext,
    gamma: Gamma,
    node_map: &NodeMap,
    toplevels: &Vec<Rc<ast::Toplevel>>,
    env: EvalEnv,
) -> (Rc<Ete>, interpreter::OverloadedFuncMap) {
    let mut overloaded_func_map_temp = OverloadedFuncMapTemp::new();
    let monomorphenv = MonomorphEnv::empty();
    let mut statements = Vec::new();
    for toplevel in toplevels {
        for s in &toplevel.statements {
            statements.push(s.clone());
        }
    }
    let toplevel = translate_expr_block(
        inf_ctx,
        monomorphenv,
        gamma,
        node_map,
        &mut overloaded_func_map_temp,
        statements,
        Some(env),
    );
    let overloaded_func_map = strip_temp_overloaded_func_map(&overloaded_func_map_temp);
    (toplevel, overloaded_func_map)
}
