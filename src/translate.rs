use crate::ast;
use crate::ast::Node;
use crate::ast::NodeMap;
use crate::eval_tree;
use crate::interpreter;
use crate::statics::Gamma;
use crate::statics::InferenceContext;
use crate::statics::Prov;
use crate::statics::Type;
use crate::statics::TypeFullyInstantiated;
use crate::statics::TypeInterfaceImpl;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::rc::Rc;

type ASTek = ast::ExprKind;
type Ete = eval_tree::Expr;

type ASTpk = ast::PatKind;
type Etp = eval_tree::Pat;

#[derive(PartialEq, Eq, Debug)]
pub struct MonomorphEnv {
    vars: BTreeMap<ast::Identifier, Type>,
    enclosing: Option<Rc<RefCell<MonomorphEnv>>>,
}

impl MonomorphEnv {
    pub fn new(enclosing: Option<Rc<RefCell<MonomorphEnv>>>) -> Self {
        Self {
            vars: BTreeMap::new(),
            enclosing,
        }
    }

    pub fn lookup(&self, key: &ast::Identifier) -> Option<Type> {
        match self.vars.get(key) {
            Some(ty) => Some(ty.clone()),
            None => match &self.enclosing {
                Some(env) => env.borrow_mut().lookup(key),
                None => None,
            },
        }
    }

    pub fn extend(&mut self, key: &ast::Identifier, ty: Type) {
        self.vars.insert(key.clone(), ty);
    }
}

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
    monomorphenv: Rc<RefCell<MonomorphEnv>>,
    gamma: Rc<RefCell<Gamma>>,
    node_map: &NodeMap,
    overloaded_func_map: &mut OverloadedFuncMapTemp,
    stmts: Vec<Rc<ast::Stmt>>,
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
        ),
        ast::StmtKind::LetFunc(pat, func_args, _, body) => {
            let ty = Type::solution_of_node(inf_ctx, pat.id).unwrap();
            if ty.is_overloaded() {
                // if function is overloaded, don't translate its body
                return translate_expr_block(
                    inf_ctx,
                    monomorphenv,
                    gamma,
                    node_map,
                    overloaded_func_map,
                    stmts[1..].to_vec(),
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
                ),
            ))
        }
        ast::StmtKind::Let((pat, _), expr) => Rc::new(Ete::Let(
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
            Rc::new(eval_tree::Pat::Var("_".to_string())), // TODO anandduk: add actual wildcard
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
            ),
        )),
    }
}

pub fn translate_expr_func(
    inf_ctx: &InferenceContext,
    monomorphenv: Rc<RefCell<MonomorphEnv>>,
    gamma: Rc<RefCell<Gamma>>,
    node_map: &NodeMap,
    overloaded_func_map: &mut OverloadedFuncMapTemp,
    func_args: Vec<ast::ArgAnnotated>,
    body: Rc<ast::Expr>,
) -> Rc<Ete> {
    let args = func_args
        .iter()
        .map(|arg| arg.0.patkind.get_identifier_of_variable())
        .collect(); // TODO: allow function arguments to be patterns
                    // if func_args.len() == 1 {
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

pub fn translate_expr_ap(
    inf_ctx: &InferenceContext,
    monomorphenv: Rc<RefCell<MonomorphEnv>>,
    gamma: Rc<RefCell<Gamma>>,
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

pub fn ty_of_global_ident(gamma: Rc<RefCell<Gamma>>, ident: &ast::Identifier) -> Option<Type> {
    // println!("ty_of_global_ident");
    // println!("ident: {}", ident);
    let gamma = gamma.borrow();
    let ty = gamma.vars.get(ident)?;
    // println!("it's in the gamma");
    ty.solution()
    // println!("solved_ty: {}", solved);
}

pub fn update_monomorphenv(
    monomorphenv: Rc<RefCell<MonomorphEnv>>,
    overloaded_ty: Type,
    monomorphic_ty: Type,
) {
    match (overloaded_ty, monomorphic_ty.clone()) {
        // recurse
        (Type::Function(_, args, out), Type::Function(_, args2, out2)) => {
            for i in 0..args.len() {
                update_monomorphenv(monomorphenv.clone(), args[i].clone(), args2[i].clone());
            }
            update_monomorphenv(monomorphenv, *out, *out2);
        }
        (Type::AdtInstance(_, ident, params), Type::AdtInstance(_, ident2, params2)) => {
            assert_eq!(ident, ident2);
            for i in 0..params.len() {
                update_monomorphenv(monomorphenv.clone(), params[i].clone(), params2[i].clone());
            }
        }
        // TODO recurse on tuples and records and adts
        (Type::Poly(_, ident, _), _) => {
            monomorphenv.borrow_mut().extend(&ident, monomorphic_ty);
        }
        _ => {}
    }
}

pub fn subst_with_monomorphic_env(monomorphic_env: Rc<RefCell<MonomorphEnv>>, ty: Type) -> Type {
    match ty {
        Type::Function(provs, args, out) => {
            let new_args = args
                .iter()
                .map(|arg| subst_with_monomorphic_env(monomorphic_env.clone(), arg.clone()))
                .collect();
            let new_out = subst_with_monomorphic_env(monomorphic_env, *out);
            Type::Function(provs, new_args, Box::new(new_out))
        }
        Type::AdtInstance(provs, ident, params) => {
            let new_params = params
                .iter()
                .map(|param| subst_with_monomorphic_env(monomorphic_env.clone(), param.clone()))
                .collect();
            Type::AdtInstance(provs, ident, new_params)
        }
        Type::Poly(_, ref ident, _) => {
            if let Some(monomorphic_ty) = monomorphic_env.borrow().lookup(ident) {
                monomorphic_ty
            } else {
                ty
            }
        }
        _ => ty,
    }
}

pub fn get_func_definition_node(
    inf_ctx: &InferenceContext,
    node_map: &NodeMap,
    ident: &ast::Identifier,
    desired_interface_impl: TypeInterfaceImpl,
) -> Rc<dyn ast::Node> {
    if let Some(interface_name) = inf_ctx.method_to_interface.get(&ident.clone()) {
        println!("interface_name: {:?}", interface_name);
        let impl_list = inf_ctx.interface_impls.get(interface_name).unwrap();
        // find an impl that matches
        dbg!(impl_list);

        for imp in impl_list {
            println!("interface_impl: {:?}", imp);
            for method in &imp.methods {
                println!("method name: {:?}", method.name);
                println!("id: {:?}", ident);
                if method.name == *ident {
                    let method_identifier_node = node_map.get(&method.identifier_location).unwrap();
                    println!("func_node: {:?}", method_identifier_node);
                    let func_id = method_identifier_node.id();
                    let unifvar = inf_ctx.vars.get(&Prov::Node(func_id)).unwrap();
                    let solved_ty = unifvar.clone_data().solution().unwrap();
                    if let Some(interface_impl) = solved_ty.interface_impl_type() {
                        println!("interface_impl: {:?}", interface_impl);
                        println!("desired_interface_impl: {:?}", desired_interface_impl);
                        if desired_interface_impl.clone() == interface_impl {
                            println!("found an impl");
                            let method_node = node_map.get(&method.method_location).unwrap();
                            return method_node.clone();
                        }
                    }
                }
            }
        }
        panic!("couldn't find impl for method");
    } else {
        return inf_ctx.fun_defs.get(ident).unwrap().clone();
    }
}

pub fn translate_expr(
    inf_ctx: &InferenceContext,
    monomorphenv: Rc<RefCell<MonomorphEnv>>,
    gamma: Rc<RefCell<Gamma>>,
    node_map: &NodeMap,
    overloaded_func_map: &mut OverloadedFuncMapTemp,
    parse_tree: Rc<ASTek>,
    ast_id: ast::Id,
) -> Rc<Ete> {
    match &*parse_tree {
        ASTek::Var(ident) => {
            println!("identifier: {ident}");
            if let Some(node_ty) = Type::solution_of_node(inf_ctx, ast_id) {
                if let Some(global_ty) = ty_of_global_ident(gamma.clone(), ident) {
                    if global_ty.is_overloaded() {
                        println!("global_ty: {} (overloaded)", global_ty);
                        println!("node's type is: {},", node_ty);
                        println!("monomorphic env before is: {:?}", monomorphenv.borrow());
                        let substituted_ty = subst_with_monomorphic_env(monomorphenv, node_ty);
                        println!("substituted type: {}", substituted_ty);
                        let instance_ty = substituted_ty.instance_type().unwrap();
                        if let Some(overloaded_func) =
                            overloaded_func_map.get(&(ident.clone(), instance_ty.clone()))
                        {
                            println!("overloaded func: {:?}", overloaded_func);
                            return Rc::new(Ete::VarOverloaded(ident.clone(), instance_ty));
                        }
                        let func_def_node = get_func_definition_node(
                            inf_ctx,
                            node_map,
                            ident,
                            substituted_ty.interface_impl_type().unwrap(),
                        )
                        .to_stmt()
                        .unwrap();
                        let ast::StmtKind::LetFunc(pat, args, _, body) = &*func_def_node.stmtkind else { panic!() };

                        let overloaded_func_ty = Type::solution_of_node(inf_ctx, pat.id()).unwrap();
                        let monomorphenv = Rc::new(RefCell::new(MonomorphEnv::new(None)));
                        update_monomorphenv(
                            monomorphenv.clone(),
                            overloaded_func_ty,
                            substituted_ty.clone(),
                        );
                        println!("monomorphic env after is: {:?}", monomorphenv.borrow());
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
                        overloaded_func_map
                            .insert((ident.clone(), instance_ty.clone()), Some(overloaded_func));
                        return Rc::new(Ete::VarOverloaded(ident.clone(), instance_ty));
                    }
                }
            }
            Rc::new(Ete::Var(ident.clone()))
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
        ASTek::MethodAp(_receiver, _method, _args) => Rc::new(Ete::Unit),
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
    }
}

type OverloadedFuncMapTemp =
    HashMap<(eval_tree::Identifier, TypeFullyInstantiated), Option<Rc<Ete>>>;

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

pub fn translate(
    inf_ctx: &InferenceContext,
    gamma: Rc<RefCell<Gamma>>,
    node_map: &NodeMap,
    toplevel: Rc<ast::Toplevel>,
) -> (Rc<Ete>, interpreter::OverloadedFuncMap) {
    dbg!(gamma.borrow());

    let mut overloaded_func_map_temp = OverloadedFuncMapTemp::new();
    let monomorphenv = Rc::new(RefCell::new(MonomorphEnv::new(None)));
    let toplevel = translate_expr_block(
        inf_ctx,
        monomorphenv,
        gamma,
        node_map,
        &mut overloaded_func_map_temp,
        toplevel.statements.clone(),
    );
    let overloaded_func_map = strip_temp_overloaded_func_map(&overloaded_func_map_temp);
    (toplevel, overloaded_func_map)
}
