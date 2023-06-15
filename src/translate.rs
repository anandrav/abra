use crate::ast;
use crate::ast::NodeMap;
use crate::eval_tree;
use crate::statics::Gamma;
use crate::statics::InferenceContext;
use crate::statics::NamedMonomorphType;
use crate::statics::Prov;
use crate::statics::Type;
use crate::statics::UnifVar;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::rc::Rc;

type ASTek = ast::ExprKind;
type Ete = eval_tree::Expr;

type ASTpk = ast::PatKind;
type Etp = eval_tree::Pat;

#[derive(Debug, Clone)]
pub struct UnifVarCompWrapper {
    pub unifvar: UnifVar,
}

impl UnifVarCompWrapper {
    pub fn new(unifvar: UnifVar) -> Self {
        Self { unifvar }
    }
}

impl PartialEq for UnifVarCompWrapper {
    fn eq(&self, other: &Self) -> bool {
        self.unifvar.equiv(&other.unifvar)
    }
}

impl Eq for UnifVarCompWrapper {}

impl PartialOrd for UnifVarCompWrapper {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self == other {
            Some(std::cmp::Ordering::Equal)
        } else {
            self.unifvar.partial_cmp(&other.unifvar)
        }
    }
}
impl Ord for UnifVarCompWrapper {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self == other {
            std::cmp::Ordering::Equal
        } else {
            self.unifvar.cmp(&other.unifvar)
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub struct MonomorphEnv {
    vars: BTreeMap<UnifVarCompWrapper, NamedMonomorphType>,
    enclosing: Option<Rc<RefCell<MonomorphEnv>>>,
}

impl MonomorphEnv {
    pub fn new(enclosing: Option<Rc<RefCell<MonomorphEnv>>>) -> Self {
        Self {
            vars: BTreeMap::new(),
            enclosing,
        }
    }

    pub fn lookup(&self, key: &UnifVarCompWrapper) -> Option<NamedMonomorphType> {
        match self.vars.get(key) {
            Some(expr) => Some(expr.clone()),
            None => match &self.enclosing {
                Some(env) => env.borrow_mut().lookup(key),
                None => None,
            },
        }
    }

    pub fn extend(&mut self, key: &UnifVarCompWrapper, expr: NamedMonomorphType) {
        self.vars.insert(key.clone(), expr);
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
            gamma.clone(),
            node_map,
            stmts[1..].to_vec(),
        ),
        ast::StmtKind::LetFunc(pat, func_args, _, body) => {
            let id = pat.patkind.get_identifier_of_variable();
            let func = translate_expr_func(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                func_args.clone(),
                body.clone(),
            );
            Rc::new(Ete::Let(
                Rc::new(Etp::Var(id)),
                func,
                translate_expr_block(
                    inf_ctx,
                    monomorphenv.clone(),
                    gamma.clone(),
                    node_map,
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
                expr.exprkind.clone(),
                expr.id,
            ),
            translate_expr_block(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                stmts[1..].to_vec(),
            ),
        )),
        ast::StmtKind::Expr(e) if stmts.len() == 1 => translate_expr(
            inf_ctx,
            monomorphenv,
            gamma.clone(),
            node_map,
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
                expr.exprkind.clone(),
                expr.id,
            ),
            translate_expr_block(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
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
    func_args: Vec<ast::ArgAnnotated>,
    body: Rc<ast::Expr>,
) -> Rc<Ete> {
    let id = func_args[0].0.patkind.get_identifier_of_variable(); // TODO: allow function arguments to be patterns
    if func_args.len() == 1 {
        Rc::new(Ete::Func(
            id,
            translate_expr(
                inf_ctx,
                monomorphenv,
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
            monomorphenv,
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
    monomorphenv: Rc<RefCell<MonomorphEnv>>,
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
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                expr1.exprkind.clone(),
                expr1.id,
            ),
            translate_expr(
                inf_ctx,
                monomorphenv.clone(),
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
            monomorphenv.clone(),
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
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                last.exprkind.clone(),
                last.id,
            ),
            None,
        ))
    }
}

pub fn inf_ty_of_node(
    inf_ctx: &InferenceContext,
    node_map: &NodeMap,
    node_id: ast::Id,
) -> Option<Type> {
    println!("named_monomorphic_type_of_node");
    let unifvar = inf_ctx.vars.get(&Prov::Node(node_id)).unwrap();
    Some(Type::UnifVar(unifvar.clone()))
}

pub fn named_monomorphic_type_of_node(
    inf_ctx: &InferenceContext,
    node_map: &NodeMap,
    node_id: ast::Id,
) -> Option<NamedMonomorphType> {
    println!("named_monomorphic_type_of_node");
    let unifvar = inf_ctx.vars.get(&Prov::Node(node_id)).unwrap();
    let solved_ty = unifvar.clone_data().solution().unwrap();
    println!("solved_ty: {}", solved_ty);
    if let Some(named_ty) = solved_ty.named_type() {
        println!("named_ty: {:?}", named_ty);
        Some(named_ty.clone())
    } else {
        None
    }
}

pub fn inf_ty_of_identifier(
    inf_ctx: &InferenceContext,
    gamma: Rc<RefCell<Gamma>>,
    node_map: &NodeMap,
    ident: &ast::Identifier,
) -> Option<Type> {
    println!("inf_ty_of_identifier");
    println!("ident: {}", ident);
    let gamma = gamma.borrow();
    let inf_ty = gamma.vars.get(ident).cloned();
    println!("inf_ty: {:?}", inf_ty);
    inf_ty
}

pub fn solved_ty_of_identifier(
    inf_ctx: &InferenceContext,
    gamma: Rc<RefCell<Gamma>>,
    node_map: &NodeMap,
    ident: &ast::Identifier,
) -> Option<Type> {
    println!("solved_ty_of_identifier");
    println!("ident: {}", ident);
    let gamma = gamma.borrow();
    let ty = gamma.vars.get(ident)?;
    println!("it's in the gamma");
    let solved = ty.solution().unwrap();
    println!("solved_ty: {}", solved);
    Some(solved)
}

pub fn update_monomorphenv(
    monomorphenv: Rc<RefCell<MonomorphEnv>>,
    inf_ty: Type,
    named_monomorph_ty: NamedMonomorphType,
) {
    if let Type::UnifVar(unifvar) = inf_ty.clone() {
        let mut m = monomorphenv.borrow_mut();
        m.extend(
            &UnifVarCompWrapper::new(unifvar),
            named_monomorph_ty.clone(),
        );
    }
    match (inf_ty.clone(), named_monomorph_ty.clone()) {
        // recurse
        (Type::Function(_, args, out), NamedMonomorphType::Function(args2, out2)) => {
            for i in 0..args.len() {
                println!("recursing!!!!!");
                update_monomorphenv(monomorphenv.clone(), args[i].clone(), args2[i].clone());
            }
            update_monomorphenv(monomorphenv.clone(), *out.clone(), *out2.clone());
        }
        (Type::UnifVar(unifvar), _) => {
            let data = unifvar.clone_data();
            for (_key, ty) in data.types {
                update_monomorphenv(monomorphenv.clone(), ty, named_monomorph_ty.clone());
            }
        }
        _ => {}
    }
}

// ANAND YOU WERE LAST HERE! YOU CAN JUST BLINDLY SUBSTITUTE POLYMORPHIC VARIABLES BASED ON THEIR SYMBOL, IT WILL WORK
pub fn specialize_type(
    inf_ctx: &InferenceContext,
    monomorphenv: Rc<RefCell<MonomorphEnv>>,
    inf_ty: Type,
) -> Option<NamedMonomorphType> {
    if let Type::UnifVar(unifvar) = inf_ty.clone() {
        let mut m = monomorphenv.borrow_mut();
        let lookup = m.lookup(&UnifVarCompWrapper::new(unifvar));
        if lookup.is_some() {
            return lookup;
        }
    } else {
        let provs = inf_ty.provs().borrow();
        let prov = provs.first().unwrap();
        let unifvar = inf_ctx.vars.get(&prov).unwrap();
        let lookup = monomorphenv
            .borrow_mut()
            .lookup(&UnifVarCompWrapper::new(unifvar.clone()));
        if lookup.is_some() {
            return lookup;
        }
    }
    match inf_ty.clone() {
        // recurse
        Type::Function(_, args, out) => {
            let mut args2 = vec![];
            for i in 0..args.len() {
                let arg2 = specialize_type(inf_ctx, monomorphenv.clone(), args[i].clone())?;
                args2.push(arg2);
            }
            let out2 = specialize_type(inf_ctx, monomorphenv.clone(), *out.clone())?;
            Some(NamedMonomorphType::Function(args2, out2.into()))
        } // (Type::UnifVar(unifvar), _) => {
        //     let data = unifvar.clone_data();
        //     for (_key, ty) in data.types {
        //         update_monomorphenv(monomorphenv.clone(), ty, named_monomorph_ty.clone());
        //     }
        // }
        _ => inf_ty.solution().unwrap().named_type(),
    }
}

pub fn get_func_definition_node(
    inf_ctx: &InferenceContext,
    node_map: &NodeMap,
    ident: &ast::Identifier,
    named_monomorph_ty: NamedMonomorphType,
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
                    if let Some(named_ty_impl) = solved_ty.named_type() {
                        println!("named_ty_impl: {:?}", named_ty_impl);
                        if (named_monomorph_ty == named_ty_impl) {
                            println!("THEY ARE EQUAL!!!!!!!!");
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
    parse_tree: Rc<ASTek>,
    ast_id: ast::Id,
) -> Rc<Ete> {
    match &*parse_tree {
        ASTek::Var(ident) => {
            // if let Some(inf_ty) = inf_ty_of_node(inf_ctx, node_map, ast_id) {
            //     // if let Some(inf_ty) = inf_ty_of_identifier(inf_ctx, gamma.clone(), node_map, ident) {
            //     if let Some(st) = solved_ty_of_identifier(inf_ctx, gamma.clone(), node_map, ident) {
            //         if st.is_overloaded() {
            //             println!("{} is overloaded", st);
            //             println!("overloaded node's type is: {}", inf_ty);
            //             dbg!(monomorphenv.borrow());
            //             if let Some(nt) = named_monomorphic_type_of_node(inf_ctx, node_map, ast_id)
            //             {
            //                 println!("specialized, add to env");
            //                 // println!("which is:");
            //                 // dbg!(&inf_ty);
            //                 let monomorphenv =
            //                     Rc::new(RefCell::new(MonomorphEnv::new(Some(monomorphenv))));
            //                 update_monomorphenv(monomorphenv.clone(), inf_ty, nt.clone());
            //                 dbg!(&monomorphenv);
            //                 let func_node = get_func_definition_node(inf_ctx, node_map, ident, nt);
            //                 let func_node_id = func_node.id();
            //                 let method_node = Rc::new(func_node.into_stmt().unwrap());
            //                 if let ast::StmtKind::LetFunc(_, args, _, body) = &*method_node.stmtkind
            //                 {
            //                     println!("it's a let func");
            //                     return translate_expr_func(
            //                         inf_ctx,
            //                         monomorphenv,
            //                         gamma,
            //                         node_map,
            //                         args.clone(),
            //                         body.clone(),
            //                     );
            //                 }
            //             } else {
            //                 println!("not specialized, must specialize using env");
            //                 println!("want to specialize inf_ty from node: {}", inf_ty);
            //                 if let Some(specialized_ty) =
            //                     specialize_type(inf_ctx, monomorphenv.clone(), inf_ty)
            //                 {
            //                     println!("specialized_ty: {:?}", specialized_ty);
            //                     let func_node = get_func_definition_node(
            //                         inf_ctx,
            //                         node_map,
            //                         ident,
            //                         specialized_ty,
            //                     );
            //                     let func_node_id = func_node.id();
            //                     let method_node = Rc::new(func_node.into_stmt().unwrap());
            //                     if let ast::StmtKind::LetFunc(_, args, _, body) =
            //                         &*method_node.stmtkind
            //                     {
            //                         println!("it's a let func");
            //                         return translate_expr_func(
            //                             inf_ctx,
            //                             monomorphenv,
            //                             gamma,
            //                             node_map,
            //                             args.clone(),
            //                             body.clone(),
            //                         );
            //                     }
            //                 } else {
            //                     println!("couldn't specialize");
            //                 }
            //             }
            //         } else {
            //             println!("{} is NOT overloaded", st);
            //         }
            //     }
            // }
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
            return Rc::new(Ete::Var(ident.clone()));
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
                expr1.exprkind.clone(),
                expr1.id,
            ),
            *op,
            translate_expr(
                inf_ctx,
                monomorphenv.clone(),
                gamma.clone(),
                node_map,
                expr2.exprkind.clone(),
                expr2.id,
            ),
        )),
        ASTek::Block(stmts) => translate_expr_block(
            inf_ctx,
            monomorphenv,
            gamma.clone(),
            node_map,
            stmts.clone(),
        ),
        ASTek::Func(func_args, _, body) => translate_expr_func(
            inf_ctx,
            monomorphenv,
            gamma.clone(),
            node_map,
            func_args.clone(),
            body.clone(),
        ),
        ASTek::FuncAp(expr1, exprs) => translate_expr_ap(
            inf_ctx,
            monomorphenv,
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
                    monomorphenv.clone(),
                    gamma.clone(),
                    node_map,
                    expr1.exprkind.clone(),
                    expr1.id,
                ),
                translate_expr(
                    inf_ctx,
                    monomorphenv.clone(),
                    gamma.clone(),
                    node_map,
                    expr2.exprkind.clone(),
                    expr2.id,
                ),
                translate_expr(
                    inf_ctx,
                    monomorphenv.clone(),
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
                    monomorphenv.clone(),
                    gamma.clone(),
                    node_map,
                    expr1.exprkind.clone(),
                    expr1.id,
                ),
                translate_expr(
                    inf_ctx,
                    monomorphenv.clone(),
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
                        monomorphenv.clone(),
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
                    monomorphenv,
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
    dbg!(gamma.borrow());

    let monomorphenv = Rc::new(RefCell::new(MonomorphEnv::new(None)));
    translate_expr_block(
        inf_ctx,
        monomorphenv,
        gamma.clone(),
        node_map,
        toplevel.statements.clone(),
    )
}
