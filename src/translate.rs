use crate::ast;
use crate::eval_tree;
use std::rc::Rc;

type ASTek = ast::ExprKind;
type Ete = eval_tree::Expr;

type ASTpk = ast::PatKind;
type Etp = eval_tree::Pat;

pub fn translate_pat(parse_tree: Rc<ast::Pat>) -> Rc<Etp> {
    match &*parse_tree.patkind {
        ASTpk::Var(id) => Rc::new(Etp::Var(id.clone())),
        ASTpk::Tuple(pats) => Rc::new(Etp::Tuple(
            pats.iter().map(|pat| translate_pat(pat.clone())).collect(),
        )),
    }
}

pub fn translate_expr_block(stmts: Vec<Rc<ast::Stmt>>) -> Rc<Ete> {
    match stmts.len() {
        0 => Rc::new(Ete::Unit),
        1 => {
            let statement = &stmts[0];
            match &*statement.stmtkind {
                ast::StmtKind::LetFunc(pat, func_args, _, body) => {
                    let id = pat.patkind.get_identifier();
                    let func = translate_expr_func(func_args.clone(), body.exprkind.clone());
                    Rc::new(Ete::Let(
                        Rc::new(Etp::Var(id)),
                        func,
                        translate_expr_block(stmts[1..].to_vec()),
                    ))
                }
                ast::StmtKind::Let(_, e) | ast::StmtKind::Expr(e) => {
                    translate_expr(e.exprkind.clone())
                }
            }
        }
        _ => {
            let statement = &stmts[0];
            match &*statement.stmtkind {
                ast::StmtKind::LetFunc(pat, func_args, _, body) => {
                    let id = pat.patkind.get_identifier();
                    let func = translate_expr_func(func_args.clone(), body.exprkind.clone());
                    Rc::new(Ete::Let(
                        Rc::new(Etp::Var(id)),
                        func,
                        translate_expr_block(stmts[1..].to_vec()),
                    ))
                }
                ast::StmtKind::Let((pat, _), expr) => Rc::new(Ete::Let(
                    translate_pat(pat.clone()),
                    translate_expr(expr.exprkind.clone()),
                    translate_expr_block(stmts[1..].to_vec()),
                )),
                ast::StmtKind::Expr(expr) => Rc::new(Ete::Let(
                    Rc::new(eval_tree::Pat::Var("_".to_string())), // TODO anandduk: add actual wildcard
                    translate_expr(expr.exprkind.clone()),
                    translate_expr_block(stmts[1..].to_vec()),
                )),
            }
        }
    }
}

pub fn translate_expr_func(func_args: Vec<ast::PatAnnotated>, body: Rc<ASTek>) -> Rc<Ete> {
    let id = func_args[0].0.patkind.get_identifier(); // TODO: allow function arguments to be patterns
    if func_args.len() == 1 {
        Rc::new(Ete::Func(id, translate_expr(body), None))
    } else {
        // currying
        let rest_of_function = translate_expr_func(func_args[1..].to_vec(), body);
        Rc::new(Ete::Func(id, rest_of_function, None))
    }
}

pub fn translate_expr_ap(expr1: Rc<ASTek>, expr2: Rc<ASTek>, exprs: Vec<Rc<ASTek>>) -> Rc<Ete> {
    if exprs.is_empty() {
        Rc::new(Ete::FuncAp(
            translate_expr(expr1),
            translate_expr(expr2),
            None,
        ))
    } else {
        // currying
        let rest_of_arguments_applied =
            translate_expr_ap(expr1, expr2, exprs[..exprs.len() - 1].to_vec());
        Rc::new(Ete::FuncAp(
            rest_of_arguments_applied,
            translate_expr(exprs.last().unwrap().clone()),
            None,
        ))
    }
}

pub fn translate_expr(parse_tree: Rc<ASTek>) -> Rc<Ete> {
    match &*parse_tree {
        ASTek::Var(id) => Rc::new(Ete::Var(id.clone())),
        ASTek::Unit => Rc::new(Ete::Unit),
        ASTek::Int(i) => Rc::new(Ete::Int(*i)),
        ASTek::Bool(b) => Rc::new(Ete::Bool(*b)),
        ASTek::Str(s) => Rc::new(Ete::Str(s.clone())),
        ASTek::Tuple(exprs) => {
            let mut translated_exprs = Vec::new();
            for expr in exprs {
                translated_exprs.push(translate_expr(expr.exprkind.clone()));
            }
            Rc::new(Ete::Tuple(translated_exprs))
        }
        ASTek::BinOp(expr1, op, expr2) => Rc::new(Ete::BinOp(
            translate_expr(expr1.exprkind.clone()),
            *op,
            translate_expr(expr2.exprkind.clone()),
        )),
        ASTek::Block(stmts) => translate_expr_block(stmts.clone()),
        ASTek::Func(func_args, _, body) => {
            translate_expr_func(func_args.clone(), body.exprkind.clone())
        }
        ASTek::FuncAp(expr1, exprs) => translate_expr_ap(
            expr1.exprkind.clone(),
            exprs[0].exprkind.clone(),
            exprs[1..]
                .iter()
                .map(|expr| expr.exprkind.clone())
                .collect(),
        ),
        ASTek::If(expr1, expr2, expr3) => Rc::new(Ete::If(
            translate_expr(expr1.exprkind.clone()),
            translate_expr(expr2.exprkind.clone()),
            translate_expr(expr3.exprkind.clone()),
        )),
    }
}
