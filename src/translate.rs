use ast;
use environment::Environment;
use eval_tree;
use std::cell::RefCell;
use std::rc::Rc;
use types::Type;

type ASTek = ast::ExprKind;
type Ete = eval_tree::Expr;

type ASTpk = ast::PatKind;
type Etp = eval_tree::Pat;

type ASTs = ast::StmtKind;

pub fn translate_pat(parse_tree: Rc<ast::Pat>) -> Rc<Etp> {
    match &*parse_tree.patkind {
        ASTpk::Var(id) => Rc::new(Etp::Var(id.clone())),
        _ => unimplemented!(),
    }
}

pub fn translate_expr_block(stmts: Vec<Rc<ast::Stmt>>) -> Rc<Ete> {
    match stmts.len() {
        0 => panic!("empty expression block!"),
        1 => {
            let statement = &stmts[0];
            match &*statement.stmtkind {
                ast::StmtKind::EmptyHole => {
                    panic!("empty hole found during translation")
                }
                ast::StmtKind::Let(..) => {
                    panic!("let statement on last line of block")
                }
                ast::StmtKind::Expr(e) => translate_expr(e.exprkind.clone()),
            }
        }
        _ => {
            let statement = &stmts[0];
            match &*statement.stmtkind {
                ast::StmtKind::EmptyHole => {
                    panic!("empty hole found during translation")
                }
                ast::StmtKind::Let(pat, _, expr) => Rc::new(Ete::Let(
                    translate_pat(pat.clone()),
                    translate_expr(expr.exprkind.clone()),
                    translate_expr_block(stmts[1..].to_vec()),
                )),
                ast::StmtKind::Expr(expr) => Rc::new(Ete::Let(
                    Rc::new(eval_tree::Pat::Var("_".to_string())),
                    translate_expr(expr.exprkind.clone()),
                    translate_expr_block(stmts[1..].to_vec()),
                )),
            }
        }
    }
}

pub fn translate_expr_func(
    (id, _): ast::FuncArg,
    func_args: Vec<ast::FuncArg>,
    body: Rc<ASTek>,
) -> Rc<Ete> {
    if func_args.is_empty() {
        Rc::new(Ete::Func(id.clone(), translate_expr(body.clone()), None))
    } else {
        // currying
        let rest_of_function =
            translate_expr_func(func_args[0].clone(), func_args[1..].to_vec(), body.clone());
        Rc::new(Ete::Func(id.clone(), rest_of_function, None))
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
            translate_expr_ap(expr1.clone(), expr2, exprs[..exprs.len() - 1].to_vec());
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
        ASTek::BinOp(expr1, op, expr2) => Rc::new(Ete::BinOp(
            translate_expr(expr1.exprkind.clone()),
            *op,
            translate_expr(expr2.exprkind.clone()),
        )),
        ASTek::Block(stmts) => translate_expr_block(stmts.clone()),
        // ASTek::Let(pat, _, expr1, expr2) => Rc::new(Ete::Let(
        //     translate_pat(pat.clone()),
        //     translate_expr(expr1.clone()),
        //     translate_expr(expr2.clone()),
        // )),
        ASTek::Func(func_arg, func_args, _, body) => {
            translate_expr_func(func_arg.clone(), func_args.clone(), body.exprkind.clone())
        }
        ASTek::FuncAp(expr1, expr2, exprs) => translate_expr_ap(
            expr1.exprkind.clone(),
            expr2.exprkind.clone(),
            exprs.iter().map(|expr| expr.exprkind.clone()).collect(),
        ),
        ASTek::If(expr1, expr2, expr3) => Rc::new(Ete::If(
            translate_expr(expr1.exprkind.clone()),
            translate_expr(expr2.exprkind.clone()),
            translate_expr(expr3.exprkind.clone()),
        )),
        _ => unimplemented!(),
    }
}
