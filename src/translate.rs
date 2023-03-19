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
    }
}

pub fn translate_expr_block(
    stmts: Vec<Rc<ast::Stmt>>,
    final_operand: Option<Rc<ast::Expr>>,
) -> Rc<Ete> {
    let final_operand_size = usize::from(final_operand.is_some());
    match stmts.len() + final_operand_size {
        0 => panic!("empty expression block!"),
        1 => match final_operand {
            None => {
                let statement = &stmts[0];
                match &*statement.stmtkind {
                    ast::StmtKind::Let(_, e) | ast::StmtKind::Expr(e) => {
                        translate_expr(e.exprkind.clone())
                    }
                }
            }
            Some(expr) => translate_expr(expr.exprkind.clone()),
        },
        _ => {
            let statement = &stmts[0];
            match &*statement.stmtkind {
                ast::StmtKind::Let((pat, ty_opt), expr) => Rc::new(Ete::Let(
                    translate_pat(pat.clone()),
                    translate_expr(expr.exprkind.clone()),
                    translate_expr_block(stmts[1..].to_vec(), final_operand),
                )),
                ast::StmtKind::Expr(expr) => Rc::new(Ete::Let(
                    Rc::new(eval_tree::Pat::Var("_".to_string())), // TODO anandduk: add actual wildcard
                    translate_expr(expr.exprkind.clone()),
                    translate_expr_block(stmts[1..].to_vec(), final_operand),
                )),
            }
        }
    }
}

pub fn translate_expr_func(func_args: Vec<ast::PatAnnotated>, body: Rc<ASTek>) -> Rc<Ete> {
    let id = func_args[0].0.patkind.get_identifier();
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
        ASTek::BinOp(expr1, op, expr2) => Rc::new(Ete::BinOp(
            translate_expr(expr1.exprkind.clone()),
            *op,
            translate_expr(expr2.exprkind.clone()),
        )),
        ASTek::Block(stmts, final_operand) => {
            translate_expr_block(stmts.clone(), final_operand.clone())
        }
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
        // _ => unimplemented!(),
    }
}
