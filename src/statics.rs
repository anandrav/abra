use crate::ast::*;
use crate::operators::BinOpcode;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

pub struct Constraint {
    expected: Type,
    actual: Type,
    cause: Span,
}

pub struct TyCtx {
    vars: HashMap<Identifier, Rc<Type>>,
    enclosing: Option<Rc<RefCell<TyCtx>>>,
}

// TODO reuse Environment instead of making a new struct
impl TyCtx {
    pub fn debug_helper(&self) -> Vec<String> {
        let mut current = Vec::new();
        for (key, value) in &self.vars {
            match &*value.clone() {
                _ => current.push(key.clone()),
            }
        }
        match &self.enclosing {
            Some(env) => {
                let mut all = env.borrow_mut().debug_helper();
                all.append(&mut current);
                all
            }
            None => current,
        }
    }
}

impl fmt::Debug for TyCtx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment(\n{:?}\n)", TyCtx::debug_helper(self))
    }
}

impl TyCtx {
    pub fn empty() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            vars: HashMap::new(),
            enclosing: None,
        }))
    }

    pub fn new(enclosing: Option<Rc<RefCell<TyCtx>>>) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            vars: HashMap::new(),
            enclosing,
        }))
    }

    pub fn lookup(&self, id: &Identifier) -> Option<Rc<Type>> {
        match self.vars.get(id) {
            Some(typ) => Some(typ.clone()),
            None => match &self.enclosing {
                Some(env) => env.borrow_mut().lookup(id),
                None => None,
            },
        }
    }

    pub fn extend(&mut self, id: &Identifier, typ: Rc<Type>) {
        self.vars.insert(id.clone(), typ);
    }
}

pub enum Mode {
    Syn,
    Ana(Type),
}

pub fn collect_constraints(
    ctx: Rc<RefCell<TyCtx>>,
    mode: Mode,
    expr: Rc<Expr>,
    constraints: &mut Vec<Constraint>,
) {
    print!("collect_constraints: {:#?} ", expr);
    match &*expr.exprkind {
        ExprKind::Unit => match mode {
            Mode::Syn => (),
            Mode::Ana(expected) => constraints.push(Constraint {
                expected,
                actual: Type::Unit,
                cause: expr.span.clone(),
            }),
        },
        ExprKind::Int(_) => match mode {
            Mode::Syn => (),
            Mode::Ana(expected) => constraints.push(Constraint {
                expected,
                actual: Type::Int,
                cause: expr.span.clone(),
            }),
        },
        ExprKind::Bool(_) => match mode {
            Mode::Syn => (),
            Mode::Ana(expected) => constraints.push(Constraint {
                expected,
                actual: Type::Bool,
                cause: expr.span.clone(),
            }),
        },
        ExprKind::Str(_) => match mode {
            Mode::Syn => (),
            Mode::Ana(expected) => constraints.push(Constraint {
                expected,
                actual: Type::String,
                cause: expr.span.clone(),
            }),
        },
        ExprKind::Var(_) => unimplemented!(),
        // ExprKind::BinOp(_, op, _) => match op {
        //     BinOpcode::Add | BinOpcode::Subtract | BinOpcode::Multiply | BinOpcode::Divide => {
        //         Rc::new(Type::Int)
        //     }
        //     BinOpcode::Equals | BinOpcode::LessThan | BinOpcode::GreaterThan => Rc::new(Type::Bool),
        // },
        // ExprKind::Block(_statements, opt_expr) => match &*opt_expr {
        //     Some(expr) => collect_constraints(TyCtx::empty(), mode, expr.clone(), constraints),
        //     None => Rc::new(Type::Unit),
        // },
        // ExprKind::Func(arg, args, opt_typ_body, body) => {
        //     let mut ctx = TyCtx::new(Some(ctx.clone()));
        //     let (id, arg_annot) = arg;
        //     match arg_annot {
        //         Some(typ) => ctx.borrow_mut().extend(id, typ.clone()),
        //         None => (),
        //     };
        //     for arg in args {
        //         let (id, arg_annot) = arg;
        //         match arg_annot {
        //             Some(typ) => ctx.borrow_mut().extend(id, typ.clone()),
        //             None => (),
        //         };
        //     }
        //     let typ_out = match opt_typ_body {
        //         Some(typ) => typ.clone(),
        //         None => collect_constraints(ctx.clone(), Mode::Syn, body.clone(), constraints),
        //     };
        //     match mode {
        //         Mode::Syn => unimplemented!(),
        //         Mode::Ana(t) => unimplemented!(),
        //     }
        // }
        ExprKind::FuncAp(_, _, _) => unimplemented!(),
        _ => unimplemented!(),
    }
}
