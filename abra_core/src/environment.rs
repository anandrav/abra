use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use typed_tree::Expr::*;
use typed_tree::*;

#[derive(Debug)]
pub struct Environment {
    vars: HashMap<Identifier, Rc<Expr>>,
    enclosing: Option<Rc<RefCell<Environment>>>,
}

impl Environment {
    pub fn new(enclosing: Option<Rc<RefCell<Environment>>>) -> Self {
        Self {
            vars: HashMap::new(),
            enclosing: enclosing,
        }
    }

    pub fn lookup(&self, id: &Identifier) -> Option<Rc<Expr>> {
        match self.vars.get(id) {
            Some(expr) => Some(expr.clone()),
            None => match &self.enclosing {
                Some(env) => env.borrow_mut().lookup(id),
                None => None,
            },
        }
    }

    pub fn extend(&mut self, id: &Identifier, expr: Rc<Expr>) {
        self.vars.insert(id.clone(), expr.clone());
    }
}
