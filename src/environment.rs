use crate::eval_tree::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

pub struct Environment {
    vars: HashMap<Identifier, Rc<Expr>>,
    enclosing: Option<Rc<RefCell<Environment>>>,
}

impl Environment {
    pub fn debug_helper(&self) -> Vec<String> {
        let mut current = Vec::new();
        for (key, value) in &self.vars {
            match &*value.clone() {
                Expr::Int(n) => {
                    let mut s = key.clone();
                    s.push('=');
                    s.push_str(n.to_string().as_str());
                    current.push(s);
                }
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

impl fmt::Debug for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment(\n{:?}\n)", Environment::debug_helper(self))
    }
}

impl Environment {
    pub fn new(enclosing: Option<Rc<RefCell<Environment>>>) -> Self {
        Self {
            vars: HashMap::new(),
            enclosing,
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
        self.vars.insert(id.clone(), expr);
    }
}
