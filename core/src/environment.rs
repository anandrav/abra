use crate::eval_tree::*;
use std::cell::RefCell;
use std::cmp::Eq;
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::rc::Rc;

pub struct Environment<Identifier: Eq + Hash, Item> {
    items: HashMap<Identifier, Item>,
    enclosing: Option<Box<Environment<Identifier, Item>>>,
}

impl<Identifier: Eq + Hash, Item> Environment<Identifier, Item> {
    pub(crate) fn new(enclosing: Option<Box<Environment<Identifier, Item>>>) -> Self {
        Self {
            items: HashMap::new(),
            enclosing,
        }
    }

    pub(crate) fn lookup<'a>(&'a self, id: &Identifier) -> Option<&'a Item> {
        match self.items.get(id) {
            Some(item) => Some(item),
            None => match &self.enclosing {
                Some(env) => env.lookup(id),
                None => None,
            },
        }
    }

    pub(crate) fn extend(&mut self, id: Identifier, item: Item) {
        self.items.insert(id, item);
    }
}

#[derive(PartialEq, Eq)]
pub struct EvalEnv {
    vars: HashMap<Identifier, Rc<Expr>>,
    enclosing: Option<Rc<RefCell<EvalEnv>>>,
}

impl EvalEnv {
    pub(crate) fn debug_helper(&self) -> Vec<String> {
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

impl fmt::Debug for EvalEnv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment(\n{:?}\n)", EvalEnv::debug_helper(self))
    }
}

impl EvalEnv {
    pub(crate) fn new(enclosing: Option<Rc<RefCell<EvalEnv>>>) -> Self {
        Self {
            vars: HashMap::new(),
            enclosing,
        }
    }

    pub(crate) fn lookup(&self, id: &Identifier) -> Option<Rc<Expr>> {
        match self.vars.get(id) {
            Some(expr) => Some(expr.clone()),
            None => match &self.enclosing {
                Some(env) => env.borrow_mut().lookup(id),
                None => None,
            },
        }
    }

    pub(crate) fn extend(&mut self, id: &Identifier, expr: Rc<Expr>) {
        self.vars.insert(id.clone(), expr);
    }

    pub(crate) fn replace(&mut self, id: &Identifier, expr: Rc<Expr>) {
        match self.vars.get_mut(id) {
            Some(e) => *e = expr,
            None => match &self.enclosing {
                Some(env) => env.borrow_mut().replace(id, expr),
                None => panic!("variable not found"),
            },
        }
    }
}
