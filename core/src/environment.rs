use crate::eval_tree::*;
use std::cell::RefCell;
use std::cmp::Eq;
use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;
use std::hash::Hash;
use std::rc::Rc;

#[derive(Clone)]
pub(crate) struct Environment<Identifier: Hash + Eq, Item> {
    base: Rc<RefCell<EnvironmentBase<Identifier, Item>>>,
}

impl<Identifier: Eq + Hash, Item: Clone> Environment<Identifier, Item> {
    pub(crate) fn empty() -> Self {
        Self {
            base: Rc::new(RefCell::new(EnvironmentBase {
                items: HashMap::new(),
                enclosing: None,
            })),
        }
    }

    pub(crate) fn new_scope(&self) -> Self {
        Self {
            base: Rc::new(RefCell::new(EnvironmentBase {
                items: HashMap::new(),
                enclosing: Some(self.base.clone()),
            })),
        }
    }

    pub(crate) fn lookup(&self, id: &Identifier) -> Option<Item> {
        self.base.borrow().lookup(id)
    }

    pub(crate) fn extend(&self, id: Identifier, item: Item) {
        self.base.borrow_mut().extend(id, item);
    }
}

impl<Identifier: Eq + Hash + Display, Item: Display> Display for Environment<Identifier, Item> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.base.borrow())
    }
}

struct EnvironmentBase<Identifier: Eq + Hash, Item> {
    items: HashMap<Identifier, Item>,
    enclosing: Option<Rc<RefCell<EnvironmentBase<Identifier, Item>>>>,
}

impl<Identifier: Eq + Hash, Item: Clone> EnvironmentBase<Identifier, Item> {
    fn lookup(&self, id: &Identifier) -> Option<Item> {
        match self.items.get(id) {
            Some(item) => Some(item.clone()),
            None => match &self.enclosing {
                Some(env) => {
                    let env = env.borrow();
                    env.lookup(id)
                }
                None => None,
            },
        }
    }

    fn extend(&mut self, id: Identifier, item: Item) {
        self.items.insert(id, item);
    }
}

impl<Identifier: Eq + Hash + Display, Item: Display> Display for EnvironmentBase<Identifier, Item> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Environment {{")?;
        self.display_helper(f)?;
        writeln!(f, "}}")
    }
}

impl<Identifier: Eq + Hash + Display, Item: Display> EnvironmentBase<Identifier, Item> {
    fn display_helper(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (key, value) in &self.items {
            writeln!(f, "{}: {}", key, value)?;
        }
        match &self.enclosing {
            Some(env) => env.borrow().display_helper(f),
            None => fmt::Result::Ok(()),
        }
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
