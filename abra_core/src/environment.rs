/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::cell::RefCell;
use std::cmp::Eq;
use std::fmt;
use std::fmt::Display;
use std::hash::Hash;
use std::rc::Rc;
use utils::hash::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub struct Environment<Identifier: Hash + Eq, Item: Clone> {
    base: Rc<RefCell<EnvironmentBase<Identifier, Item>>>,
}

impl<Identifier: Eq + Hash, Item: Clone> Environment<Identifier, Item> {
    pub(crate) fn empty() -> Self {
        Self {
            base: Rc::new(RefCell::new(EnvironmentBase {
                items: HashMap::default(),
                enclosing: None,
            })),
        }
    }

    pub(crate) fn new_scope(&self) -> Self {
        Self {
            base: Rc::new(RefCell::new(EnvironmentBase {
                items: HashMap::default(),
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

impl<Identifier: Eq + Hash + Display, Item: Clone + Display> Display
    for Environment<Identifier, Item>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.base.borrow())
    }
}

#[derive(Debug, PartialEq)]
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
            writeln!(f, "{key}: {value}")?;
        }
        match &self.enclosing {
            Some(env) => env.borrow().display_helper(f),
            None => fmt::Result::Ok(()),
        }
    }
}
