use std::{cell::RefCell, rc::Rc};

pub fn shared<T>(value: T) -> Shared<T> {
    Rc::new(RefCell::new(value))
}

pub type Shared<T> = Rc<RefCell<T>>;
