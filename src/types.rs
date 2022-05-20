use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum Type {
    Unit,
    Int,
    Bool,
    String,
    Arrow(Rc<Type>, Rc<Type>),
}
