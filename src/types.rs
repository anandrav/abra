use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Unit,
    Int,
    Bool,
    String,
    Arrow(Rc<Type>, Rc<Type>),
}
