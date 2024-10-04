use std::collections::HashMap;

use crate::ast::NodeId;

#[derive(Clone, Debug)]
pub struct Namespace {
    content: HashMap<String, NamespaceOrDeclaration>,
}

#[derive(Clone, Debug)]
pub enum NamespaceOrDeclaration {
    Namespace(Namespace),
    Declaration(NodeId),
}
