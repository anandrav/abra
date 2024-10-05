use std::collections::HashMap;

use crate::ast::NodeId;

#[derive(Clone, Debug)]
pub struct _Namespace {
    content: HashMap<String, _NamespaceOrDeclaration>,
}

#[derive(Clone, Debug)]
pub enum _NamespaceOrDeclaration {
    Namespace(_Namespace),
    Declaration(NodeId),
}
