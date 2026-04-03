/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::parse::PrefixOp;
use crate::vm::AbraInt;
use std::fmt::Display;
use std::hash::Hasher;
use std::ops::Range;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::atomic::{AtomicU32, Ordering};

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct Identifier {
    pub(crate) v: String,

    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl std::hash::Hash for Identifier {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Identifier {
    pub fn node(self: &Rc<Identifier>) -> AstNode {
        AstNode::Identifier(self.clone())
    }
}

#[derive(Debug, Clone)]
pub struct FileData {
    pub package_name: PathBuf,
    pub absolute_path: PathBuf,
    pub source: String,
    /// The starting byte indices in the source code.
    line_starts: Vec<usize>,
}

pub fn line_starts(source: &str) -> impl '_ + Iterator<Item = usize> {
    std::iter::once(0).chain(source.match_indices('\n').map(|(i, _)| i + 1))
}

impl FileData {
    pub fn new(package_name: PathBuf, absolute_path: PathBuf, source: String) -> FileData {
        FileData {
            package_name,
            absolute_path,
            line_starts: line_starts(source.as_ref()).collect(),
            source,
        }
    }

    pub fn new_simple(path: PathBuf, source: String) -> FileData {
        let absolute_path = path.clone();
        let mut package_name = path;
        package_name.set_extension("");
        FileData {
            package_name,
            absolute_path,
            line_starts: line_starts(source.as_ref()).collect(),
            source,
        }
    }

    pub fn name(&self) -> &str {
        self.absolute_path.file_name().unwrap().to_str().unwrap()
    }

    /// Return the starting byte index of the line with the specified line index.
    /// Convenience method that already generates codespan_reporting::files::Errors if necessary.
    pub fn line_start(&self, line_index: usize) -> Result<usize, codespan_reporting::files::Error> {
        use std::cmp::Ordering;

        match line_index.cmp(&self.line_starts.len()) {
            Ordering::Less => Ok(self
                .line_starts
                .get(line_index)
                .cloned()
                .expect("failed despite previous check")),
            Ordering::Equal => Ok(self.source.len()),
            Ordering::Greater => Err(codespan_reporting::files::Error::LineTooLarge {
                given: line_index,
                max: self.line_starts.len() - 1,
            }),
        }
    }

    /// returns the 1-indexed line number in which the target index lies.
    pub fn line_number_for_index(&self, index: usize) -> usize {
        match self.line_starts.binary_search(&index) {
            Ok(line) => line + 1, // found the line
            Err(line) => line,    // it must be the previous index
        }
    }
}

impl FileData {
    pub fn line_index(&self, byte_index: usize) -> Result<usize, codespan_reporting::files::Error> {
        Ok(self
            .line_starts
            .binary_search(&byte_index)
            .unwrap_or_else(|next_line| next_line - 1))
    }

    fn line_range(
        &self,
        line_index: usize,
    ) -> Result<Range<usize>, codespan_reporting::files::Error> {
        let line_start = self.line_start(line_index)?;
        let next_line_start = self.line_start(line_index + 1)?;

        Ok(line_start..next_line_start)
    }
}

#[derive(Debug, Clone, Default)]
pub struct FileDatabase {
    pub files: Vec<FileData>,
}

impl FileDatabase {
    /// Create a new files database.
    pub fn new() -> FileDatabase {
        FileDatabase { files: Vec::new() }
    }

    /// Add a file to the database, returning the handle that can be used to
    /// refer to it again.
    pub fn add(&mut self, file_data: FileData) -> FileId {
        let file_id = self.files.len() as FileId;
        self.files.push(file_data);
        file_id
    }

    /// Get the file corresponding to the given id.
    pub fn get(&self, file_id: FileId) -> Result<&FileData, codespan_reporting::files::Error> {
        self.files
            .get(file_id as usize)
            .ok_or(codespan_reporting::files::Error::FileMissing)
    }
}

pub type FileId = u32;

impl<'a> codespan_reporting::files::Files<'a> for FileDatabase {
    type FileId = FileId;
    type Name = &'a str;
    type Source = &'a str;

    fn name(&'a self, file_id: FileId) -> Result<Self::Name, codespan_reporting::files::Error> {
        Ok(self.get(file_id)?.name())
    }

    fn source(&'a self, file_id: FileId) -> Result<&'a str, codespan_reporting::files::Error> {
        Ok(&self.get(file_id)?.source)
    }

    fn line_index(
        &'a self,
        file_id: FileId,
        byte_index: usize,
    ) -> Result<usize, codespan_reporting::files::Error> {
        self.get(file_id)?.line_index(byte_index)
    }

    fn line_range(
        &'a self,
        file_id: FileId,
        line_index: usize,
    ) -> Result<Range<usize>, codespan_reporting::files::Error> {
        self.get(file_id)?.line_range(line_index)
    }
}

pub(crate) type PatAnnotated = (Rc<Pat>, Option<Rc<Type>>);

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct FileAst {
    pub(crate) items: Vec<Rc<Item>>,
    /// name of the Abra package this file represents
    pub(crate) package_name: PathBuf,
    /// package name as a String
    pub(crate) package_name_str: String,
    /// absolute path of the file this AST was parsed from
    pub(crate) absolute_path: PathBuf,

    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl std::hash::Hash for FileAst {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum TypeDefKind {
    // Alias(Rc<Identifier>, Rc<AstType>),
    Enum(Rc<EnumDef>),
    Struct(Rc<StructDef>),
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct EnumDef {
    pub(crate) name: Rc<Identifier>,
    pub(crate) ty_args: Vec<Rc<Polytype>>,
    pub(crate) variants: Vec<Rc<Variant>>,
    pub(crate) id: NodeId,

    pub(crate) attributes: Vec<Attribute>,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct StructDef {
    pub(crate) name: Rc<Identifier>,
    pub(crate) ty_args: Vec<Rc<Polytype>>,
    pub(crate) fields: Vec<Rc<StructField>>,
    pub(crate) id: NodeId,

    pub(crate) attributes: Vec<Attribute>,
}

impl std::hash::Hash for StructDef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct Variant {
    pub(crate) ctor: Rc<Identifier>,
    pub(crate) data: Option<Rc<Type>>,

    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl std::hash::Hash for Variant {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Variant {
    pub fn node(self: &Rc<Variant>) -> AstNode {
        AstNode::Variant(self.clone())
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct StructField {
    pub(crate) name: Rc<Identifier>,
    pub(crate) ty: Rc<Type>,

    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl std::hash::Hash for StructField {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) enum AstNode {
    Item(Rc<Item>),
    Stmt(Rc<Stmt>),
    Expr(Rc<Expr>),
    Pat(Rc<Pat>),
    Type(Rc<Type>),
    Identifier(Rc<Identifier>),
    Variant(Rc<Variant>),
    MatchArm(Rc<MatchArm>),
}

impl std::hash::Hash for AstNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

impl AstNode {
    pub fn location(&self) -> &Location {
        match self {
            AstNode::Item(item) => &item.loc,
            AstNode::Stmt(stmt) => &stmt.loc,
            AstNode::Expr(expr) => &expr.loc,
            AstNode::Pat(pat) => &pat.loc,
            AstNode::Type(typ) => &typ.loc,
            AstNode::Identifier(identifier) => &identifier.loc,
            AstNode::Variant(variant) => &variant.loc,
            AstNode::MatchArm(match_arm) => &match_arm.loc,
        }
    }

    pub fn id(&self) -> NodeId {
        match self {
            AstNode::Item(item) => item.id,
            AstNode::Stmt(stmt) => stmt.id,
            AstNode::Expr(expr) => expr.id,
            AstNode::Pat(pat) => pat.id,
            AstNode::Type(typ) => typ.id,
            AstNode::Identifier(identifier) => identifier.id,
            AstNode::Variant(variant) => variant.id,
            AstNode::MatchArm(match_arm) => match_arm.id,
        }
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]

pub(crate) struct Item {
    pub(crate) kind: Rc<ItemKind>,
    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl std::hash::Hash for Item {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Item {
    pub fn node(self: &Rc<Item>) -> AstNode {
        AstNode::Item(self.clone())
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum ItemKind {
    FuncDecl(Rc<FuncDecl>),
    FuncDef(Rc<FuncDef>),
    TypeDef(TypeDefKind),
    InterfaceDef(Rc<InterfaceDef>),
    InterfaceImpl(Rc<InterfaceImpl>),
    Extension(Rc<Extension>),
    Import(Rc<Identifier>, ImportKind),
    Stmt(Rc<Stmt>),
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum ImportKind {
    Glob,
    As(Rc<Identifier>),
    Inclusion(Vec<Rc<Identifier>>),
    Exclusion(Vec<Rc<Identifier>>),
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct Stmt {
    pub(crate) kind: Rc<StmtKind>,
    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl std::hash::Hash for Stmt {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Stmt {
    pub fn node(self: &Rc<Stmt>) -> AstNode {
        AstNode::Stmt(self.clone())
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum StmtKind {
    Let(bool, PatAnnotated, Rc<Expr>), // bool is whether it's mutable
    Assign(Rc<Expr>, AssignOperator, Rc<Expr>),
    Expr(Rc<Expr>),
    Continue,
    Break,
    Return(Rc<Expr>),
    WhileLoop(Rc<Expr>, Vec<Rc<Stmt>>),
    ForLoop(Rc<Pat>, Rc<Expr>, Vec<Rc<Stmt>>),
}

pub(crate) type ArgMaybeAnnotated = (Rc<Identifier>, Option<Rc<Type>>);

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct FuncDef {
    pub(crate) name: Rc<Identifier>,
    pub(crate) args: Vec<ArgMaybeAnnotated>,
    pub(crate) ret_type: Option<Rc<Type>>,
    pub(crate) body: Rc<Expr>,

    pub(crate) attributes: Vec<Attribute>,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct FuncDecl {
    pub(crate) name: Rc<Identifier>,
    pub(crate) args: Vec<ArgMaybeAnnotated>,
    pub(crate) ret_type: Rc<Type>,

    pub(crate) attributes: Vec<Attribute>,
}

impl FuncDecl {
    pub(crate) fn is_foreign(&self) -> bool {
        self.attributes.iter().any(Attribute::is_foreign)
    }

    pub(crate) fn is_host(&self) -> bool {
        self.attributes.iter().any(Attribute::is_host)
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct Attribute {
    pub(crate) name: Rc<Identifier>,
    pub(crate) _args: Vec<Rc<Identifier>>, // unused right now
}

impl Attribute {
    pub(crate) fn is_foreign(&self) -> bool {
        self.name.v == "foreign"
    }

    pub(crate) fn is_host(&self) -> bool {
        self.name.v == "host"
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct InterfaceDef {
    pub(crate) name: Rc<Identifier>,
    pub(crate) methods: Vec<Rc<FuncDecl>>,
    pub(crate) output_types: Vec<Rc<InterfaceOutputType>>,

    pub(crate) attributes: Vec<Attribute>,
}

impl InterfaceDef {
    pub fn get_method_by_name(&self, name: &str) -> Option<(usize, &Rc<FuncDecl>)> {
        self.methods
            .iter()
            .enumerate()
            .find(|(_i, method)| method.name.v == name)
    }

    pub fn get_output_type_by_name(&self, name: &str) -> Option<Rc<InterfaceOutputType>> {
        self.output_types
            .iter()
            .find(|ot| ot.name.v == name)
            .cloned()
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct InterfaceOutputType {
    pub(crate) name: Rc<Identifier>,
    pub(crate) interfaces: Vec<Rc<Interface>>,

    pub(crate) id: NodeId,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct InterfaceImpl {
    pub(crate) iface: Rc<Identifier>,
    pub(crate) typ: Rc<Type>,
    pub(crate) methods: Vec<Rc<FuncDef>>,

    pub(crate) id: NodeId,
}

impl InterfaceImpl {
    pub fn get_method_by_name(&self, name: &str) -> Option<Rc<FuncDef>> {
        self.methods
            .iter()
            .find(|method| method.name.v == name)
            .cloned()
    }
}

impl std::hash::Hash for InterfaceImpl {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct Extension {
    pub(crate) typ: Rc<Type>,
    pub(crate) methods: Vec<Rc<FuncDef>>,

    pub(crate) id: NodeId,
}

impl std::hash::Hash for Extension {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct Expr {
    pub(crate) kind: Rc<ExprKind>,
    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl std::hash::Hash for Expr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Expr {
    pub fn node(self: &Rc<Expr>) -> AstNode {
        AstNode::Expr(self.clone())
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum ExprKind {
    Variable(String),
    Nil,
    Int(AbraInt),
    Float(String), // Float is represented as String to allow Eq and Hash
    Bool(bool),
    Str(String),
    Array(Vec<Rc<Expr>>),
    AnonymousFunction(Vec<ArgMaybeAnnotated>, Option<Rc<Type>>, Rc<Expr>),
    IfElse(Rc<Expr>, Rc<Stmt>, Option<Rc<Stmt>>),
    Match(Rc<Expr>, Vec<Rc<MatchArm>>),
    Block(Vec<Rc<Stmt>>),
    BinOp(Rc<Expr>, BinaryOperator, Rc<Expr>),
    Unop(PrefixOp, Rc<Expr>),
    FuncAp(Rc<Expr>, Vec<Rc<Expr>>),
    Tuple(Vec<Rc<Expr>>),
    MemberAccess(Rc<Expr>, Rc<Identifier>),
    MemberAccessLeadingDot(Rc<Identifier>),
    IndexAccess(Rc<Expr>, Rc<Expr>),
    Unwrap(Rc<Expr>),
    Try(Rc<Expr>),
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Copy)]
pub enum BinaryOperator {
    // comparison
    Equal,
    NotEqual,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    // numeric
    Add,
    Subtract,
    Multiply,
    Divide,
    Mod,
    Pow,
    // boolean
    And,
    Or,
    // string
    Format,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Copy)]
pub enum AssignOperator {
    Equal,
    // numeric
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
    ModEq,
    // Pow,
    // // boolean
    // And,
    // Or,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct MatchArm {
    pub(crate) pat: Rc<Pat>,
    pub(crate) stmt: Rc<Stmt>,

    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl std::hash::Hash for MatchArm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl MatchArm {
    pub fn node(self: &Rc<MatchArm>) -> AstNode {
        AstNode::MatchArm(self.clone())
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct Pat {
    pub(crate) kind: Rc<PatKind>,
    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl std::hash::Hash for Pat {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Pat {
    pub fn node(self: &Rc<Pat>) -> AstNode {
        AstNode::Pat(self.clone())
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum PatKind {
    Wildcard,
    Binding(String),
    Variant(Vec<Rc<Identifier>>, Rc<Identifier>, Option<Rc<Pat>>),
    Void,
    Int(AbraInt),
    Float(String),
    Bool(bool),
    Str(String),
    Tuple(Vec<Rc<Pat>>),
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct Type {
    pub(crate) kind: Rc<TypeKind>,
    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl std::hash::Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Type {
    pub fn node(self: &Rc<Type>) -> AstNode {
        AstNode::Type(self.clone())
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum TypeKind {
    Poly(Rc<Polytype>),
    NamedWithParams(Rc<Identifier>, Vec<Rc<Type>>),
    Void,
    Int,
    Float,
    Bool,
    Str,
    Function(Vec<Rc<Type>>, Rc<Type>),
    Tuple(Vec<Rc<Type>>),
    Wildcard,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct Polytype {
    pub(crate) name: Rc<Identifier>,
    pub(crate) interfaces: Vec<Rc<Interface>>,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct Interface {
    pub(crate) name: Rc<Identifier>,
    pub(crate) arguments: Vec<(Rc<Identifier>, Rc<Type>)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct NodeId {
    pub(crate) id: u32,
}

impl NodeId {
    pub(crate) fn new() -> Self {
        static ID_COUNTER: std::sync::atomic::AtomicU32 = AtomicU32::new(1);
        let id = ID_COUNTER.fetch_add(1, Ordering::Relaxed);
        Self { id }
    }
}

impl Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Id[{}]", self.id)
    }
}

impl Default for NodeId {
    fn default() -> Self {
        NodeId::new()
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct Location {
    pub(crate) file_id: FileId,
    pub(crate) lo: usize,
    pub(crate) hi: usize,
}

impl Location {
    pub fn range(&self) -> Range<usize> {
        self.lo..self.hi
    }

    fn contains_offset(&self, offset: usize) -> bool {
        self.lo <= offset && offset < self.hi
    }
}

// --- LSP utilities: find AST nodes at a given byte offset ---

/// Find the innermost AST node at the given byte offset within a file.
pub(crate) fn find_innermost_node_at_offset(file_ast: &FileAst, offset: usize) -> Option<AstNode> {
    for item in &file_ast.items {
        if !item.loc.contains_offset(offset) {
            continue;
        }
        if let Some(node) = find_in_item(item, offset) {
            return Some(node);
        }
        return Some(item.node());
    }
    None
}

/// Find the identifier at the given byte offset (for go-to-definition).
pub(crate) fn find_identifier_at_offset(file_ast: &FileAst, offset: usize) -> Option<AstNode> {
    for item in &file_ast.items {
        if !item.loc.contains_offset(offset) {
            continue;
        }
        if let Some(node) = find_ident_in_item(item, offset) {
            return Some(node);
        }
    }
    None
}

fn find_in_func_def_body(func_def: &Rc<FuncDef>, offset: usize) -> Option<AstNode> {
    if func_def.name.loc.contains_offset(offset) {
        return Some(func_def.name.node());
    }
    for (arg_name, _) in &func_def.args {
        if arg_name.loc.contains_offset(offset) {
            return Some(arg_name.node());
        }
    }
    find_in_expr(&func_def.body, offset)
}

fn find_in_item(item: &Rc<Item>, offset: usize) -> Option<AstNode> {
    match &*item.kind {
        ItemKind::FuncDef(func_def) => find_in_func_def_body(func_def, offset),
        ItemKind::Stmt(stmt) => find_in_stmt(stmt, offset),
        ItemKind::InterfaceImpl(iface_impl) => {
            for method in &iface_impl.methods {
                if let Some(node) = find_in_func_def_body(method, offset) {
                    return Some(node);
                }
            }
            None
        }
        ItemKind::Extension(ext) => {
            for method in &ext.methods {
                if let Some(node) = find_in_func_def_body(method, offset) {
                    return Some(node);
                }
            }
            None
        }
        _ => None,
    }
}

fn find_in_stmt(stmt: &Rc<Stmt>, offset: usize) -> Option<AstNode> {
    if !stmt.loc.contains_offset(offset) {
        return None;
    }
    match &*stmt.kind {
        StmtKind::Let(_, (pat, _), expr) => {
            if let Some(node) = find_in_expr(expr, offset) {
                return Some(node);
            }
            if pat.loc.contains_offset(offset) {
                return Some(pat.node());
            }
            None
        }
        StmtKind::Assign(lhs, _, rhs) => {
            find_in_expr(lhs, offset).or_else(|| find_in_expr(rhs, offset))
        }
        StmtKind::Expr(expr) => find_in_expr(expr, offset),
        StmtKind::Return(expr) => find_in_expr(expr, offset),
        StmtKind::WhileLoop(cond, body) => {
            if let Some(node) = find_in_expr(cond, offset) {
                return Some(node);
            }
            for s in body {
                if let Some(node) = find_in_stmt(s, offset) {
                    return Some(node);
                }
            }
            None
        }
        StmtKind::ForLoop(pat, iter, body) => {
            if pat.loc.contains_offset(offset) {
                return Some(pat.node());
            }
            if let Some(node) = find_in_expr(iter, offset) {
                return Some(node);
            }
            for s in body {
                if let Some(node) = find_in_stmt(s, offset) {
                    return Some(node);
                }
            }
            None
        }
        StmtKind::Continue | StmtKind::Break => None,
    }
}

fn find_in_expr(expr: &Rc<Expr>, offset: usize) -> Option<AstNode> {
    if !expr.loc.contains_offset(offset) {
        return None;
    }
    match &*expr.kind {
        ExprKind::Variable(_) => Some(expr.node()),
        ExprKind::BinOp(lhs, _, rhs) => find_in_expr(lhs, offset)
            .or_else(|| find_in_expr(rhs, offset))
            .or(Some(expr.node())),
        ExprKind::Unop(_, operand) => find_in_expr(operand, offset).or(Some(expr.node())),
        ExprKind::FuncAp(func, args) => {
            if let Some(node) = find_in_expr(func, offset) {
                return Some(node);
            }
            for arg in args {
                if let Some(node) = find_in_expr(arg, offset) {
                    return Some(node);
                }
            }
            Some(expr.node())
        }
        ExprKind::MemberAccess(receiver, member) => {
            if member.loc.contains_offset(offset) {
                return Some(expr.node());
            }
            find_in_expr(receiver, offset).or(Some(expr.node()))
        }
        ExprKind::MemberAccessLeadingDot(_) => Some(expr.node()),
        ExprKind::IndexAccess(arr, idx) => find_in_expr(arr, offset)
            .or_else(|| find_in_expr(idx, offset))
            .or(Some(expr.node())),
        ExprKind::Block(stmts) => {
            for s in stmts {
                if let Some(node) = find_in_stmt(s, offset) {
                    return Some(node);
                }
            }
            Some(expr.node())
        }
        ExprKind::IfElse(cond, then_branch, else_branch) => {
            if let Some(node) = find_in_expr(cond, offset) {
                return Some(node);
            }
            if let Some(node) = find_in_stmt(then_branch, offset) {
                return Some(node);
            }
            if let Some(else_b) = else_branch
                && let Some(node) = find_in_stmt(else_b, offset)
            {
                return Some(node);
            }
            Some(expr.node())
        }
        ExprKind::Match(scrutinee, arms) => {
            if let Some(node) = find_in_expr(scrutinee, offset) {
                return Some(node);
            }
            for arm in arms {
                if arm.loc.contains_offset(offset) {
                    if let Some(node) = find_in_stmt(&arm.stmt, offset) {
                        return Some(node);
                    }
                    return Some(arm.node());
                }
            }
            Some(expr.node())
        }
        ExprKind::AnonymousFunction(args, _, body) => {
            for (arg_name, _) in args {
                if arg_name.loc.contains_offset(offset) {
                    return Some(arg_name.node());
                }
            }
            find_in_expr(body, offset).or(Some(expr.node()))
        }
        ExprKind::Array(elems) => {
            for elem in elems {
                if let Some(node) = find_in_expr(elem, offset) {
                    return Some(node);
                }
            }
            Some(expr.node())
        }
        ExprKind::Tuple(elems) => {
            for elem in elems {
                if let Some(node) = find_in_expr(elem, offset) {
                    return Some(node);
                }
            }
            Some(expr.node())
        }
        ExprKind::Unwrap(inner) | ExprKind::Try(inner) => {
            find_in_expr(inner, offset).or(Some(expr.node()))
        }
        ExprKind::Nil
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Str(_) => Some(expr.node()),
    }
}

// For go-to-definition: find the identifier (Variable or MemberAccess) at offset
fn find_ident_in_item(item: &Rc<Item>, offset: usize) -> Option<AstNode> {
    if !item.loc.contains_offset(offset) {
        return None;
    }
    match &*item.kind {
        ItemKind::FuncDef(func_def) => {
            if let Some(node) =
                find_ident_in_func_signature(&func_def.args, func_def.ret_type.as_ref(), offset)
            {
                return Some(node);
            }
            find_ident_in_expr(&func_def.body, offset)
        }
        ItemKind::FuncDecl(func_decl) => {
            find_ident_in_func_signature(&func_decl.args, Some(&func_decl.ret_type), offset)
        }
        ItemKind::Stmt(stmt) => find_ident_in_stmt(stmt, offset),
        ItemKind::InterfaceImpl(iface_impl) => {
            if iface_impl.iface.loc.contains_offset(offset) {
                return Some(iface_impl.iface.node());
            }
            if let Some(node) = find_ident_in_type(&iface_impl.typ, offset) {
                return Some(node);
            }
            for method in &iface_impl.methods {
                if let Some(node) =
                    find_ident_in_func_signature(&method.args, method.ret_type.as_ref(), offset)
                {
                    return Some(node);
                }
                if let Some(node) = find_ident_in_expr(&method.body, offset) {
                    return Some(node);
                }
            }
            None
        }
        ItemKind::Extension(ext) => {
            if let Some(node) = find_ident_in_type(&ext.typ, offset) {
                return Some(node);
            }
            for method in &ext.methods {
                if let Some(node) =
                    find_ident_in_func_signature(&method.args, method.ret_type.as_ref(), offset)
                {
                    return Some(node);
                }
                if let Some(node) = find_ident_in_expr(&method.body, offset) {
                    return Some(node);
                }
            }
            None
        }
        ItemKind::Import(ident, _) => {
            if ident.loc.contains_offset(offset) {
                return Some(ident.node());
            }
            None
        }
        _ => None,
    }
}

fn find_ident_in_func_signature(
    args: &[ArgMaybeAnnotated],
    ret_type: Option<&Rc<Type>>,
    offset: usize,
) -> Option<AstNode> {
    for (arg_name, arg_type) in args {
        if arg_name.loc.contains_offset(offset) {
            return Some(arg_name.node());
        }
        if let Some(ty) = arg_type
            && let Some(node) = find_ident_in_type(ty, offset)
        {
            return Some(node);
        }
    }
    if let Some(ret) = ret_type
        && let Some(node) = find_ident_in_type(ret, offset)
    {
        return Some(node);
    }
    None
}

fn find_ident_in_type(typ: &Rc<Type>, offset: usize) -> Option<AstNode> {
    if !typ.loc.contains_offset(offset) {
        return None;
    }
    match &*typ.kind {
        TypeKind::NamedWithParams(ident, args) => {
            if ident.loc.contains_offset(offset) {
                return Some(ident.node());
            }
            for arg in args {
                if let Some(node) = find_ident_in_type(arg, offset) {
                    return Some(node);
                }
            }
            None
        }
        TypeKind::Poly(poly) => {
            if poly.name.loc.contains_offset(offset) {
                return Some(poly.name.node());
            }
            None
        }
        TypeKind::Function(args, ret) => {
            for arg in args {
                if let Some(node) = find_ident_in_type(arg, offset) {
                    return Some(node);
                }
            }
            find_ident_in_type(ret, offset)
        }
        TypeKind::Tuple(elems) => {
            for elem in elems {
                if let Some(node) = find_ident_in_type(elem, offset) {
                    return Some(node);
                }
            }
            None
        }
        _ => None,
    }
}

fn find_ident_in_stmt(stmt: &Rc<Stmt>, offset: usize) -> Option<AstNode> {
    if !stmt.loc.contains_offset(offset) {
        return None;
    }
    match &*stmt.kind {
        StmtKind::Let(_, (_, type_annot), expr) => {
            if let Some(ty) = type_annot
                && let Some(node) = find_ident_in_type(ty, offset)
            {
                return Some(node);
            }
            find_ident_in_expr(expr, offset)
        }
        StmtKind::Assign(lhs, _, rhs) => {
            find_ident_in_expr(lhs, offset).or_else(|| find_ident_in_expr(rhs, offset))
        }
        StmtKind::Expr(expr) => find_ident_in_expr(expr, offset),
        StmtKind::Return(expr) => find_ident_in_expr(expr, offset),
        StmtKind::WhileLoop(cond, body) => {
            if let Some(node) = find_ident_in_expr(cond, offset) {
                return Some(node);
            }
            for s in body {
                if let Some(node) = find_ident_in_stmt(s, offset) {
                    return Some(node);
                }
            }
            None
        }
        StmtKind::ForLoop(_, iter, body) => {
            if let Some(node) = find_ident_in_expr(iter, offset) {
                return Some(node);
            }
            for s in body {
                if let Some(node) = find_ident_in_stmt(s, offset) {
                    return Some(node);
                }
            }
            None
        }
        StmtKind::Continue | StmtKind::Break => None,
    }
}

fn find_ident_in_expr(expr: &Rc<Expr>, offset: usize) -> Option<AstNode> {
    if !expr.loc.contains_offset(offset) {
        return None;
    }
    match &*expr.kind {
        ExprKind::Variable(_) => Some(expr.node()),
        ExprKind::BinOp(lhs, _, rhs) => {
            find_ident_in_expr(lhs, offset).or_else(|| find_ident_in_expr(rhs, offset))
        }
        ExprKind::Unop(_, operand) => find_ident_in_expr(operand, offset),
        ExprKind::FuncAp(func, args) => {
            if let Some(node) = find_ident_in_expr(func, offset) {
                return Some(node);
            }
            for arg in args {
                if let Some(node) = find_ident_in_expr(arg, offset) {
                    return Some(node);
                }
            }
            None
        }
        ExprKind::MemberAccess(receiver, member) => {
            if member.loc.contains_offset(offset) {
                return Some(member.node());
            }
            find_ident_in_expr(receiver, offset)
        }
        ExprKind::MemberAccessLeadingDot(_) => Some(expr.node()),
        ExprKind::IndexAccess(arr, idx) => {
            find_ident_in_expr(arr, offset).or_else(|| find_ident_in_expr(idx, offset))
        }
        ExprKind::Block(stmts) => {
            for s in stmts {
                if let Some(node) = find_ident_in_stmt(s, offset) {
                    return Some(node);
                }
            }
            None
        }
        ExprKind::IfElse(cond, then_branch, else_branch) => {
            if let Some(node) = find_ident_in_expr(cond, offset) {
                return Some(node);
            }
            if let Some(node) = find_ident_in_stmt(then_branch, offset) {
                return Some(node);
            }
            if let Some(else_b) = else_branch {
                return find_ident_in_stmt(else_b, offset);
            }
            None
        }
        ExprKind::Match(scrutinee, arms) => {
            if let Some(node) = find_ident_in_expr(scrutinee, offset) {
                return Some(node);
            }
            for arm in arms {
                if arm.loc.contains_offset(offset) {
                    return find_ident_in_stmt(&arm.stmt, offset);
                }
            }
            None
        }
        ExprKind::AnonymousFunction(_, _, body) => find_ident_in_expr(body, offset),
        ExprKind::Array(elems) | ExprKind::Tuple(elems) => {
            for elem in elems {
                if let Some(node) = find_ident_in_expr(elem, offset) {
                    return Some(node);
                }
            }
            None
        }
        ExprKind::Unwrap(inner) | ExprKind::Try(inner) => find_ident_in_expr(inner, offset),
        ExprKind::Nil
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Str(_) => None,
    }
}

/// Find all Variable expression nodes with the given name in a file AST.
pub(crate) fn find_variables_by_name(file_ast: &FileAst, name: &str) -> Vec<AstNode> {
    let mut results = vec![];
    for item in &file_ast.items {
        collect_vars_in_item(item, name, &mut results);
    }
    results
}

fn collect_vars_in_item(item: &Rc<Item>, name: &str, out: &mut Vec<AstNode>) {
    match &*item.kind {
        ItemKind::FuncDef(func_def) => collect_vars_in_expr(&func_def.body, name, out),
        ItemKind::Stmt(stmt) => collect_vars_in_stmt(stmt, name, out),
        ItemKind::InterfaceImpl(iface_impl) => {
            for method in &iface_impl.methods {
                collect_vars_in_expr(&method.body, name, out);
            }
        }
        ItemKind::Extension(ext) => {
            for method in &ext.methods {
                collect_vars_in_expr(&method.body, name, out);
            }
        }
        _ => {}
    }
}

fn collect_vars_in_stmt(stmt: &Rc<Stmt>, name: &str, out: &mut Vec<AstNode>) {
    match &*stmt.kind {
        StmtKind::Let(_, _, expr) => collect_vars_in_expr(expr, name, out),
        StmtKind::Assign(lhs, _, rhs) => {
            collect_vars_in_expr(lhs, name, out);
            collect_vars_in_expr(rhs, name, out);
        }
        StmtKind::Expr(expr) | StmtKind::Return(expr) => collect_vars_in_expr(expr, name, out),
        StmtKind::WhileLoop(cond, body) => {
            collect_vars_in_expr(cond, name, out);
            for s in body {
                collect_vars_in_stmt(s, name, out);
            }
        }
        StmtKind::ForLoop(_, iter, body) => {
            collect_vars_in_expr(iter, name, out);
            for s in body {
                collect_vars_in_stmt(s, name, out);
            }
        }
        StmtKind::Continue | StmtKind::Break => {}
    }
}

fn collect_vars_in_expr(expr: &Rc<Expr>, name: &str, out: &mut Vec<AstNode>) {
    match &*expr.kind {
        ExprKind::Variable(v) if v == name => {
            out.push(expr.node());
        }
        ExprKind::Variable(_)
        | ExprKind::Nil
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Str(_)
        | ExprKind::MemberAccessLeadingDot(_) => {}
        ExprKind::BinOp(lhs, _, rhs) => {
            collect_vars_in_expr(lhs, name, out);
            collect_vars_in_expr(rhs, name, out);
        }
        ExprKind::Unop(_, operand) => collect_vars_in_expr(operand, name, out),
        ExprKind::FuncAp(func, args) => {
            collect_vars_in_expr(func, name, out);
            for arg in args {
                collect_vars_in_expr(arg, name, out);
            }
        }
        ExprKind::MemberAccess(receiver, _) => collect_vars_in_expr(receiver, name, out),
        ExprKind::IndexAccess(arr, idx) => {
            collect_vars_in_expr(arr, name, out);
            collect_vars_in_expr(idx, name, out);
        }
        ExprKind::Block(stmts) => {
            for s in stmts {
                collect_vars_in_stmt(s, name, out);
            }
        }
        ExprKind::IfElse(cond, then_branch, else_branch) => {
            collect_vars_in_expr(cond, name, out);
            collect_vars_in_stmt(then_branch, name, out);
            if let Some(else_b) = else_branch {
                collect_vars_in_stmt(else_b, name, out);
            }
        }
        ExprKind::Match(scrutinee, arms) => {
            collect_vars_in_expr(scrutinee, name, out);
            for arm in arms {
                collect_vars_in_stmt(&arm.stmt, name, out);
            }
        }
        ExprKind::AnonymousFunction(_, _, body) => collect_vars_in_expr(body, name, out),
        ExprKind::Array(elems) | ExprKind::Tuple(elems) => {
            for elem in elems {
                collect_vars_in_expr(elem, name, out);
            }
        }
        ExprKind::Unwrap(inner) | ExprKind::Try(inner) => collect_vars_in_expr(inner, name, out),
    }
}
