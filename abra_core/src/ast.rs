/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

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
    pub nominal_path: PathBuf,
    pub full_path: PathBuf,
    pub source: String,
    /// The starting byte indices in the source code.
    line_starts: Vec<usize>,
}

pub fn line_starts(source: &str) -> impl '_ + Iterator<Item = usize> {
    std::iter::once(0).chain(source.match_indices('\n').map(|(i, _)| i + 1))
}

impl FileData {
    pub fn new(nominal_path: PathBuf, full_path: PathBuf, source: String) -> FileData {
        FileData {
            nominal_path,
            full_path,
            line_starts: line_starts(source.as_ref()).collect(),
            source,
        }
    }

    pub fn name(&self) -> &str {
        self.full_path.file_name().unwrap().to_str().unwrap()
    }

    /// Return the starting byte index of the line with the specified line index.
    /// Convenience method that already generates codespan_reporting::files::Errors if necessary.
    fn line_start(&self, line_index: usize) -> Result<usize, codespan_reporting::files::Error> {
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
    fn line_index(&self, byte_index: usize) -> Result<usize, codespan_reporting::files::Error> {
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
    pub(crate) name: String,
    pub(crate) path: PathBuf,

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
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub(crate) struct StructDef {
    pub(crate) name: Rc<Identifier>,
    pub(crate) ty_args: Vec<Rc<Polytype>>,
    pub(crate) fields: Vec<Rc<StructField>>,

    pub(crate) id: NodeId,
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
    // FileAst(Rc<FileAst>),
    Item(Rc<Item>),
    Stmt(Rc<Stmt>),
    Expr(Rc<Expr>),
    Pat(Rc<Pat>),
    Type(Rc<Type>),
    Identifier(Rc<Identifier>),
    Variant(Rc<Variant>),
    // FuncDecl(Rc<FuncDecl>),
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
            // AstNode::FuncDecl(decl) => &decl.loc,
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
            // AstNode::FuncDecl(decl) => decl.id,
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
    TypeDef(Rc<TypeDefKind>), // TODO: doesn't need to be an Rc<TypeDefKind>. Just use TypeDefKind
    InterfaceDef(Rc<InterfaceDef>),
    InterfaceImpl(Rc<InterfaceImpl>),
    Extension(Rc<Extension>),
    Import(Rc<Identifier>, Option<ImportList>),
    Stmt(Rc<Stmt>),
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum ImportList {
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
    Set(Rc<Expr>, Rc<Expr>),
    Expr(Rc<Expr>),
    Continue,
    Break,
    Return(Rc<Expr>),
    If(Rc<Expr>, Vec<Rc<Stmt>>),
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
    Void,
    Int(AbraInt),
    Float(String), // Float is represented as String to allow Eq and Hash
    Bool(bool),
    Str(String),
    Array(Vec<Rc<Expr>>),
    AnonymousFunction(Vec<ArgMaybeAnnotated>, Option<Rc<Type>>, Rc<Expr>),
    IfElse(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Match(Rc<Expr>, Vec<Rc<MatchArm>>),
    Block(Vec<Rc<Stmt>>),
    BinOp(Rc<Expr>, BinaryOperator, Rc<Expr>),
    FuncAp(Rc<Expr>, Vec<Rc<Expr>>),
    MemberFuncAp(Option<Rc<Expr>>, Rc<Identifier>, Vec<Rc<Expr>>),
    Tuple(Vec<Rc<Expr>>),
    MemberAccess(Rc<Expr>, Rc<Identifier>),
    MemberAccessLeadingDot(Rc<Identifier>),
    IndexAccess(Rc<Expr>, Rc<Expr>),
    Unwrap(Rc<Expr>),
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Copy)]
pub enum BinaryOperator {
    // comparison
    Equal,
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

impl BinaryOperator {
    pub(crate) fn precedence(&self) -> u8 {
        match self {
            BinaryOperator::Equal => 1,
            BinaryOperator::Format => 2,
            BinaryOperator::And | BinaryOperator::Or => 4,
            BinaryOperator::LessThan
            | BinaryOperator::LessThanOrEqual
            | BinaryOperator::GreaterThan
            | BinaryOperator::GreaterThanOrEqual => 5,
            BinaryOperator::Add | BinaryOperator::Subtract => 6,
            BinaryOperator::Multiply | BinaryOperator::Divide => 7,
            BinaryOperator::Mod => 8,
            BinaryOperator::Pow => 9,
        }
    }
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
}
