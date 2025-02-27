use std::collections::HashMap;
use std::fmt::Display;
use std::ops::Range;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct Identifier {
    pub(crate) v: String,

    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl Node for Identifier {
    fn location(&self) -> Location {
        self.loc.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        vec![]
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
    pub fn add(&mut self, file_data: FileData) -> usize {
        let file_id = self.files.len();
        self.files.push(file_data);
        file_id
    }

    /// Get the file corresponding to the given id.
    pub fn get(&self, file_id: usize) -> Result<&FileData, codespan_reporting::files::Error> {
        self.files
            .get(file_id)
            .ok_or(codespan_reporting::files::Error::FileMissing)
    }
}

pub type FileId = usize;

impl<'a> codespan_reporting::files::Files<'a> for FileDatabase {
    type FileId = FileId;
    type Name = &'a str;
    type Source = &'a str;

    fn name(&'a self, file_id: usize) -> Result<Self::Name, codespan_reporting::files::Error> {
        Ok(self.get(file_id)?.name())
    }

    fn source(&'a self, file_id: usize) -> Result<&'a str, codespan_reporting::files::Error> {
        Ok(&self.get(file_id)?.source)
    }

    fn line_index(
        &'a self,
        file_id: usize,
        byte_index: usize,
    ) -> Result<usize, codespan_reporting::files::Error> {
        self.get(file_id)?.line_index(byte_index)
    }

    fn line_range(
        &'a self,
        file_id: usize,
        line_index: usize,
    ) -> Result<Range<usize>, codespan_reporting::files::Error> {
        self.get(file_id)?.line_range(line_index)
    }
}

pub(crate) type PatAnnotated = (Rc<Pat>, Option<Rc<Type>>);

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct FileAst {
    pub(crate) items: Vec<Rc<Item>>,
    pub(crate) name: String,
    pub(crate) path: PathBuf,

    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl Node for FileAst {
    fn location(&self) -> Location {
        self.loc.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        self.items
            .iter()
            .map(|i| i.clone() as Rc<dyn Node>)
            .collect()
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum TypeDefKind {
    // Alias(Identifier, Rc<AstType>),
    Enum(Rc<EnumDef>),
    Struct(Rc<StructDef>),
    Foreign(Identifier),
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct EnumDef {
    pub(crate) name: Identifier,
    pub(crate) ty_args: Vec<Rc<Type>>,
    pub(crate) variants: Vec<Rc<Variant>>,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct StructDef {
    pub(crate) name: Identifier,
    pub(crate) ty_args: Vec<Rc<Type>>,
    pub(crate) fields: Vec<Rc<StructField>>,

    pub(crate) id: NodeId,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct Variant {
    pub(crate) ctor: Identifier,
    pub(crate) data: Option<Rc<Type>>,

    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl Node for Variant {
    fn location(&self) -> Location {
        self.loc.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &self.data {
            Some(ty) => vec![ty.clone()],
            None => vec![],
        }
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct StructField {
    pub(crate) name: Identifier,
    pub(crate) ty: Rc<Type>,

    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl Node for StructField {
    fn location(&self) -> Location {
        self.loc.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        vec![self.ty.clone()]
    }
}

impl std::fmt::Debug for dyn Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Node")
            .field("span", &self.location())
            .field("id", &self.id())
            .finish()
    }
}

// TODO: convert this to an Enum
pub(crate) trait Node {
    fn location(&self) -> Location;
    fn id(&self) -> NodeId;
    fn children(&self) -> Vec<Rc<dyn Node>>;

    fn to_expr(&self) -> Option<Expr> {
        None
    }
    fn _to_stmt(&self) -> Option<Stmt> {
        None
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]

pub(crate) struct Item {
    pub(crate) kind: Rc<ItemKind>,
    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl Node for Item {
    fn location(&self) -> Location {
        self.loc.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.kind {
            ItemKind::ForeignFuncDecl(f) => {
                let mut children: Vec<Rc<dyn Node>> = vec![];
                for (pat, annot) in f.args.iter() {
                    children.push(pat.clone() as Rc<dyn Node>);
                    if let Some(ty) = annot {
                        children.push(ty.clone())
                    }
                }
                children.push(f.ret_type.clone());
                children
            }
            ItemKind::FuncDef(f) => {
                let mut children: Vec<Rc<dyn Node>> = vec![];
                children_func_def(f, &mut children);
                children
            }
            ItemKind::TypeDef(tydefkind) => match &**tydefkind {
                // TypeDefKind::Alias(_, ty) => vec![ty.clone()],
                // TODO this is redundant, use the Node::children() implementation
                TypeDefKind::Enum(e) => {
                    let mut children: Vec<Rc<dyn Node>> = Vec::new();
                    for param in e.ty_args.iter() {
                        children.push(param.clone());
                    }
                    for variant in e.variants.iter() {
                        children.push(variant.clone() as Rc<dyn Node>);
                    }
                    children
                }
                TypeDefKind::Struct(s) => {
                    let mut children: Vec<Rc<dyn Node>> = Vec::new();
                    for ty in s.ty_args.iter() {
                        children.push(ty.clone());
                    }
                    for field in s.fields.iter() {
                        children.push(field.clone() as Rc<dyn Node>);
                    }
                    children
                }
                TypeDefKind::Foreign(ident) => vec![Rc::new(ident.clone())],
            },
            ItemKind::InterfaceDef(i) => {
                let mut children: Vec<Rc<dyn Node>> = Vec::new();
                for prop in i.methods.iter() {
                    children.push(prop.clone() as Rc<dyn Node>);
                }
                children
            }
            ItemKind::InterfaceImpl(iface_impl) => {
                let mut children: Vec<Rc<dyn Node>> = vec![iface_impl.typ.clone()];
                for method in &iface_impl.methods {
                    children_func_def(method, &mut children);
                }
                children
            }
            ItemKind::Import(ident) => vec![Rc::new(ident.clone())],
            ItemKind::Stmt(stmt) => vec![stmt.clone() as Rc<dyn Node>],
        }
    }
}

fn children_func_def(f: &FuncDef, children: &mut Vec<Rc<dyn Node>>) {
    children.push(Rc::new(f.name.clone()));
    for (pat, annot) in f.args.iter() {
        children.push(pat.clone() as Rc<dyn Node>);
        if let Some(ty) = annot {
            children.push(ty.clone())
        }
    }
    if let Some(ty) = &f.ret_type {
        children.push(ty.clone());
    }
    children.push(f.body.clone());
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum ItemKind {
    ForeignFuncDecl(Rc<ForeignFuncDecl>),
    FuncDef(Rc<FuncDef>),
    TypeDef(Rc<TypeDefKind>),
    InterfaceDef(Rc<InterfaceDecl>),
    InterfaceImpl(Rc<InterfaceImpl>),
    Import(Identifier),
    Stmt(Rc<Stmt>),
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct Stmt {
    pub(crate) kind: Rc<StmtKind>,
    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl Node for Stmt {
    fn location(&self) -> Location {
        self.loc.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.kind {
            StmtKind::FuncDef(f) => {
                let mut children: Vec<Rc<dyn Node>> = vec![];
                for (pat, annot) in f.args.iter() {
                    children.push(pat.clone() as Rc<dyn Node>);
                    if let Some(ty) = annot {
                        children.push(ty.clone())
                    }
                }
                if let Some(ty) = &f.ret_type {
                    children.push(ty.clone());
                }
                children.push(f.body.clone());
                children
            }
            StmtKind::Let(_mutable, (pat, ty), expr) => {
                let mut children: Vec<Rc<dyn Node>> = vec![pat.clone() as Rc<dyn Node>];
                if let Some(ty) = ty {
                    children.push(ty.clone());
                }
                children.push(expr.clone());
                children
            }
            StmtKind::Set(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
            StmtKind::Expr(expr) => vec![expr.clone()],
            StmtKind::Break | StmtKind::Continue => vec![],
            StmtKind::Return(expr) => vec![expr.clone()],
        }
    }

    fn _to_stmt(&self) -> Option<Stmt> {
        Some(self.clone())
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum StmtKind {
    Let(bool, PatAnnotated, Rc<Expr>), // bool is whether it's mutable
    Set(Rc<Expr>, Rc<Expr>),
    Expr(Rc<Expr>),
    FuncDef(Rc<FuncDef>),
    Continue,
    Break,
    Return(Rc<Expr>),
}

pub(crate) type ArgAnnotated = (Rc<Pat>, Option<Rc<Type>>);

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct FuncDef {
    pub(crate) name: Identifier,
    pub(crate) args: Vec<ArgAnnotated>,
    pub(crate) ret_type: Option<Rc<Type>>,
    pub(crate) body: Rc<Expr>,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct ForeignFuncDecl {
    pub(crate) name: Identifier,
    pub(crate) args: Vec<ArgAnnotated>, // TODO: arg annotations are optional but they should be required.
    pub(crate) ret_type: Rc<Type>,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct InterfaceDecl {
    pub(crate) name: Identifier,
    pub(crate) methods: Vec<Rc<InterfaceMethodDecl>>,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct InterfaceMethodDecl {
    pub(crate) name: Identifier,
    pub(crate) ty: Rc<Type>,
}

impl Node for InterfaceMethodDecl {
    fn location(&self) -> Location {
        self.ty.location()
    }
    fn id(&self) -> NodeId {
        self.ty.id()
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        vec![self.ty.clone()]
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct InterfaceImpl {
    pub(crate) iface: Identifier,
    pub(crate) typ: Rc<Type>,
    pub(crate) methods: Vec<Rc<FuncDef>>, // TODO: Don't use Vec<Stmt>. Use Vec<MethodDef>

    pub(crate) id: NodeId,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct Expr {
    pub(crate) kind: Rc<ExprKind>,
    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl Node for Expr {
    fn location(&self) -> Location {
        self.loc.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.kind {
            ExprKind::Identifier(_) => vec![],
            ExprKind::Unit => vec![],
            ExprKind::Int(_) => vec![],
            ExprKind::Float(_) => vec![],
            ExprKind::Bool(_) => vec![],
            ExprKind::Str(_) => vec![],
            ExprKind::List(exprs) => exprs.iter().map(|e| e.clone() as Rc<dyn Node>).collect(),
            ExprKind::Array(exprs) => exprs.iter().map(|e| e.clone() as Rc<dyn Node>).collect(),
            ExprKind::AnonymousFunction(args, ty_opt, body) => {
                let mut children: Vec<Rc<dyn Node>> = Vec::new();
                args.iter().for_each(|(pat, annot)| {
                    children.push(pat.clone());
                    if let Some(ty) = annot {
                        children.push(ty.clone())
                    }
                });
                if let Some(ty) = ty_opt {
                    children.push(ty.clone())
                }
                children.push(body.clone());
                children
            }
            ExprKind::If(cond, then, els) => {
                let mut children: Vec<Rc<dyn Node>> = vec![cond.clone()];
                children.push(then.clone());
                if let Some(els) = els {
                    children.push(els.clone());
                }
                children
            }
            ExprKind::WhileLoop(cond, body) => vec![cond.clone(), body.clone()],
            ExprKind::Block(stmts) => stmts
                .iter()
                .map(|s| s.clone() as Rc<dyn Node>)
                .collect::<Vec<_>>(),
            ExprKind::BinOp(lhs, _, rhs) => vec![lhs.clone(), rhs.clone()],
            ExprKind::FuncAp(func, args) => {
                let mut children: Vec<Rc<dyn Node>> = vec![func.clone() as Rc<dyn Node>];
                children.extend(args.iter().map(|a| a.clone() as Rc<dyn Node>));
                children
            }
            ExprKind::Tuple(exprs) => exprs
                .iter()
                .map(|e| e.clone() as Rc<dyn Node>)
                .collect::<Vec<_>>(),
            ExprKind::Match(expr, arms) => {
                let mut children: Vec<Rc<dyn Node>> = vec![expr.clone()];
                for arm in arms {
                    children.push(arm.pat.clone() as Rc<dyn Node>);
                    children.push(arm.expr.clone() as Rc<dyn Node>);
                }
                children
            }
            ExprKind::MemberAccess(expr, field) => vec![expr.clone(), field.clone()], // TODO: should field really be an expression? maybe just an identifier?
            ExprKind::IndexAccess(expr, index) => vec![expr.clone(), index.clone()],
        }
    }

    fn to_expr(&self) -> Option<Expr> {
        Some(self.clone())
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum ExprKind {
    // EmptyHole,
    Identifier(String),
    Unit,
    Int(i64),
    Float(String), // represented as String to allow Eq and Hash
    Bool(bool),
    Str(String),
    List(Vec<Rc<Expr>>),
    Array(Vec<Rc<Expr>>),
    AnonymousFunction(Vec<ArgAnnotated>, Option<Rc<Type>>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Option<Rc<Expr>>),
    WhileLoop(Rc<Expr>, Rc<Expr>),
    Match(Rc<Expr>, Vec<MatchArm>),
    Block(Vec<Rc<Stmt>>),
    BinOp(Rc<Expr>, BinaryOperator, Rc<Expr>),
    FuncAp(Rc<Expr>, Vec<Rc<Expr>>),
    Tuple(Vec<Rc<Expr>>),
    MemberAccess(Rc<Expr>, Rc<Expr>), // TODO: field should not be an expression? just an identifier.
    IndexAccess(Rc<Expr>, Rc<Expr>),
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

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct MatchArm {
    pub(crate) pat: Rc<Pat>,
    pub(crate) expr: Rc<Expr>,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct Pat {
    pub(crate) kind: Rc<PatKind>,
    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl Node for Pat {
    fn location(&self) -> Location {
        self.loc.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.kind {
            PatKind::Wildcard => vec![],
            PatKind::Binding(_) => vec![],
            PatKind::Unit => vec![],
            PatKind::Int(_) => vec![],
            PatKind::Float(_) => vec![],
            PatKind::Bool(_) => vec![],
            PatKind::Str(_) => vec![],
            PatKind::Variant(ident, pat_opt) => {
                let mut children = vec![Rc::new(ident.clone()) as Rc<dyn Node>];
                if let Some(pat) = pat_opt {
                    children.push(pat.clone());
                }
                children
            }
            PatKind::Tuple(pats) => pats
                .iter()
                .map(|p| p.clone() as Rc<dyn Node>)
                .collect::<Vec<_>>(),
        }
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum PatKind {
    Wildcard,
    Binding(String),
    Variant(Identifier, Option<Rc<Pat>>),
    Unit,
    Int(i64),
    Float(String),
    Bool(bool),
    Str(String),
    Tuple(Vec<Rc<Pat>>),
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct Type {
    pub(crate) kind: Rc<TypeKind>,
    pub(crate) loc: Location,
    pub(crate) id: NodeId,
}

impl Node for Type {
    fn location(&self) -> Location {
        self.loc.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.kind {
            TypeKind::Poly(polytype) => {
                let mut children: Vec<Rc<dyn Node>> = vec![];
                // TODO: gross.
                children.push(Rc::new(polytype.name.clone()) as Rc<dyn Node>);
                children.extend(
                    polytype
                        .iface_names
                        .iter()
                        .map(|t| Rc::new(t.clone()) as Rc<dyn Node>),
                );
                children
            }
            TypeKind::Identifier(_)
            | TypeKind::Unit
            | TypeKind::Int
            | TypeKind::Float
            | TypeKind::Bool
            | TypeKind::Str => {
                vec![]
            }
            TypeKind::Ap(tyname, params) => {
                let mut children: Vec<Rc<dyn Node>> = vec![];
                // TODO: gross.
                children.push(Rc::new(tyname.clone()) as Rc<dyn Node>);
                children.extend(params.iter().map(|t| t.clone() as Rc<dyn Node>));
                children
            }
            TypeKind::Function(lhs, rhs) => {
                let mut children: Vec<Rc<dyn Node>> = vec![];
                children.extend(lhs.iter().map(|t| t.clone() as Rc<dyn Node>));
                children.push(rhs.clone() as Rc<dyn Node>);
                children
            }
            TypeKind::Tuple(types) => types
                .iter()
                .map(|t| t.clone() as Rc<dyn Node>)
                .collect::<Vec<_>>(),
        }
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum TypeKind {
    Poly(Rc<Polytype>),
    Identifier(String),
    Ap(Identifier, Vec<Rc<Type>>),
    Unit,
    Int,
    Float,
    Bool,
    Str,
    Function(Vec<Rc<Type>>, Rc<Type>),
    Tuple(Vec<Rc<Type>>),
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct Polytype {
    pub(crate) name: Identifier,
    pub(crate) iface_names: Vec<Identifier>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct NodeId {
    pub(crate) id: usize,
}

impl NodeId {
    pub(crate) fn new() -> Self {
        static ID_COUNTER: std::sync::atomic::AtomicUsize = AtomicUsize::new(1);
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
    pub fn new(file_id: FileId, pest_span: pest::Span) -> Self {
        Location {
            file_id,
            lo: pest_span.start(),
            hi: pest_span.end(),
        }
    }

    pub fn range(&self) -> std::ops::Range<usize> {
        self.lo..self.hi
    }
}

pub(crate) type NodeMap = HashMap<NodeId, Rc<dyn Node>>;

pub(crate) fn initialize_node_map(node_map: &mut NodeMap, node: &Rc<dyn Node>) {
    node_map.insert(node.id(), node.clone());
    for child in node.children() {
        initialize_node_map(node_map, &child);
    }
}
