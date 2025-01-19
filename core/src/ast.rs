use std::collections::HashMap;
use std::fmt::Display;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct Identifier {
    pub(crate) v: String,

    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for Identifier {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        vec![]
    }
}

pub(crate) type ArgAnnotated = (Rc<Pat>, Option<Rc<Type>>);

#[derive(Debug, Clone, Default)]
pub(crate) struct Sources {
    pub(crate) filename_to_source: HashMap<String, String>,
}

pub(crate) type PatAnnotated = (Rc<Pat>, Option<Rc<Type>>);

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) struct FileAst {
    pub(crate) items: Vec<Rc<Item>>,
    pub(crate) name: String,
    pub(crate) path: PathBuf,

    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for FileAst {
    fn span(&self) -> Span {
        self.span.clone()
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

    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for Variant {
    fn span(&self) -> Span {
        self.span.clone()
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

    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for StructField {
    fn span(&self) -> Span {
        self.span.clone()
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
            .field("span", &self.span())
            .field("id", &self.id())
            .finish()
    }
}

// TODO: convert this to an Enum
pub(crate) trait Node {
    fn span(&self) -> Span;
    fn id(&self) -> NodeId;
    fn children(&self) -> Vec<Rc<dyn Node>>;

    fn to_expr(&self) -> Option<Expr> {
        None
    }
    fn to_stmt(&self) -> Option<Stmt> {
        None
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]

pub(crate) struct Item {
    pub(crate) kind: Rc<ItemKind>,
    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for Item {
    fn span(&self) -> Span {
        self.span.clone()
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
                TypeDefKind::Foreign(_) => vec![],
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
            ItemKind::Import(_) => vec![],
            ItemKind::Stmt(stmt) => vec![stmt.clone() as Rc<dyn Node>],
        }
    }
}

fn children_func_def(f: &FuncDef, children: &mut Vec<Rc<dyn Node>>) {
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
    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for Stmt {
    fn span(&self) -> Span {
        self.span.clone()
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
        }
    }

    fn to_stmt(&self) -> Option<Stmt> {
        Some(self.clone())
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum StmtKind {
    Let(bool, PatAnnotated, Rc<Expr>), // bool is whether it's mutable
    Set(Rc<Expr>, Rc<Expr>),
    Expr(Rc<Expr>),
    FuncDef(Rc<FuncDef>),
}

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
    fn span(&self) -> Span {
        self.ty.span()
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
    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for Expr {
    fn span(&self) -> Span {
        self.span.clone()
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
            ExprKind::Func(args, ty_opt, body) => {
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
    Func(Vec<ArgAnnotated>, Option<Rc<Type>>, Rc<Expr>),
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

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
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
    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for Pat {
    fn span(&self) -> Span {
        self.span.clone()
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
            PatKind::Variant(_, pat_opt) => {
                if let Some(pat) = pat_opt {
                    vec![pat.clone()]
                } else {
                    vec![]
                }
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
    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for Type {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.kind {
            TypeKind::Poly(_, _)
            | TypeKind::Identifier(_)
            | TypeKind::Unit
            | TypeKind::Int
            | TypeKind::Float
            | TypeKind::Bool
            | TypeKind::Str => {
                vec![]
            }
            TypeKind::Ap(_ty, params) => {
                let mut children: Vec<Rc<dyn Node>> = vec![];
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
    Poly(Identifier, Vec<Identifier>),
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
pub(crate) struct Span {
    // TODO: this is egregious
    // storing the filename for every single Span? Every single node in the AST? Lol.
    pub(crate) filename: String,
    pub(crate) lo: usize,
    pub(crate) hi: usize,
}

impl Span {
    pub fn new(filename: &str, pest_span: pest::Span) -> Self {
        Span {
            filename: filename.to_string(),
            lo: pest_span.start(),
            hi: pest_span.end(),
        }
    }

    pub(crate) fn lines_and_columns(&self, source: &str) -> ((usize, usize), (usize, usize)) {
        let lo_line = source[..=self.lo].lines().count() - 1;
        let num_chars_of_lines_before = source
            .lines()
            .enumerate()
            .filter(|(i, _)| *i < lo_line)
            .map(|(_, l)| l.len())
            .sum::<usize>()
            + lo_line; // account for newlines
        let lo_col = self.lo - num_chars_of_lines_before;

        let hi_line = source[..self.hi].lines().count() - 1;
        let num_chars_of_lines_before = source
            .lines()
            .enumerate()
            .filter(|(i, _)| *i < hi_line)
            .map(|(_, l)| l.len())
            .sum::<usize>()
            + hi_line; // account for newlines
        let hi_col = self.hi - num_chars_of_lines_before - 1;
        ((lo_line, lo_col), (hi_line, hi_col))
    }

    pub(crate) fn display(&self, s: &mut String, sources: &Sources, detail: &str) {
        let source = sources.filename_to_source.get(&self.filename).unwrap();
        let ((lo_line, lo_col), (hi_line, hi_col)) = self.lines_and_columns(source);
        if lo_line != hi_line {
            s.push_str(&format!(
                "--> On lines {}-{} of {}, {}\n",
                lo_line + 1,
                hi_line + 1,
                self.filename,
                detail
            ));
        } else {
            s.push_str(&format!(
                "--> On line {} of {}, {}\n",
                lo_line + 1,
                self.filename,
                detail
            ));
        }
        for line_number in lo_line..=hi_line {
            let line = source.lines().nth(line_number).unwrap();
            s.push_str(&format!("{:3} | {}\n", line_number + 1, line));

            let pad_before = if line_number == lo_line { lo_col } else { 0 };
            let num_tabs = line.chars().take(pad_before).filter(|c| *c == '\t').count();
            let pad_before_in_spaces = pad_before + num_tabs * 3;

            let underline_length = if line_number == hi_line {
                hi_col - pad_before + 1
            } else {
                line.len() - pad_before
            };
            s.push_str(&format!("{:3} | ", "")); // line number placeholder
            s.push_str(&format!("{:1$}", "", pad_before_in_spaces)); // pad before
            s.push_str(&format!("{:^<1$}\n", "", underline_length)); // underline
        }
    }
}

pub(crate) type NodeMap = HashMap<NodeId, Rc<dyn Node>>;

pub(crate) fn initialize_node_map(node_map: &mut NodeMap, node: &Rc<dyn Node>) {
    node_map.insert(node.id(), node.clone());
    for child in node.children() {
        initialize_node_map(node_map, &child);
    }
}
