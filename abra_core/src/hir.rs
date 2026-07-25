/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
use crate::ast::{BinaryOperator, Location, NodeId};
use crate::parse::PrefixOp;
pub(crate) use crate::statics::Type;
use crate::vm::AbraInt;

#[derive(Debug)]
pub(crate) struct Program {
    pub(crate) funcs: Vec<Function>,
}

#[derive(Debug)]
pub(crate) struct Function {
    pub(crate) return_ty: Type,
    pub(crate) body: Expr,
}

#[derive(Debug)]
pub(crate) struct Expr {
    pub(crate) ty: Type,
    pub(crate) kind: ExprKind,
    pub(crate) span: Location,
}

#[derive(Debug)]
pub(crate) enum ExprKind {
    Variable(NodeId),
    Int(i64),
    Float(String),
    Bool(bool),
    String(String),
    Array(Vec<Box<Expr>>),
    Block(Vec<Stmt>),
    // AnonymousFunction
    IfElse(Box<Expr>, Box<Stmt>, Option<Box<Stmt>>),
    // Match(Box<Expr>, Vec<Box<MatchArm>>), // replace this with a switch?
    BinOp(Box<Expr>, BinaryOperator, Box<Expr>),
    Unop(PrefixOp, Box<Expr>),
    FuncCall(Box<Expr>, Vec<Box<Expr>>),
    Tuple(Vec<Box<Expr>>),
    // MemberAccess
    // MemberAccessLeadingDot
    IndexAccess(Box<Expr>, Box<Expr>),
    // TaskBlock
}

/*
    AnonymousFunction(Vec<ArgMaybeAnnotated>, Option<Rc<Type>>, Rc<Expr>),
    IfElse(Rc<Expr>, Rc<Stmt>, Option<Rc<Stmt>>),
    Match(Rc<Expr>, Vec<Rc<MatchArm>>),
    Block(Vec<Rc<Stmt>>),
    BinOp(Rc<Expr>, BinaryOperator, Rc<Expr>),
    Unop(PrefixOp, Rc<Expr>),
    FuncCall(Rc<Expr>, Vec<FuncCallArg>),
    Tuple(Vec<Rc<Expr>>),
    MemberAccess(Rc<Expr>, Rc<Identifier>),
    MemberAccessLeadingDot(Rc<Identifier>),
    IndexAccess(Rc<Expr>, Rc<Expr>),
    Unwrap(Rc<Expr>),
    Try(Rc<Expr>),
    TaskBlock(Rc<Expr>),
*/

#[derive(Debug)]
pub(crate) struct Stmt {
    pub(crate) kind: StmtKind,
    pub(crate) span: Location,
}

#[derive(Debug)]
pub(crate) enum StmtKind {
    Let(Pat, Box<Expr>),
    Var(Pat, Box<Expr>),
    Assign(Box<Expr>, Box<Expr>),
    Expr(Box<Expr>),
    Continue,
    Break,
    Return(Option<Box<Expr>>),
    Loop,
}

#[derive(Debug)]
pub(crate) struct Pat {
    pub(crate) ty: Type,
    pub(crate) kind: PatKind,
    pub(crate) span: Location,
}

#[derive(Debug)]
pub(crate) enum PatKind {
    Wildcard,
    Binding(NodeId),
    // Variant
    Void,
    Int(AbraInt),
    Float(String),
    Bool(bool),
    Str(String),
    Tuple(Vec<Box<Pat>>),
}

/*
    Wildcard,
    Binding(String),
    Variant(Vec<Rc<Identifier>>, Rc<Identifier>, Option<PatVariantData>),
    Void,
    Int(AbraInt),
    Float(String),
    Bool(bool),
    Str(String),
    Tuple(Vec<Rc<Pat>>),
    // struct patterns match every field, either all positionally or all by name,
    // e.g. Point(a, b) or Point(x = a, y = b)
    Struct(Rc<Identifier>, PatStructFields),
    Or(Rc<Pat>, Rc<Pat>),
*/
