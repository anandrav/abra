/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ast::{
    AstNode, Expr, ExprKind, FileAst, Item, ItemKind, MatchArm, Pat, PatKind, Stmt, StmtKind,
};

use core::panic;

use super::typecheck::Nominal;
use super::{Declaration, EnumDef, Error, SolvedType, StaticsContext, TypeKind};
use crate::vm::AbraInt;
use std::fmt::{self, Display};
use std::rc::Rc;
use utils::hash::HashSet;

pub(crate) fn check_pattern_exhaustiveness_and_usefulness(
    ctx: &mut StaticsContext,
    files: &[Rc<FileAst>],
) {
    for file in files {
        check_pattern_exhaustiveness_file(ctx, file);
    }
}

fn check_pattern_exhaustiveness_file(statics: &mut StaticsContext, file: &FileAst) {
    for item in file.items.iter() {
        check_pattern_exhaustiveness_item(statics, item);
    }
}

fn check_pattern_exhaustiveness_item(statics: &mut StaticsContext, stmt: &Item) {
    match &*stmt.kind {
        ItemKind::Import(..) => {}
        ItemKind::InterfaceDef(..) => {}
        ItemKind::TypeDef(..) => {}
        ItemKind::FuncDecl { .. } => {}
        ItemKind::InterfaceImpl(iface_impl) => {
            for f in &iface_impl.methods {
                check_pattern_exhaustiveness_expr(statics, &f.body);
            }
        }
        ItemKind::Extension(ext) => {
            for f in &ext.methods {
                check_pattern_exhaustiveness_expr(statics, &f.body);
            }
        }
        ItemKind::FuncDef(f) => {
            check_pattern_exhaustiveness_expr(statics, &f.body);
        }
        ItemKind::Stmt(stmt) => {
            check_pattern_exhaustiveness_stmt(statics, stmt);
        }
    }
}

fn check_pattern_exhaustiveness_stmt(statics: &mut StaticsContext, stmt: &Stmt) {
    match &*stmt.kind {
        StmtKind::Assign(_, _, expr) => {
            check_pattern_exhaustiveness_expr(statics, expr);
        }
        StmtKind::Let(_, _, expr) => {
            check_pattern_exhaustiveness_expr(statics, expr);
        }
        StmtKind::Expr(expr) => {
            check_pattern_exhaustiveness_expr(statics, expr);
        }
        StmtKind::Break | StmtKind::Continue => {}
        StmtKind::Return(expr) => {
            check_pattern_exhaustiveness_expr(statics, expr);
        }
        StmtKind::WhileLoop(cond, statements) => {
            check_pattern_exhaustiveness_expr(statics, cond);
            for statement in statements {
                check_pattern_exhaustiveness_stmt(statics, statement);
            }
        }
        StmtKind::ForLoop(_, iterable, statements) => {
            check_pattern_exhaustiveness_expr(statics, iterable);
            for statement in statements {
                check_pattern_exhaustiveness_stmt(statics, statement);
            }
        }
    }
}

fn check_pattern_exhaustiveness_expr(statics: &mut StaticsContext, expr: &Rc<Expr>) {
    match &*expr.kind {
        ExprKind::Match(scrutiny, arms) => {
            if statics.solution_of_node(scrutiny.node()).is_none() {
                return;
            }
            for arm in arms {
                if statics.solution_of_node(arm.node()).is_none() {
                    return;
                }
            }

            match_expr_exhaustive_check(statics, expr.node(), scrutiny, arms);
        }

        ExprKind::Nil
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Str(_)
        | ExprKind::Variable { .. } => {}
        ExprKind::Array(exprs) => {
            for expr in exprs {
                check_pattern_exhaustiveness_expr(statics, expr);
            }
        }
        ExprKind::BinOp(left, _op, right) => {
            check_pattern_exhaustiveness_expr(statics, left);
            check_pattern_exhaustiveness_expr(statics, right);
        }
        ExprKind::Unop(_op, right) => {
            check_pattern_exhaustiveness_expr(statics, right);
        }
        ExprKind::Block(statements) => {
            for statement in statements {
                check_pattern_exhaustiveness_stmt(statics, statement);
            }
        }
        ExprKind::IfElse(cond, stmt1, stmt2) => {
            check_pattern_exhaustiveness_expr(statics, cond);
            check_pattern_exhaustiveness_stmt(statics, stmt1);
            if let Some(stmt2) = stmt2 {
                check_pattern_exhaustiveness_stmt(statics, stmt2);
            }
        }
        ExprKind::AnonymousFunction(_args, _out_annot, body) => {
            check_pattern_exhaustiveness_expr(statics, body);
        }
        ExprKind::MemberFuncAp(expr, _, args) => {
            if let Some(expr) = expr {
                check_pattern_exhaustiveness_expr(statics, expr);
            }
            for arg in args {
                check_pattern_exhaustiveness_expr(statics, arg);
            }
        }
        ExprKind::FuncAp(func, args) => {
            check_pattern_exhaustiveness_expr(statics, func);
            for arg in args {
                check_pattern_exhaustiveness_expr(statics, arg);
            }
        }
        ExprKind::Tuple(exprs) => {
            for expr in exprs {
                check_pattern_exhaustiveness_expr(statics, expr);
            }
        }
        ExprKind::MemberAccess(expr, _) => {
            check_pattern_exhaustiveness_expr(statics, expr);
        }
        ExprKind::MemberAccessLeadingDot(_ident) => {}
        ExprKind::IndexAccess(expr, index) => {
            check_pattern_exhaustiveness_expr(statics, expr);
            check_pattern_exhaustiveness_expr(statics, index);
        }
        ExprKind::Unwrap(expr) => {
            check_pattern_exhaustiveness_expr(statics, expr);
        }
    }
}

// Exhaustiveness and usefulness analysis for pattern matching
// uses same algorithm as Rust compiler: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_pattern_analysis/usefulness/index.html
#[derive(Debug, Clone)]
struct Matrix {
    rows: Vec<MatrixRow>,
    types: Vec<SolvedType>,
}

impl Matrix {
    fn new(statics: &StaticsContext, scrutinee_ty: SolvedType, arms: &[Rc<MatchArm>]) -> Self {
        let types = vec![scrutinee_ty];
        let mut rows = Vec::new();
        for (dummy, arm) in arms.iter().enumerate() {
            let pats = vec![DeconstructedPat::from_ast_pat(statics, &arm.pat)];
            rows.push(MatrixRow {
                pats,
                parent_row: dummy,
                useful: false,
            });
        }
        Self { rows, types }
    }

    fn head_column(&self) -> Vec<DeconstructedPat> {
        if self.rows.is_empty() {
            return vec![];
        }
        self.rows.iter().map(|row| row.head()).collect()
    }

    fn specialize(
        &self,
        ctor: &Constructor,
        ctor_arity: usize,
        statics: &StaticsContext,
    ) -> Matrix {
        let mut new_types = Vec::new();
        match ctor {
            Constructor::Int(..)
            | Constructor::Float(..)
            | Constructor::String(..)
            | Constructor::Bool(..)
            | Constructor::Wildcard(..) => {}
            Constructor::Product => match &self.types[0] {
                SolvedType::Tuple(tys) => {
                    new_types.extend(tys.clone());
                }
                SolvedType::Void => {}
                _ => unreachable!(),
            },
            Constructor::Variant((enum_def, idx)) => {
                let variant = &enum_def.variants[*idx];
                let variant_data = &variant.data;
                let data_ty = if let Some(data) = &variant_data {
                    data.to_solved_type(statics).unwrap()
                } else {
                    SolvedType::Void
                };
                match data_ty {
                    SolvedType::Never => unreachable!(),
                    SolvedType::InterfaceOutput(..) => unreachable!(),
                    SolvedType::Void => {}
                    SolvedType::Poly(..)
                    | SolvedType::Bool
                    | SolvedType::Int
                    | SolvedType::String
                    | SolvedType::Float
                    | SolvedType::Function(..)
                    | SolvedType::Tuple(_)
                    | SolvedType::Nominal(..) => new_types.push(data_ty),
                }
            }
        }

        new_types.extend(self.types[1..].iter().cloned());

        let mut new_matrix = Matrix {
            rows: vec![],
            types: new_types,
        };
        for (i, row) in self.rows.iter().enumerate() {
            if row.pats.is_empty() {
                panic!("no pats in row");
            }
            if ctor.is_covered_by(&row.head().ctor) {
                let new_row = row.pop_head(ctor, ctor_arity, i, statics);
                new_matrix.rows.push(new_row);
            }
        }
        new_matrix
    }

    fn unspecialize(&mut self, specialized: Self) {
        for child_row in specialized.rows.iter() {
            let parent_row = &mut self.rows[child_row.parent_row];
            parent_row.useful |= child_row.useful;
        }
    }
}

impl Display for Matrix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f)?;
        for row in self.rows.iter() {
            if row.pats.is_empty() {
                write!(f, "()")?;
            }
            for (i, pat) in row.pats.iter().enumerate() {
                if i != 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{pat}")?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct MatrixRow {
    pats: Vec<DeconstructedPat>,
    parent_row: usize,
    useful: bool,
}

impl MatrixRow {
    fn head(&self) -> DeconstructedPat {
        match self.pats.first() {
            Some(p) => p.clone(),
            None => panic!(),
        }
    }

    fn pop_head(
        &self,
        other_ctor: &Constructor,
        arity: usize,
        parent_row: usize,
        statics: &StaticsContext,
    ) -> MatrixRow {
        if self.pats.is_empty() {
            panic!("no pats in row");
        }

        let head_pat = self.head();

        let mut new_pats = head_pat.specialize(other_ctor, arity, statics);

        new_pats.extend_from_slice(&self.pats[1..]);
        MatrixRow {
            pats: new_pats,
            parent_row,
            useful: false,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct DeconstructedPat {
    ctor: Constructor,
    fields: Vec<DeconstructedPat>,
    ty: SolvedType,
}

impl DeconstructedPat {
    fn from_ast_pat(statics: &StaticsContext, pat: &Rc<Pat>) -> Self {
        let ty = statics.solution_of_node(pat.node()).unwrap();

        let mut fields = vec![];
        let ctor = match &*pat.kind {
            PatKind::Wildcard => Constructor::Wildcard(WildcardReason::UserCreated),
            PatKind::Binding(_ident) => Constructor::Wildcard(WildcardReason::VarPat),
            PatKind::Bool(b) => Constructor::Bool(*b),
            PatKind::Int(i) => Constructor::Int(*i),
            PatKind::Float(f) => Constructor::Float(f.clone()),
            PatKind::Str(s) => Constructor::String(s.clone()),
            PatKind::Void => Constructor::Product,
            PatKind::Tuple(elems) => {
                fields = elems
                    .iter()
                    .map(|pat| DeconstructedPat::from_ast_pat(statics, pat))
                    .collect();
                Constructor::Product
            }
            PatKind::Variant(_prefixes, ident, data) => {
                let Some(Declaration::EnumVariant {
                    e: enum_def,
                    variant,
                }) = statics.resolution_map.get(&ident.id)
                else {
                    panic!()
                };
                fields = data
                    .iter()
                    .map(|pat| DeconstructedPat::from_ast_pat(statics, pat))
                    .collect();
                Constructor::Variant((enum_def.clone(), *variant))
            }
        };
        Self { ctor, fields, ty }
    }

    fn specialize(
        &self,
        other_ctor: &Constructor,
        arity: usize,
        statics: &StaticsContext,
    ) -> Vec<DeconstructedPat> {
        match &self.ctor {
            Constructor::Wildcard(_) => {
                let field_tys = self.field_tys(other_ctor, statics);
                (0..arity)
                    .map(|i| DeconstructedPat {
                        ctor: Constructor::Wildcard(WildcardReason::MatrixSpecialization),
                        fields: vec![],
                        ty: field_tys[i].clone(),
                    })
                    .collect()
            }
            _ => self.fields.clone(),
        }
    }

    fn field_tys(&self, ctor: &Constructor, statics: &StaticsContext) -> Vec<SolvedType> {
        match &self.ty {
            SolvedType::Int
            | SolvedType::Float
            | SolvedType::String
            | SolvedType::Bool
            | SolvedType::Void
            | SolvedType::Poly(..)
            | SolvedType::InterfaceOutput(..)
            | SolvedType::Function(..) => vec![],
            SolvedType::Tuple(tys) => tys.clone(),
            SolvedType::Nominal(_, _) => match ctor {
                Constructor::Variant((enum_def, idx)) => {
                    let variant = &enum_def.variants[*idx];
                    let variant_data = &variant.data;
                    let data_ty = if let Some(data) = &variant_data {
                        data.to_solved_type(statics).unwrap()
                    } else {
                        SolvedType::Void
                    };

                    if !matches!(data_ty, SolvedType::Void) {
                        vec![data_ty.clone()]
                    } else {
                        vec![]
                    }
                }
                Constructor::Wildcard(_) => {
                    vec![]
                }
                _ => panic!("unexpected constructor"),
            },
            SolvedType::Never => unreachable!(),
        }
    }

    fn missing_from_ctor(ctor: &Constructor, ty: SolvedType) -> Self {
        let fields = match ty.clone() {
            SolvedType::Tuple(tys) | SolvedType::Nominal(_, tys) => tys
                .iter()
                .map(|ty| DeconstructedPat {
                    ctor: Constructor::Wildcard(WildcardReason::NonExhaustive),
                    fields: vec![],
                    ty: ty.clone(),
                })
                .collect(),
            _ => vec![],
        };
        Self {
            ctor: ctor.clone(),
            fields,
            ty,
        }
    }
}

impl Display for DeconstructedPat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.ctor {
            Constructor::Wildcard(_) => write!(f, "_"),
            Constructor::Bool(b) => write!(f, "{b}"),
            Constructor::Int(i) => write!(f, "{i}"),
            Constructor::Float(fl) => write!(f, "{fl}"),
            Constructor::String(s) => write!(f, "{s}"),
            Constructor::Product => {
                write!(f, "(")?;
                for (i, field) in self.fields.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{field}")?;
                }
                write!(f, ")")
            }
            Constructor::Variant((enum_def, idx)) => {
                let variant_name = &enum_def.variants[*idx].ctor.v;
                write!(f, "{variant_name}")?;
                if !self.fields.is_empty() {
                    write!(f, " of ")?;
                    for (i, field) in self.fields.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{field}")?;
                    }
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Constructor {
    Wildcard(WildcardReason), // user-created wildcard pattern
    Bool(bool),
    Int(AbraInt),
    Float(String),
    String(String),
    Product, // tuples, including unit
    Variant(EnumVariant),
}

impl Constructor {
    fn is_covered_by(&self, other: &Constructor) -> bool {
        match (self, other) {
            (_, Constructor::Wildcard(_)) => true,
            (Constructor::Wildcard(_), _) => false,

            (Constructor::Bool(b1), Constructor::Bool(b2)) => b1 == b2,
            (Constructor::Variant(..), Constructor::Variant(..)) => self == other,
            (Constructor::Int(i1), Constructor::Int(i2)) => i1 == i2,
            (Constructor::Float(f1), Constructor::Float(f2)) => f1 == f2,
            (Constructor::String(s1), Constructor::String(s2)) => s1 == s2,
            (Constructor::Product, Constructor::Product) => true,
            _ => panic!("comparing incompatible constructors"),
        }
    }

    fn as_bool(&self) -> Option<bool> {
        match self {
            Constructor::Bool(b) => Some(*b),
            _ => None,
        }
    }

    fn as_variant(&self) -> Option<EnumVariant> {
        match self {
            Constructor::Variant(ev) => Some(ev.clone()),
            _ => None,
        }
    }

    fn arity(&self, matrix_tys: &[SolvedType]) -> usize {
        match self {
            Constructor::Bool(..)
            | Constructor::Int(..)
            | Constructor::String(..)
            | Constructor::Float(..)
            | Constructor::Wildcard(..) => 0,
            Constructor::Product => match &matrix_tys[0] {
                SolvedType::Tuple(tys) => tys.len(),
                SolvedType::Void => 0,
                _ => panic!("unexpected type for product constructor: {}", matrix_tys[0]),
            },
            Constructor::Variant((enum_def, idx)) => {
                let variant = &enum_def.variants[*idx];
                match &variant.data {
                    None => 0,
                    Some(ty) => match &*ty.kind {
                        TypeKind::Void => 0,
                        _ => 1,
                    },
                }
            }
        }
    }

    fn is_wildcard_nonexhaustive(&self) -> bool {
        matches!(self, Constructor::Wildcard(WildcardReason::NonExhaustive))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum WildcardReason {
    UserCreated,          // a wildcard typed by the user
    VarPat, // a variable pattern created by the user, which similar to wildcard, matches anything
    NonExhaustive, // wildcards introduced by algorithm when user did not cover all constructors
    MatrixSpecialization, // wildcards introduced by algorithm during matrix specialization, which are potentially expanded from _ to (_, _, _) etc.
}

#[derive(Debug, Clone)]
struct WitnessMatrix {
    rows: Vec<Vec<DeconstructedPat>>,
}

impl WitnessMatrix {
    fn empty() -> Self {
        Self { rows: vec![] }
    }

    fn unit_witness() -> Self {
        Self { rows: vec![vec![]] }
    }

    fn extend(&mut self, other: &Self) {
        self.rows.extend_from_slice(&other.rows);
    }

    fn push_pattern(&mut self, pat: DeconstructedPat) {
        for witness in self.rows.iter_mut() {
            witness.push(pat.clone());
        }
    }

    fn apply_constructor(&mut self, ctor: &Constructor, arity: usize, head_ty: &SolvedType) {
        for witness in self.rows.iter_mut() {
            let len = witness.len();
            let fields: Vec<DeconstructedPat> = witness.drain((len - arity)..).rev().collect();
            let first_pat = DeconstructedPat {
                ctor: ctor.clone(),
                fields,
                ty: head_ty.clone(),
            };

            witness.push(first_pat);
        }
    }

    fn apply_missing_constructors(&mut self, missing_ctors: &[Constructor], head_ty: &SolvedType) {
        if missing_ctors.is_empty() {
            return;
        }

        let mut ret = Self::empty();
        for ctor in missing_ctors.iter() {
            let mut witness_matrix = self.clone();
            let missing_pat = DeconstructedPat::missing_from_ctor(ctor, head_ty.clone());
            witness_matrix.push_pattern(missing_pat);
            ret.extend(&witness_matrix);
        }
        *self = ret;
    }

    fn first_column(&self) -> Vec<DeconstructedPat> {
        self.rows.iter().map(|row| row[0].clone()).collect()
    }
}

impl Display for WitnessMatrix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f)?;
        for row in self.rows.iter() {
            if row.len() > 1 {
                write!(f, "(")?;
            }
            for (i, pat) in row.iter().enumerate() {
                if i != 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{pat}")?;
            }
            if row.len() > 1 {
                write!(f, ")")?;
            }
        }
        Ok(())
    }
}

type EnumVariant = (Rc<EnumDef>, usize);

#[derive(Debug, Clone)]
enum ConstructorSet {
    Bool,
    EnumVariants(Vec<EnumVariant>),
    Product,    // tuples, including unit
    Unlistable, // int, float, string
}

#[derive(Debug, Clone)]
struct SplitConstructorSet {
    present_ctors: Vec<Constructor>,
    missing_ctors: Vec<Constructor>,
}

impl ConstructorSet {
    fn split(&self, head_ctors: &[Constructor]) -> SplitConstructorSet {
        let mut present_ctors = Vec::new();
        let mut missing_ctors = Vec::new();
        // Constructors in `head_ctors`, except wildcards and opaques.
        let mut seen: Vec<Constructor> = Vec::new();
        let mut wildcard_seen = false;
        for ctor in head_ctors.iter().cloned() {
            if let Constructor::Wildcard(_) = &ctor {
                wildcard_seen = true;
            }
            seen.push(ctor)
        }

        match self {
            ConstructorSet::Product => {
                if !seen.is_empty() {
                    present_ctors.push(Constructor::Product);
                } else {
                    missing_ctors.push(Constructor::Product);
                }
            }
            ConstructorSet::EnumVariants(enum_variants) => {
                let mut missing_set: HashSet<EnumVariant> = enum_variants.iter().cloned().collect();
                for identifier in seen.iter().filter_map(|ctor| ctor.as_variant()) {
                    if missing_set.remove(&identifier) {
                        present_ctors.push(Constructor::Variant(identifier.clone()));
                    }
                }
                for identifier in missing_set {
                    missing_ctors.push(Constructor::Variant(identifier));
                }
            }
            ConstructorSet::Bool => {
                let mut seen_false = false;
                let mut seen_true = false;
                for b in seen.iter().filter_map(|ctor| ctor.as_bool()) {
                    if b {
                        seen_true = true;
                    } else {
                        seen_false = true;
                    }
                }
                if seen_false {
                    present_ctors.push(Constructor::Bool(false));
                } else {
                    missing_ctors.push(Constructor::Bool(false));
                }
                if seen_true {
                    present_ctors.push(Constructor::Bool(true));
                } else {
                    missing_ctors.push(Constructor::Bool(true));
                }
            }
            ConstructorSet::Unlistable => {
                present_ctors.extend(seen);
                if !wildcard_seen {
                    missing_ctors.push(Constructor::Wildcard(WildcardReason::NonExhaustive));
                }
            }
        }

        SplitConstructorSet {
            present_ctors,
            missing_ctors,
        }
    }
}

// identify missing and extra constructors in patterns
fn match_expr_exhaustive_check(
    statics: &mut StaticsContext,
    node: AstNode,
    scrutiny: &Rc<Expr>,
    arms: &[Rc<MatchArm>],
) {
    let scrutinee_ty = statics.solution_of_node(scrutiny.node());
    let Some(scrutinee_ty) = scrutinee_ty else {
        return;
    };

    let mut matrix = Matrix::new(statics, scrutinee_ty, arms);

    let witness_matrix = compute_exhaustiveness_and_usefulness(statics, &mut matrix);

    let witness_patterns = witness_matrix.first_column();
    if !witness_patterns.is_empty() {
        statics.errors.push(Error::NonexhaustiveMatch {
            node: node.clone(),
            missing: witness_patterns,
        });
    }

    let mut useless_indices = HashSet::default();
    for (i, row) in matrix.rows.iter().enumerate() {
        if !row.useful {
            useless_indices.insert(i);
        }
    }
    let mut redundant_arms = Vec::new();
    redundant_arms.extend(arms.iter().enumerate().filter_map(|(i, arm)| {
        if useless_indices.contains(&i) {
            Some(arm.pat.node())
        } else {
            None
        }
    }));
    if !redundant_arms.is_empty() {
        statics.errors.push(Error::RedundantArms {
            node,
            redundant_arms,
        })
    }
}

// here's where the actual match usefulness algorithm goes
fn compute_exhaustiveness_and_usefulness(
    statics: &StaticsContext,
    matrix: &mut Matrix,
) -> WitnessMatrix {
    // base case
    let Some(head_ty) = matrix.types.first().cloned() else {
        // we are morally pattern matching on ()
        let mut useful = true;
        // only the first row is useful
        for row in matrix.rows.iter_mut() {
            row.useful = useful;
            useful = false;
        }
        let no_useful_rows = useful;
        return if no_useful_rows {
            // match was not exhaustive (there were no rows)

            WitnessMatrix::unit_witness()
        } else {
            // match was exhaustive

            WitnessMatrix::empty()
        };
    };

    let mut ret_witnesses = WitnessMatrix::empty();

    let head_ctors: Vec<Constructor> = matrix
        .head_column()
        .iter()
        .cloned()
        .map(|pat| pat.ctor)
        .collect();

    let ctors_for_ty = ctors_for_ty(&head_ty);
    let SplitConstructorSet {
        mut present_ctors,
        missing_ctors,
    } = ctors_for_ty.split(&head_ctors);

    // special constructor representing cases not listed by user
    if !missing_ctors.is_empty() {
        present_ctors.push(Constructor::Wildcard(WildcardReason::NonExhaustive));
    }

    for ctor in present_ctors {
        let ctor_arity = ctor.arity(&matrix.types);

        let mut specialized_matrix = matrix.specialize(&ctor, ctor_arity, statics);

        let mut witnesses = compute_exhaustiveness_and_usefulness(statics, &mut specialized_matrix);

        if ctor.is_wildcard_nonexhaustive() {
            // special constructor representing cases not listed by user
            witnesses.apply_missing_constructors(&missing_ctors, &head_ty);
        } else {
            witnesses.apply_constructor(&ctor, ctor_arity, &head_ty);
        }

        ret_witnesses.extend(&witnesses);

        matrix.unspecialize(specialized_matrix);
    }

    ret_witnesses
}

fn ctors_for_ty(ty: &SolvedType) -> ConstructorSet {
    match ty {
        SolvedType::Bool => ConstructorSet::Bool,
        SolvedType::Nominal(nominal, _) => {
            let Nominal::Enum(enum_def) = nominal else { panic!() };
            let variants: Vec<_> = enum_def
                .variants
                .iter()
                .enumerate()
                .map(|(i, _)| (enum_def.clone(), i))
                .collect();
            ConstructorSet::EnumVariants(variants)
        }
        SolvedType::Tuple(..) => ConstructorSet::Product,
        SolvedType::Void => ConstructorSet::Product,
        SolvedType::Int | SolvedType::Float | SolvedType::String | SolvedType::Function(..) => {
            ConstructorSet::Unlistable
        }
        SolvedType::Poly(..) => ConstructorSet::Unlistable,

        SolvedType::Never => unreachable!(),
        SolvedType::InterfaceOutput(..) => unreachable!(),
    }
}
