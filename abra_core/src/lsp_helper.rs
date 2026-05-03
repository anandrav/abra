// --- LSP utilities: find AST nodes at a given byte offset ---

use crate::ast::{
    ArgMaybeAnnotated, AstNode, Expr, ExprKind, FileAst, FuncDef, Item, ItemKind, Pat, PatKind,
    Stmt, StmtKind, Type, TypeDefKind, TypeKind,
};
use crate::{
    CompletionCandidate, CompletionCandidateKind, DefinitionInfo, FileId, LspAnalysisResult, ast,
    lsp_helper, statics,
};
use std::ops::Range;
use std::rc::Rc;

impl LspAnalysisResult {
    /// Collect every `Declaration` that the name `ident_name` could refer to in
    /// the cursor's scope, in priority order: import aliases, the file's
    /// top-level namespace, then bindings/args/Variable usages found in the AST.
    pub(crate) fn find_completion_targets(
        &self,
        file_ast: &ast::FileAst,
        ident_name: &str,
    ) -> Vec<statics::Declaration> {
        use statics::Declaration;

        let mut targets = vec![];

        // 1. Imports with an `As` alias (`use core/fs as fs`).
        for item in &file_ast.items {
            if let ItemKind::Import(path, ast::ImportKind::As(alias)) = &*item.kind
                && alias.v == ident_name
                && let Some(ns) = self.ctx.root_namespace.namespaces.get(&path.v)
            {
                targets.push(Declaration::Namespace(ns.clone(), alias.node()));
            }
        }

        // 2. File's own top-level namespace — populated by scan_declarations
        //    for every item that parsed (types, enums, interfaces, free fns).
        //    This is what makes `Color.<TAB>` work even when the using-item
        //    failed to parse.
        if let Some(file_ns) = self
            .ctx
            .root_namespace
            .namespaces
            .get(&file_ast.package_name_str)
            && let Some(decl) = file_ns.declarations.get(ident_name)
        {
            targets.push(decl.clone());
        }

        // 3. Variable expressions, pattern bindings, fn-arg identifiers.
        //    Variables resolve via resolution_map; bindings/args are wrapped
        //    as Var(node) so members_of_decl handles them uniformly.
        for node in lsp_helper::find_variables_by_name(file_ast, ident_name) {
            if let Some(decl) = self.ctx.resolution_map.get(&node.id()) {
                targets.push(decl.clone());
            } else {
                // binding pat or fn arg ident — type info lives on the node itself
                targets.push(Declaration::Var(node));
            }
        }

        targets
    }

    pub(crate) fn members_of_decl(&self, decl: &statics::Declaration) -> Vec<CompletionCandidate> {
        use statics::Declaration;
        use statics::typecheck::{Nominal, TypeKey};

        let mut candidates = vec![];
        match decl {
            Declaration::Namespace(ns, _) => return namespace_completions(ns),
            Declaration::Struct(s) => {
                self.add_member_function_completions(
                    &TypeKey::TyApp(Nominal::Struct(s.clone())),
                    &mut candidates,
                );
            }
            Declaration::Enum(e) => {
                for variant in &e.variants {
                    candidates.push(CompletionCandidate {
                        label: variant.ctor.v.clone(),
                        kind: CompletionCandidateKind::EnumVariant,
                    });
                }
                self.add_member_function_completions(
                    &TypeKey::TyApp(Nominal::Enum(e.clone())),
                    &mut candidates,
                );
            }
            Declaration::InterfaceDef(iface) => {
                for method in &iface.methods {
                    candidates.push(CompletionCandidate {
                        label: method.name.v.clone(),
                        kind: CompletionCandidateKind::Function,
                    });
                }
                for output_type in &iface.output_types {
                    candidates.push(CompletionCandidate {
                        label: output_type.name.v.clone(),
                        kind: CompletionCandidateKind::Type,
                    });
                }
            }
            Declaration::BuiltinType(bt) => {
                self.add_member_function_completions(&bt.to_type_key(), &mut candidates);
            }
            Declaration::Var(node) => {
                if let Some(solved) = self.ctx.solution_of_node(node.clone()) {
                    return self.type_completions(&solved);
                }
            }
            _ => {}
        }
        candidates.sort_by(|a, b| a.label.cmp(&b.label));
        candidates
    }

    pub(crate) fn type_completions(&self, solved_type: &statics::Type) -> Vec<CompletionCandidate> {
        use statics::typecheck::{Nominal, SolvedType, TypeKey};

        let mut candidates = vec![];
        match solved_type {
            SolvedType::Nominal(Nominal::Struct(struct_def), _) => {
                for field in &struct_def.fields {
                    candidates.push(CompletionCandidate {
                        label: field.name.v.clone(),
                        kind: CompletionCandidateKind::Field,
                    });
                }
                let type_key = TypeKey::TyApp(Nominal::Struct(struct_def.clone()));
                self.add_member_function_completions(&type_key, &mut candidates);
            }
            SolvedType::Nominal(Nominal::Enum(_enum_def), _) => {
                let type_key = TypeKey::TyApp(Nominal::Enum(_enum_def.clone()));
                self.add_member_function_completions(&type_key, &mut candidates);
            }
            SolvedType::Nominal(Nominal::Array, _) => {
                self.add_member_function_completions(
                    &TypeKey::TyApp(Nominal::Array),
                    &mut candidates,
                );
            }
            SolvedType::Int => {
                self.add_member_function_completions(&TypeKey::Int, &mut candidates);
            }
            SolvedType::Float => {
                self.add_member_function_completions(&TypeKey::Float, &mut candidates);
            }
            SolvedType::String => {
                self.add_member_function_completions(&TypeKey::String, &mut candidates);
            }
            _ => {}
        }
        candidates.sort_by(|a, b| a.label.cmp(&b.label));
        candidates
    }

    pub(crate) fn add_member_function_completions(
        &self,
        type_key: &statics::typecheck::TypeKey,
        candidates: &mut Vec<CompletionCandidate>,
    ) {
        for (tk, name) in self.ctx.member_functions.keys() {
            if tk == type_key {
                candidates.push(CompletionCandidate {
                    label: name.clone(),
                    kind: CompletionCandidateKind::Function,
                });
            }
        }
    }
}

pub(crate) fn namespace_completions(ns: &statics::Namespace) -> Vec<CompletionCandidate> {
    use crate::statics::Declaration;

    let mut candidates = vec![];
    for (name, decl) in &ns.declarations {
        let kind = match decl {
            Declaration::FreeFunction(_) | Declaration::MemberFunction(_) => {
                CompletionCandidateKind::Function
            }
            Declaration::EnumVariant { .. } => CompletionCandidateKind::EnumVariant,
            Declaration::Struct(_)
            | Declaration::Enum(_)
            | Declaration::BuiltinType(_)
            | Declaration::InterfaceDef(_) => CompletionCandidateKind::Type,
            _ => CompletionCandidateKind::Function,
        };
        candidates.push(CompletionCandidate {
            label: name.clone(),
            kind,
        });
    }
    candidates.sort_by(|a, b| a.label.cmp(&b.label));
    candidates
}

pub(crate) fn extract_primary_from_diagnostic(
    diagnostic: &codespan_reporting::diagnostic::Diagnostic<FileId>,
) -> (FileId, Range<usize>, String) {
    if let Some(label) = diagnostic.labels.first() {
        (
            label.file_id,
            label.range.clone(),
            diagnostic.message.clone(),
        )
    } else {
        (0, 0..0, diagnostic.message.clone())
    }
}

pub(crate) fn declaration_location(decl: &statics::Declaration) -> Option<DefinitionInfo> {
    use crate::statics::{Declaration, FuncResolutionKind};
    let node = match decl {
        Declaration::FreeFunction(FuncResolutionKind::Ordinary(func_def)) => func_def.name.node(),
        Declaration::FreeFunction(FuncResolutionKind::Host(func_decl)) => func_decl.name.node(),
        Declaration::FreeFunction(FuncResolutionKind::_Foreign { decl, .. }) => decl.name.node(),
        Declaration::MemberFunction(func_def) => func_def.name.node(),
        Declaration::InterfaceDef(iface) => iface.name.node(),
        Declaration::InterfaceMethod {
            iface,
            method_index,
        } => iface.methods[*method_index].name.node(),
        Declaration::InterfaceOutputType { ty, .. } => ty.name.node(),
        Declaration::Enum(e) => e.name.node(),
        Declaration::EnumVariant { e, variant } => e.variants[*variant].node(),
        Declaration::StructField { s, field } => s.fields[*field].name.node(),
        Declaration::Struct(s) => s.name.node(),
        Declaration::Var(node) => node.clone(),
        Declaration::Polytype(statics::PolytypeDeclaration::Ordinary(p)) => p.name.node(),
        Declaration::Namespace(_, node) => node.clone(),
        Declaration::Intrinsic(_) | Declaration::BuiltinType(_) => return None,
        Declaration::Polytype(
            statics::PolytypeDeclaration::InterfaceSelf(_)
            | statics::PolytypeDeclaration::ArrayArg
            | statics::PolytypeDeclaration::IntrinsicOperation(..),
        ) => return None,
    };
    let loc = node.location();
    Some(DefinitionInfo {
        file_id: loc.file_id,
        range: loc.range(),
    })
}

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
    for arg in &func_def.args {
        if arg.name.loc.contains_offset(offset) {
            return Some(arg.name.node());
        }
        if let Some(default) = &arg.default_val
            && let Some(node) = find_in_expr(default, offset)
        {
            return Some(node);
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
        ItemKind::TypeDef(TypeDefKind::Struct(s)) => {
            for field in &s.fields {
                if let Some(default) = &field.default_val
                    && let Some(node) = find_in_expr(default, offset)
                {
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
        ExprKind::FuncCall(func, args) => {
            if let Some(node) = find_in_expr(func, offset) {
                return Some(node);
            }
            for arg in args {
                if let Some(node) = find_in_expr(&arg.val, offset) {
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
            for arg in args {
                if arg.name.loc.contains_offset(offset) {
                    return Some(arg.name.node());
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
        ItemKind::TypeDef(typedef) => match typedef {
            TypeDefKind::Enum(e) => {
                if e.name.loc.contains_offset(offset) {
                    return Some(e.name.node());
                }
                for ty_arg in &e.ty_args {
                    if let Some(node) = find_ident_in_polytype(ty_arg, offset) {
                        return Some(node);
                    }
                }
                for variant in &e.variants {
                    if variant.ctor.loc.contains_offset(offset) {
                        return Some(variant.ctor.node());
                    }
                    if let Some(data) = &variant.data
                        && let Some(node) = find_ident_in_type(data, offset)
                    {
                        return Some(node);
                    }
                }
                None
            }
            TypeDefKind::Struct(s) => {
                if s.name.loc.contains_offset(offset) {
                    return Some(s.name.node());
                }
                for ty_arg in &s.ty_args {
                    if let Some(node) = find_ident_in_polytype(ty_arg, offset) {
                        return Some(node);
                    }
                }
                for field in &s.fields {
                    if field.name.loc.contains_offset(offset) {
                        return Some(field.name.node());
                    }
                    if let Some(node) = find_ident_in_type(&field.ty, offset) {
                        return Some(node);
                    }
                    if let Some(default) = &field.default_val
                        && let Some(node) = find_ident_in_expr(default, offset)
                    {
                        return Some(node);
                    }
                }
                None
            }
        },
        ItemKind::InterfaceDef(iface) => {
            if iface.name.loc.contains_offset(offset) {
                return Some(iface.name.node());
            }
            for method in &iface.methods {
                if method.name.loc.contains_offset(offset) {
                    return Some(method.name.node());
                }
                if let Some(node) =
                    find_ident_in_func_signature(&method.args, Some(&method.ret_type), offset)
                {
                    return Some(node);
                }
            }
            for output_type in &iface.output_types {
                if output_type.name.loc.contains_offset(offset) {
                    return Some(output_type.name.node());
                }
                for sub_iface in &output_type.interfaces {
                    if sub_iface.name.loc.contains_offset(offset) {
                        return Some(sub_iface.name.node());
                    }
                    for (arg_name, arg_val) in &sub_iface.arguments {
                        if arg_name.loc.contains_offset(offset) {
                            return Some(arg_name.node());
                        }
                        if let Some(node) = find_ident_in_type(arg_val, offset) {
                            return Some(node);
                        }
                    }
                }
            }
            None
        }
    }
}

fn find_ident_in_polytype(polyty: &Rc<crate::ast::Polytype>, offset: usize) -> Option<AstNode> {
    if polyty.name.loc.contains_offset(offset) {
        return Some(polyty.name.node());
    }
    for iface in &polyty.interfaces {
        if iface.name.loc.contains_offset(offset) {
            return Some(iface.name.node());
        }
        for (arg_name, arg_val) in &iface.arguments {
            if arg_name.loc.contains_offset(offset) {
                return Some(arg_name.node());
            }
            if let Some(node) = find_ident_in_type(arg_val, offset) {
                return Some(node);
            }
        }
    }
    None
}

fn find_ident_in_func_signature(
    args: &[ArgMaybeAnnotated],
    ret_type: Option<&Rc<Type>>,
    offset: usize,
) -> Option<AstNode> {
    for arg in args {
        if arg.name.loc.contains_offset(offset) {
            return Some(arg.name.node());
        }
        if let Some(ty) = &arg.ty
            && let Some(node) = find_ident_in_type(ty, offset)
        {
            return Some(node);
        }
        if let Some(default) = &arg.default_val
            && let Some(node) = find_ident_in_expr(default, offset)
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
            for iface in &poly.interfaces {
                if iface.name.loc.contains_offset(offset) {
                    return Some(iface.name.node());
                }
                for (arg_name, arg_val) in &iface.arguments {
                    if arg_name.loc.contains_offset(offset) {
                        return Some(arg_name.node());
                    }
                    if let Some(node) = find_ident_in_type(arg_val, offset) {
                        return Some(node);
                    }
                }
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
        StmtKind::Let(_, (pat, type_annot), expr) => {
            if let Some(node) = find_ident_in_pat(pat, offset) {
                return Some(node);
            }
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
        StmtKind::ForLoop(pat, iter, body) => {
            if let Some(node) = find_ident_in_pat(pat, offset) {
                return Some(node);
            }
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

fn find_ident_in_pat(pat: &Rc<Pat>, offset: usize) -> Option<AstNode> {
    if !pat.loc.contains_offset(offset) {
        return None;
    }
    match &*pat.kind {
        PatKind::Variant(prefixes, tag, data) => {
            for prefix in prefixes {
                if prefix.loc.contains_offset(offset) {
                    return Some(prefix.node());
                }
            }
            if tag.loc.contains_offset(offset) {
                return Some(tag.node());
            }
            if let Some(data) = data {
                return find_ident_in_pat(data, offset);
            }
            None
        }
        PatKind::Tuple(pats) => {
            for p in pats {
                if let Some(node) = find_ident_in_pat(p, offset) {
                    return Some(node);
                }
            }
            None
        }
        PatKind::Wildcard
        | PatKind::Binding(_)
        | PatKind::Void
        | PatKind::Int(_)
        | PatKind::Float(_)
        | PatKind::Bool(_)
        | PatKind::Str(_) => None,
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
        ExprKind::FuncCall(func, args) => {
            if let Some(node) = find_ident_in_expr(func, offset) {
                return Some(node);
            }
            for arg in args {
                if let Some(name) = &arg.name
                    && name.loc.contains_offset(offset)
                {
                    return Some(name.node());
                }
                if let Some(node) = find_ident_in_expr(&arg.val, offset) {
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
        ExprKind::MemberAccessLeadingDot(ident) => Some(ident.node()),
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
                    if let Some(node) = find_ident_in_pat(&arm.pat, offset) {
                        return Some(node);
                    }
                    return find_ident_in_stmt(&arm.stmt, offset);
                }
            }
            None
        }
        ExprKind::AnonymousFunction(args, ret_ty, body) => {
            if let Some(node) = find_ident_in_func_signature(args, ret_ty.as_ref(), offset) {
                return Some(node);
            }
            find_ident_in_expr(body, offset)
        }
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

/// Find all nodes that bear the given name and have associated type info — Variable
/// expressions (uses), function-arg identifiers, and `let`/`for` pattern bindings.
/// Used by completions to look up `x.<TAB>` even when `x` is only at its binding site.
pub(crate) fn find_variables_by_name(file_ast: &FileAst, name: &str) -> Vec<AstNode> {
    let mut results = vec![];
    for item in &file_ast.items {
        collect_vars_in_item(item, name, &mut results);
    }
    results
}

fn collect_vars_in_func_def(func_def: &Rc<FuncDef>, name: &str, out: &mut Vec<AstNode>) {
    for arg in &func_def.args {
        if arg.name.v == name {
            out.push(arg.name.node());
        }
        if let Some(default) = &arg.default_val {
            collect_vars_in_expr(default, name, out);
        }
    }
    collect_vars_in_expr(&func_def.body, name, out);
}

fn collect_vars_in_item(item: &Rc<Item>, name: &str, out: &mut Vec<AstNode>) {
    match &*item.kind {
        ItemKind::FuncDef(func_def) => collect_vars_in_func_def(func_def, name, out),
        ItemKind::Stmt(stmt) => collect_vars_in_stmt(stmt, name, out),
        ItemKind::InterfaceImpl(iface_impl) => {
            for method in &iface_impl.methods {
                collect_vars_in_func_def(method, name, out);
            }
        }
        ItemKind::Extension(ext) => {
            for method in &ext.methods {
                collect_vars_in_func_def(method, name, out);
            }
        }
        _ => {}
    }
}

fn collect_bindings_in_pat(pat: &Rc<Pat>, name: &str, out: &mut Vec<AstNode>) {
    match &*pat.kind {
        PatKind::Binding(n) if n == name => out.push(pat.node()),
        PatKind::Variant(_, _, Some(data)) => collect_bindings_in_pat(data, name, out),
        PatKind::Tuple(pats) => {
            for p in pats {
                collect_bindings_in_pat(p, name, out);
            }
        }
        _ => {}
    }
}

fn collect_vars_in_stmt(stmt: &Rc<Stmt>, name: &str, out: &mut Vec<AstNode>) {
    match &*stmt.kind {
        StmtKind::Let(_, (pat, _), expr) => {
            collect_bindings_in_pat(pat, name, out);
            collect_vars_in_expr(expr, name, out);
        }
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
        StmtKind::ForLoop(pat, iter, body) => {
            collect_bindings_in_pat(pat, name, out);
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
        ExprKind::FuncCall(func, args) => {
            collect_vars_in_expr(func, name, out);
            for arg in args {
                collect_vars_in_expr(&arg.val, name, out);
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
                collect_bindings_in_pat(&arm.pat, name, out);
                collect_vars_in_stmt(&arm.stmt, name, out);
            }
        }
        ExprKind::AnonymousFunction(args, _, body) => {
            for arg in args {
                if arg.name.v == name {
                    out.push(arg.name.node());
                }
                if let Some(default) = &arg.default_val {
                    collect_vars_in_expr(default, name, out);
                }
            }
            collect_vars_in_expr(body, name, out);
        }
        ExprKind::Array(elems) | ExprKind::Tuple(elems) => {
            for elem in elems {
                collect_vars_in_expr(elem, name, out);
            }
        }
        ExprKind::Unwrap(inner) | ExprKind::Try(inner) => collect_vars_in_expr(inner, name, out),
    }
}
