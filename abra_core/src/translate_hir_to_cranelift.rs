/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ast::{BinaryOperator, Location, NodeId};
use crate::hir;
use crate::parse::PrefixOp;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{self, AbiParam, InstBuilder, types};
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{Linkage, Module, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::HashMap;

pub(crate) fn translate(program: &hir::Program) -> Vec<u8> {
    let flags = settings::Flags::new(settings::builder());
    let isa = cranelift_native::builder()
        .expect("host architecture is not supported by Cranelift")
        .finish(flags)
        .unwrap();
    let builder = ObjectBuilder::new(isa, "abra", default_libcall_names()).unwrap();
    let mut module = ObjectModule::new(builder);

    let functions: Vec<_> = program
        .funcs
        .iter()
        .enumerate()
        .map(|(index, function)| {
            let signature = signature(&module, function);
            module
                .declare_function(&format!("abra_fn{index}"), Linkage::Local, &signature)
                .unwrap()
        })
        .collect();

    for (function, id) in program.funcs.iter().zip(&functions) {
        let mut context = module.make_context();
        context.func.signature = signature(&module, function);
        lower_function(function, &mut context.func, module.target_config());
        module.define_function(*id, &mut context).unwrap();
    }

    let entry = *functions
        .first()
        .expect("HIR program has no entry function");
    assert!(matches!(program.funcs[0].return_ty, hir::Type::Void));
    define_main(&mut module, entry);

    module.finish().emit().unwrap()
}

fn signature(module: &ObjectModule, function: &hir::Function) -> ir::Signature {
    let mut signature = module.make_signature();
    match &function.return_ty {
        hir::Type::Void | hir::Type::Never => {}
        ty => signature.returns.push(AbiParam::new(lower_type(ty))),
    }
    signature
}

fn lower_function(
    function: &hir::Function,
    output: &mut ir::Function,
    frontend_config: cranelift_codegen::isa::TargetFrontendConfig,
) {
    let mut context = FunctionBuilderContext::new();
    let mut lowerer = Lowerer {
        builder: FunctionBuilder::new(output, &mut context),
        binding_values: HashMap::new(),
        return_ty: function.return_ty.clone(),
    };
    let entry = lowerer.builder.create_block();
    lowerer.builder.switch_to_block(entry);
    lowerer.builder.seal_block(entry);

    if let Continues { value, .. } = lowerer.lower_expr(entry, &function.body) {
        let value = value_for_type(value, &lowerer.return_ty);
        let values: Vec<_> = value.into_iter().collect();
        lowerer
            .builder
            .set_srcloc(source_location(&function.body.span));
        lowerer.builder.ins().return_(&values);
    }

    lowerer.builder.seal_all_blocks();
    lowerer.builder.finalize(frontend_config);
}

struct Lowerer<'a> {
    builder: FunctionBuilder<'a>,
    binding_values: HashMap<NodeId, ir::Value>,
    return_ty: hir::Type,
}

enum Lowered {
    Continues {
        block: ir::Block,
        value: Option<ir::Value>,
    },
    Terminated,
}

use Lowered::{Continues, Terminated};

impl Lowerer<'_> {
    fn lower_expr(&mut self, block: ir::Block, expr: &hir::Expr) -> Lowered {
        self.builder.set_srcloc(source_location(&expr.span));
        match &expr.kind {
            hir::ExprKind::Variable(binding) => Continues {
                block,
                value: Some(
                    *self
                        .binding_values
                        .get(binding)
                        .expect("HIR binding has no Cranelift value"),
                ),
            },
            hir::ExprKind::Bool(value) => Continues {
                block,
                value: Some(self.builder.ins().iconst(types::I8, i64::from(*value))),
            },
            hir::ExprKind::Int(value) => Continues {
                block,
                value: Some(self.builder.ins().iconst(types::I64, *value)),
            },
            hir::ExprKind::Float(_) => unimplemented!(),
            hir::ExprKind::Block(statements) => self.lower_block(block, statements, &expr.ty),
            hir::ExprKind::IfElse(condition, then_branch, else_branch) => self.lower_if_else(
                block,
                condition,
                then_branch,
                else_branch.as_deref(),
                &expr.ty,
                &expr.span,
            ),
            hir::ExprKind::BinOp(left, op, right) => {
                if matches!(op, BinaryOperator::And | BinaryOperator::Or) {
                    self.lower_short_circuit(block, left, *op, right, &expr.span)
                } else {
                    self.lower_binary(block, left, *op, right, &expr.span)
                }
            }
            hir::ExprKind::Unop(op, operand) => self.lower_unary(block, op, operand, &expr.span),
            hir::ExprKind::String(_)
            | hir::ExprKind::Array(_)
            | hir::ExprKind::Tuple(_)
            | hir::ExprKind::FuncCall(_, _)
            | hir::ExprKind::IndexAccess(_, _) => unimplemented!(),
        }
    }

    fn lower_block(
        &mut self,
        block: ir::Block,
        statements: &[hir::Stmt],
        ty: &hir::Type,
    ) -> Lowered {
        let mut block = block;
        let mut value = None;
        for statement in statements {
            match self.lower_stmt(block, statement) {
                Continues {
                    block: next_block,
                    value: next_value,
                } => {
                    block = next_block;
                    value = next_value;
                }
                Terminated => return Terminated,
            }
        }
        Continues {
            block,
            value: value_for_type(value, ty),
        }
    }

    fn lower_stmt(&mut self, block: ir::Block, stmt: &hir::Stmt) -> Lowered {
        match &stmt.kind {
            hir::StmtKind::Expr(expr) => self.lower_expr(block, expr),
            hir::StmtKind::Let(pattern, expr) => {
                let Continues { block, value } = self.lower_expr(block, expr) else {
                    return Terminated;
                };
                let value = value.expect("let expression must produce a value");
                match &pattern.kind {
                    hir::PatKind::Wildcard => {}
                    hir::PatKind::Binding(binding) => {
                        self.binding_values.insert(*binding, value);
                    }
                    _ => unimplemented!(),
                }
                Continues { block, value: None }
            }
            hir::StmtKind::Return(expr) => {
                let lowered = match expr {
                    Some(expr) => self.lower_expr(block, expr),
                    None => Continues { block, value: None },
                };
                let Continues { value, .. } = lowered else {
                    return Terminated;
                };
                let value = value_for_type(value, &self.return_ty);
                let values: Vec<_> = value.into_iter().collect();
                self.builder.set_srcloc(source_location(&stmt.span));
                self.builder.ins().return_(&values);
                Terminated
            }
            hir::StmtKind::Var(_, _)
            | hir::StmtKind::Assign(_, _)
            | hir::StmtKind::Continue
            | hir::StmtKind::Break
            | hir::StmtKind::Loop => unimplemented!(),
        }
    }

    fn lower_if_else(
        &mut self,
        block: ir::Block,
        condition: &hir::Expr,
        then_stmt: &hir::Stmt,
        else_stmt: Option<&hir::Stmt>,
        ty: &hir::Type,
        span: &Location,
    ) -> Lowered {
        let Continues {
            block: _,
            value: condition,
        } = self.lower_expr(block, condition)
        else {
            return Terminated;
        };
        let condition = condition.expect("condition must produce a value");
        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.set_srcloc(source_location(span));
        self.builder
            .ins()
            .brif(condition, then_block, &[], else_block, &[]);

        self.builder.switch_to_block(then_block);
        let then_path = self.lower_stmt(then_block, then_stmt);
        let then_continues = self.jump_to_merge(then_path, merge_block, ty, span);

        self.builder.switch_to_block(else_block);
        let else_path = match else_stmt {
            Some(stmt) => self.lower_stmt(else_block, stmt),
            None => Continues {
                block: else_block,
                value: None,
            },
        };
        let else_continues = self.jump_to_merge(else_path, merge_block, ty, span);

        if then_continues || else_continues {
            let result = (!matches!(ty, hir::Type::Void))
                .then(|| self.builder.append_block_param(merge_block, lower_type(ty)));
            self.builder.switch_to_block(merge_block);
            Continues {
                block: merge_block,
                value: result,
            }
        } else {
            Terminated
        }
    }

    fn lower_short_circuit(
        &mut self,
        block: ir::Block,
        left: &hir::Expr,
        op: BinaryOperator,
        right: &hir::Expr,
        span: &Location,
    ) -> Lowered {
        let Continues {
            block: _,
            value: left,
        } = self.lower_expr(block, left)
        else {
            return Terminated;
        };
        let left = left.expect("operator must produce a value");
        let right_block = self.builder.create_block();
        let short_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        let result = self.builder.append_block_param(merge_block, types::I8);
        let (then_block, else_block, short_value) = match op {
            BinaryOperator::And => (right_block, short_block, false),
            BinaryOperator::Or => (short_block, right_block, true),
            _ => unreachable!(),
        };
        self.builder.set_srcloc(source_location(span));
        self.builder
            .ins()
            .brif(left, then_block, &[], else_block, &[]);

        self.builder.switch_to_block(right_block);
        let right_path = self.lower_expr(right_block, right);
        self.jump_to_merge(right_path, merge_block, &hir::Type::Bool, span);

        self.builder.switch_to_block(short_block);
        self.builder.set_srcloc(source_location(span));
        let short_value = self.builder.ins().iconst(types::I8, i64::from(short_value));
        self.builder.ins().jump(merge_block, &[short_value.into()]);

        self.builder.switch_to_block(merge_block);
        Continues {
            block: merge_block,
            value: Some(result),
        }
    }

    fn jump_to_merge(
        &mut self,
        path: Lowered,
        merge_block: ir::Block,
        ty: &hir::Type,
        span: &Location,
    ) -> bool {
        let Continues { value, .. } = path else {
            return false;
        };
        let value = value_for_type(value, ty);
        let arguments: Vec<ir::BlockArg> = value.into_iter().map(Into::into).collect();
        self.builder.set_srcloc(source_location(span));
        self.builder.ins().jump(merge_block, &arguments);
        true
    }

    fn lower_binary(
        &mut self,
        block: ir::Block,
        left: &hir::Expr,
        op: BinaryOperator,
        right: &hir::Expr,
        span: &Location,
    ) -> Lowered {
        let Continues {
            block,
            value: left_value,
        } = self.lower_expr(block, left)
        else {
            return Terminated;
        };
        let left_value = left_value.expect("operator must produce a value");
        let Continues {
            block,
            value: right_value,
        } = self.lower_expr(block, right)
        else {
            return Terminated;
        };
        let right_value = right_value.expect("operator must produce a value");
        self.builder.set_srcloc(source_location(span));
        let value = lower_binary(&mut self.builder, op, &left.ty, left_value, right_value);
        Continues {
            block,
            value: Some(value),
        }
    }

    fn lower_unary(
        &mut self,
        block: ir::Block,
        op: &PrefixOp,
        operand: &hir::Expr,
        span: &Location,
    ) -> Lowered {
        let Continues {
            block,
            value: operand_value,
        } = self.lower_expr(block, operand)
        else {
            return Terminated;
        };
        let operand_value = operand_value.expect("operator must produce a value");
        self.builder.set_srcloc(source_location(span));
        let value = match (op, &operand.ty) {
            (PrefixOp::Not, hir::Type::Bool) => {
                self.builder
                    .ins()
                    .icmp_imm_s(IntCC::Equal, operand_value, 0)
            }
            (PrefixOp::Minus, hir::Type::Int) => self.builder.ins().ineg(operand_value),
            (PrefixOp::Minus, hir::Type::Float) => unimplemented!(),
            _ => unreachable!("operator must be valid for its operand type"),
        };
        Continues {
            block,
            value: Some(value),
        }
    }
}

fn source_location(location: &Location) -> ir::SourceLoc {
    ir::SourceLoc::new(u32::try_from(location.lo).expect("source file is too large"))
}

fn value_for_type(value: Option<ir::Value>, ty: &hir::Type) -> Option<ir::Value> {
    if matches!(ty, hir::Type::Void) {
        None
    } else {
        Some(value.unwrap_or_else(|| panic!("expected a value of type {ty:?}")))
    }
}

fn lower_binary(
    builder: &mut FunctionBuilder,
    op: BinaryOperator,
    ty: &hir::Type,
    left: ir::Value,
    right: ir::Value,
) -> ir::Value {
    use BinaryOperator::*;

    match (op, ty) {
        (Add, hir::Type::Int) => builder.ins().iadd(left, right),
        (Subtract, hir::Type::Int) => builder.ins().isub(left, right),
        (Multiply, hir::Type::Int) => builder.ins().imul(left, right),
        (Divide, hir::Type::Int) => builder.ins().sdiv(left, right),
        (Mod, hir::Type::Int) => builder.ins().srem(left, right),
        (Pow, hir::Type::Int) => unimplemented!(),
        (Add | Subtract | Multiply | Divide | Pow, hir::Type::Float) => unimplemented!(),
        (Equal, hir::Type::Int | hir::Type::Bool) => builder.ins().icmp(IntCC::Equal, left, right),
        (NotEqual, hir::Type::Int | hir::Type::Bool) => {
            builder.ins().icmp(IntCC::NotEqual, left, right)
        }
        (LessThan, hir::Type::Int) => builder.ins().icmp(IntCC::SignedLessThan, left, right),
        (LessThanOrEqual, hir::Type::Int) => {
            builder
                .ins()
                .icmp(IntCC::SignedLessThanOrEqual, left, right)
        }
        (GreaterThan, hir::Type::Int) => builder.ins().icmp(IntCC::SignedGreaterThan, left, right),
        (GreaterThanOrEqual, hir::Type::Int) => {
            builder
                .ins()
                .icmp(IntCC::SignedGreaterThanOrEqual, left, right)
        }
        (
            Equal | NotEqual | LessThan | LessThanOrEqual | GreaterThan | GreaterThanOrEqual,
            hir::Type::Float,
        ) => unimplemented!(),
        _ => unimplemented!(),
    }
}

fn lower_type(ty: &hir::Type) -> ir::Type {
    match ty {
        hir::Type::Bool => types::I8,
        hir::Type::Int => types::I64,
        hir::Type::Float => types::F64,
        hir::Type::Void | hir::Type::Never => panic!("{ty:?} has no Cranelift value type"),
        _ => unimplemented!(),
    }
}

fn define_main(module: &mut ObjectModule, entry: cranelift_module::FuncId) {
    let frontend_config = module.target_config();
    let mut signature = module.make_signature();
    signature.returns.push(AbiParam::new(types::I32));
    let main = module
        .declare_function("main", Linkage::Export, &signature)
        .unwrap();
    let mut context = module.make_context();
    context.func.signature = signature;
    let entry = module.declare_func_in_func(entry, &mut context.func);
    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut context.func, &mut builder_context);
    let block = builder.create_block();
    builder.switch_to_block(block);
    builder.seal_block(block);
    builder.ins().call(entry, &[]);
    let status = builder.ins().iconst(types::I32, 0);
    builder.ins().return_(&[status]);
    builder.finalize(frontend_config);
    module.define_function(main, &mut context).unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span(lo: usize) -> Location {
        Location {
            file_id: 0,
            lo,
            hi: lo + 1,
        }
    }

    fn return_statement(lo: usize) -> hir::Stmt {
        hir::Stmt {
            kind: hir::StmtKind::Return(None),
            span: span(lo),
        }
    }

    #[test]
    fn lowers_if_with_two_terminating_branches() {
        let program = hir::Program {
            funcs: vec![hir::Function {
                return_ty: hir::Type::Void,
                body: hir::Expr {
                    ty: hir::Type::Never,
                    kind: hir::ExprKind::IfElse(
                        Box::new(hir::Expr {
                            ty: hir::Type::Bool,
                            kind: hir::ExprKind::Bool(true),
                            span: span(0),
                        }),
                        Box::new(return_statement(1)),
                        Some(Box::new(return_statement(2))),
                    ),
                    span: span(0),
                },
            }],
        };

        assert!(!translate(&program).is_empty());
    }
}
