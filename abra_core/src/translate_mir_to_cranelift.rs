/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::mir;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{self, AbiParam, InstBuilder, types};
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder as CraneliftFunctionBuilder, FunctionBuilderContext};
use cranelift_module::{Linkage, Module, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::HashMap;

pub(crate) fn translate(program: &mir::Program) -> Vec<u8> {
    let flags = settings::Flags::new(settings::builder());
    let isa = cranelift_native::builder()
        .expect("host architecture is not supported by Cranelift")
        .finish(flags)
        .unwrap();
    let builder = ObjectBuilder::new(isa, "abra", default_libcall_names()).unwrap();
    let mut module = ObjectModule::new(builder);
    let mut functions = HashMap::new();

    for function in program.functions() {
        let signature = signature(&module, program.function(function));
        let id = module
            .declare_function(&format!("abra_{function}"), Linkage::Local, &signature)
            .unwrap();
        functions.insert(function, id);
    }

    for function in program.functions() {
        let mut context = module.make_context();
        context.func.signature = signature(&module, program.function(function));
        lower_function(
            program.function(function),
            &mut context.func,
            module.target_config(),
        );
        module
            .define_function(functions[&function], &mut context)
            .unwrap();
    }

    let entry = program
        .functions()
        .next()
        .expect("MIR program has no entry function");
    assert_eq!(program.function(entry).return_type(), &mir::Ty::Void);
    define_main(&mut module, functions[&entry]);

    module.finish().emit().unwrap()
}

fn signature(module: &ObjectModule, function: &mir::Function) -> ir::Signature {
    let mut signature = module.make_signature();
    match function.return_type() {
        mir::Ty::Void | mir::Ty::Never => {}
        ty => signature.returns.push(AbiParam::new(lower_type(ty))),
    }
    signature
}

fn lower_function(
    function: &mir::Function,
    output: &mut ir::Function,
    frontend_config: cranelift_codegen::isa::TargetFrontendConfig,
) {
    let mut context = FunctionBuilderContext::new();
    let mut builder = CraneliftFunctionBuilder::new(output, &mut context);
    let mut blocks = HashMap::new();
    let mut values = HashMap::new();

    for block in function.blocks() {
        blocks.insert(block, builder.create_block());
    }

    for block in function.blocks() {
        let cranelift_block = blocks[&block];
        for parameter in function.block(block).params() {
            let value = builder
                .append_block_param(cranelift_block, lower_type(function.value_type(*parameter)));
            values.insert(*parameter, value);
        }
    }

    for block in function.blocks() {
        builder.switch_to_block(blocks[&block]);

        for instruction in function.instructions(block) {
            let instruction = function.inst(instruction);
            let value = lower_inst(&mut builder, instruction.kind(), &values);
            values.insert(instruction.result(), value);
        }

        let terminator = function
            .block(block)
            .terminator()
            .expect("MIR block has no terminator");
        match terminator.kind() {
            mir::TerminatorKind::Jump {
                destination,
                arguments,
            } => {
                let arguments: Vec<ir::BlockArg> =
                    arguments.iter().map(|value| values[value].into()).collect();
                builder.ins().jump(blocks[destination], &arguments);
            }
            mir::TerminatorKind::Branch {
                condition,
                then_block,
                else_block,
            } => {
                builder.ins().brif(
                    values[condition],
                    blocks[then_block],
                    &[],
                    blocks[else_block],
                    &[],
                );
            }
            mir::TerminatorKind::Return(value) => {
                let values: Vec<_> = value.iter().map(|value| values[value]).collect();
                builder.ins().return_(&values);
            }
        }
    }

    builder.seal_all_blocks();
    builder.finalize(frontend_config);
}

fn lower_inst(
    builder: &mut CraneliftFunctionBuilder,
    instruction: &mir::InstKind,
    values: &HashMap<mir::Value, ir::Value>,
) -> ir::Value {
    match instruction {
        mir::InstKind::BoolConst(value) => builder.ins().iconst(types::I8, i64::from(*value)),
        mir::InstKind::IntConst(value) => builder.ins().iconst(types::I64, *value),
        mir::InstKind::FloatConst(_) => unimplemented!(),
        mir::InstKind::Unary { op, operand } => match op {
            mir::UnaryOp::BoolNot => builder.ins().icmp_imm_s(IntCC::Equal, values[operand], 0),
            mir::UnaryOp::IntNeg => builder.ins().ineg(values[operand]),
            mir::UnaryOp::FloatNeg => unimplemented!(),
        },
        mir::InstKind::Binary { op, left, right } => {
            lower_binary(builder, *op, values[left], values[right])
        }
    }
}

fn lower_binary(
    builder: &mut CraneliftFunctionBuilder,
    op: mir::BinaryOp,
    left: ir::Value,
    right: ir::Value,
) -> ir::Value {
    use mir::BinaryOp::*;

    match op {
        IntAdd => builder.ins().iadd(left, right),
        IntSubtract => builder.ins().isub(left, right),
        IntMultiply => builder.ins().imul(left, right),
        IntDivide => builder.ins().sdiv(left, right),
        IntModulo => builder.ins().srem(left, right),
        IntPow => unimplemented!(),
        IntEqual => builder.ins().icmp(IntCC::Equal, left, right),
        IntNotEqual => builder.ins().icmp(IntCC::NotEqual, left, right),
        IntLessThan => builder.ins().icmp(IntCC::SignedLessThan, left, right),
        IntLessThanOrEqual => builder
            .ins()
            .icmp(IntCC::SignedLessThanOrEqual, left, right),
        IntGreaterThan => builder.ins().icmp(IntCC::SignedGreaterThan, left, right),
        IntGreaterThanOrEqual => builder
            .ins()
            .icmp(IntCC::SignedGreaterThanOrEqual, left, right),
        BoolEqual => builder.ins().icmp(IntCC::Equal, left, right),
        BoolNotEqual => builder.ins().icmp(IntCC::NotEqual, left, right),
        FloatAdd
        | FloatSubtract
        | FloatMultiply
        | FloatDivide
        | FloatPow
        | FloatEqual
        | FloatNotEqual
        | FloatLessThan
        | FloatLessThanOrEqual
        | FloatGreaterThan
        | FloatGreaterThanOrEqual => unimplemented!(),
    }
}

fn lower_type(ty: &mir::Ty) -> ir::Type {
    match ty {
        mir::Ty::Bool => types::I8,
        mir::Ty::Int => types::I64,
        mir::Ty::Float => types::F64,
        mir::Ty::Void | mir::Ty::Never => panic!("{ty} has no Cranelift value type"),
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
    let mut builder = CraneliftFunctionBuilder::new(&mut context.func, &mut builder_context);
    let block = builder.create_block();
    builder.switch_to_block(block);
    builder.ins().call(entry, &[]);
    let status = builder.ins().iconst(types::I32, 0);
    builder.ins().return_(&[status]);
    builder.seal_all_blocks();
    builder.finalize(frontend_config);
    module.define_function(main, &mut context).unwrap();
}
