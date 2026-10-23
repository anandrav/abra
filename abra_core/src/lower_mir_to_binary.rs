use crate::ast::BinaryOperator;
use crate::intrinsic::IntrinsicOperation;
use crate::mir;
use crate::mir::{Expr, ExprKind, Function, Stmt, StmtKind};
use crate::statics::typecheck::Monotype;
use cranelift::codegen::ir;
use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use utils::tempfile::TempFile;

pub struct LoweringContext {
    module: ObjectModule,

    exit_id: FuncId,
}

pub(crate) fn lower(program: mir::Program, output_path: &PathBuf) {
    let isa = {
        let mut builder = settings::builder();

        // disable optimizations so disassembly will more directly correlated to our Cranelift usage
        builder.set("opt_level", "none").unwrap();

        builder.enable("is_pic").unwrap();

        let flags = settings::Flags::new(builder);

        let TARGET_TRIPLE = "aarch64-apple-darwin"; // TODO: don't hardcode this

        isa::lookup_by_name(TARGET_TRIPLE)
            .unwrap()
            .finish(flags)
            .unwrap()
    };

    let mut module = {
        let translation_unit_name = b"output_a_binary"; // TODO: use a name derived from the program's mainfile name
        let libcall_names = cranelift_module::default_libcall_names();
        let builder =
            ObjectBuilder::new(isa.clone(), translation_unit_name, libcall_names).unwrap();
        ObjectModule::new(builder)
    };

    let exit_id = {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I32));

        module
            .declare_function("exit", Linkage::Import, &sig)
            .unwrap()
    };

    let mut ctx = LoweringContext { module, exit_id };

    let abra_main = ctx.lower_program(&program);

    // main function shim
    {
        let config = ctx.module.target_config();
        let mut signature = ctx.module.make_signature();
        signature.returns.push(AbiParam::new(types::I32));
        let main = ctx
            .module
            .declare_function("main", Linkage::Export, &signature)
            .unwrap();
        let mut context = ctx.module.make_context();
        context.func.signature = signature;
        let mut builder_context = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut builder_context);
        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.seal_block(block);
        let callee = ctx.module.declare_func_in_func(abra_main, builder.func);
        builder.ins().call(callee, &[]);
        let status = builder.ins().iconst(types::I32, 0);
        builder.ins().return_(&[status]);
        builder.finalize(config);
        ctx.module.define_function(main, &mut context).unwrap();
    }

    let object_contents = ctx.module.finish().emit().unwrap();
    let object = TempFile::new();
    fs::write(&object.path, object_contents).unwrap();

    // link
    // TODO: Compile and link the runtime.
    Command::new("cc")
        .arg(&object.path)
        .arg("-o")
        .arg(output_path)
        .status()
        .unwrap();
}

impl LoweringContext {
    fn lower_program(&mut self, program: &mir::Program) -> FuncId {
        let mut function_signatures: Vec<Signature> = vec![];
        let mut function_declarations: Vec<FuncId> = vec![];
        for func in program.funcs.iter() {
            let sig = self.module.make_signature();
            match &func.ret_ty {
                Monotype::Void => {}
                _ => unimplemented!(),
            }
            function_signatures.push(sig);
            let func_id = self
                .module
                .declare_function(
                    &func.fully_qualified_name,
                    Linkage::Local,
                    function_signatures.last().unwrap(),
                )
                .unwrap(); // TODO: don't unwrap
            function_declarations.push(func_id);
        }

        for (index, func) in program.funcs.iter().enumerate() {
            let mut context = self.module.make_context();
            context.func.signature = function_signatures[index].clone();

            self.lower_function(func, &mut context.func);

            let declaration = function_declarations[index];
            self.module
                .define_function(declaration, &mut context)
                .unwrap(); // TODO: don't unwrap
        }

        function_declarations[0]
    }

    fn lower_function(&mut self, func: &Function, ir: &mut ir::Function) {
        let config = self.module.target_config();
        let mut builder_context = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(ir, &mut builder_context);

        let block = builder.create_block();
        builder.switch_to_block(block);

        self.lower_expr(&func.body, &mut builder);
        builder.ins().return_(&[]);

        builder.seal_block(block);
        builder.finalize(config);
    }

    fn lower_expr(&mut self, expr: &Expr, fn_builder: &mut FunctionBuilder) -> Option<Value> {
        match &expr.kind {
            ExprKind::Int(n) => Some(fn_builder.ins().iconst(types::I64, *n)),
            ExprKind::Block(stmts) => {
                if stmts.is_empty() {
                    return None;
                }
                for stmt in &stmts[..stmts.len() - 1] {
                    self.lower_stmt(stmt, fn_builder);
                }
                self.lower_stmt(stmts.last().unwrap(), fn_builder)
            }
            ExprKind::Intrinsic(op, args) => match op {
                IntrinsicOperation::Exit => {
                    let arg = self.lower_expr(&args[0], fn_builder).unwrap();
                    let converted_arg = fn_builder.ins().ireduce(types::I32, arg);
                    let exit_ref = self
                        .module
                        .declare_func_in_func(self.exit_id, fn_builder.func); // TODO: don't create a ref every time exit is lowered, there should be one per function
                    fn_builder.ins().call(exit_ref, &[converted_arg]);
                    None
                }
                _ => unimplemented!("{:#?}", expr.kind),
            },
            ExprKind::BinOp(left, op, right) => {
                let left = self.lower_expr(left, fn_builder).unwrap();
                let right = self.lower_expr(right, fn_builder).unwrap();
                match op {
                    BinaryOperator::Add => Some(fn_builder.ins().iadd(left, right)),
                    _ => unimplemented!("{:#?}", op),
                }
            }
            _ => unimplemented!("{:#?}", expr.kind),
        }
    }

    fn lower_stmt(&mut self, stmt: &Stmt, fn_builder: &mut FunctionBuilder) -> Option<Value> {
        match &stmt.kind {
            StmtKind::Expr(e) => self.lower_expr(e, fn_builder),
            _ => unimplemented!("{:#?}", stmt.kind),
        }
    }
}
