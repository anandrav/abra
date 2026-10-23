use crate::intrinsic::IntrinsicOperation;
use crate::mir;
use crate::mir::{Expr, ExprKind, Function, Stmt, StmtKind};
use crate::statics::typecheck::Monotype;
use cranelift::codegen::ir;
use cranelift::codegen::isa::TargetFrontendConfig;
use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::env::temp_dir;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};
use std::{fs, process};

pub struct LoweringContext {
    module: ObjectModule,
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

    let mut ctx = LoweringContext { module };

    ctx.lower_program(&program);

    // TODO: make this shim actually call the main function instead of just returning 0
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
        let status = builder.ins().iconst(types::I32, 0);
        builder.ins().return_(&[status]);
        builder.finalize(config);
        ctx.module.define_function(main, &mut context).unwrap();
    }

    let object_contents = ctx.module.finish().emit().unwrap();
    let object_path = temp_dir().join(format!(
        "abra-object-{}-{}.o",
        process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    fs::write(&object_path, object_contents).unwrap();

    // link
    // TODO: Compile and link the runtime.
    Command::new("cc")
        .arg(&object_path)
        .arg("-o")
        .arg(output_path)
        .status()
        .unwrap();
    fs::remove_file(object_path).unwrap()
}

impl LoweringContext {
    fn lower_program(&mut self, program: &mir::Program) {
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
                    ();
                    None
                }
                _ => unimplemented!("{:#?}", expr.kind),
            },
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
