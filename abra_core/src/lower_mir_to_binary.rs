use crate::ast::{AstNode, BinaryOperator};
use crate::intrinsic::IntrinsicOperation;
use crate::mir;
use crate::mir::{Expr, ExprKind, Function, MirContext, PatKind, Stmt, StmtKind};
use crate::statics::Declaration;
use crate::statics::typecheck::Monotype;
use cranelift::codegen::ir;
use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use utils::hash::HashMap;
use utils::tempfile::TempFile;

// General bookkeeping when lowering the entire program
pub struct LoweringContext {
    mir_context: MirContext,

    module: ObjectModule,

    exit_id: FuncId,
}

// Used when lowering a single function
pub struct FunctionContext<'a> {
    builder: FunctionBuilder<'a>,

    variables: HashMap<AstNode, Variable>,
}

impl<'a> FunctionContext<'a> {
    fn new(builder: FunctionBuilder<'a>) -> Self {
        Self {
            builder,
            variables: Default::default(),
        }
    }
}

pub(crate) fn lower(program: mir::Program, mir_context: MirContext, output_path: &PathBuf) {
    let isa = {
        let mut builder = settings::builder();

        // disable optimizations so disassembly will more directly correlated to our Cranelift usage
        builder.set("opt_level", "none").unwrap();

        builder.enable("is_pic").unwrap();

        let flags = settings::Flags::new(builder);

        isa::lookup(target_lexicon::HOST)
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

    let mut ctx = LoweringContext {
        mir_context,
        module,
        exit_id,
    };

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
        let mut cranelift_function_context = ctx.module.make_context();
        cranelift_function_context.func.signature = signature;
        let mut cranelift_function_builder_context = FunctionBuilderContext::new();
        let mut cranelift_function_builder = FunctionBuilder::new(
            &mut cranelift_function_context.func,
            &mut cranelift_function_builder_context,
        );
        let block = cranelift_function_builder.create_block();
        cranelift_function_builder.switch_to_block(block);
        cranelift_function_builder.seal_block(block);
        let callee = ctx
            .module
            .declare_func_in_func(abra_main, cranelift_function_builder.func);
        cranelift_function_builder.ins().call(callee, &[]);
        let status = cranelift_function_builder.ins().iconst(types::I32, 0);
        cranelift_function_builder.ins().return_(&[status]);
        cranelift_function_builder.finalize(config);
        ctx.module
            .define_function(main, &mut cranelift_function_context)
            .unwrap();
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

        let mut function_context = FunctionContext::new(builder);
        self.lower_expr(&func.body, &mut function_context);
        function_context.builder.ins().return_(&[]); // TODO: return value(s)

        function_context.builder.seal_block(block);
        function_context.builder.finalize(config);
    }

    fn lower_expr(&mut self, expr: &Expr, func: &mut FunctionContext) -> Option<Value> {
        match &expr.kind {
            ExprKind::Int(n) => Some(func.builder.ins().iconst(types::I64, *n)),
            ExprKind::Block(stmts) => {
                if stmts.is_empty() {
                    return None;
                }
                for stmt in &stmts[..stmts.len() - 1] {
                    self.lower_stmt(stmt, func);
                }
                self.lower_stmt(stmts.last().unwrap(), func)
            }
            ExprKind::Intrinsic(op, args) => match op {
                IntrinsicOperation::Exit => {
                    let arg = self.lower_expr(&args[0], func).unwrap();
                    let converted_arg = func.builder.ins().ireduce(types::I32, arg);
                    let exit_ref = self
                        .module
                        .declare_func_in_func(self.exit_id, func.builder.func); // TODO: don't create a ref every time exit is lowered, there should be one per function
                    func.builder.ins().call(exit_ref, &[converted_arg]);
                    None
                }
                _ => unimplemented!("{:#?}", expr.kind),
            },
            ExprKind::BinOp(left, op, right) => {
                let left = self.lower_expr(left, func).unwrap();
                let right = self.lower_expr(right, func).unwrap();
                match op {
                    BinaryOperator::Add => Some(func.builder.ins().iadd(left, right)),
                    _ => unimplemented!("{:#?}", op),
                }
            }
            // TODO: String contents aren't needed
            ExprKind::Variable(_) => {
                let node = self.mir_context.resolution_map[&expr.id].clone();
                let variable = func.variables[&node];
                Some(func.builder.use_var(variable))
            }
            _ => unimplemented!("{:#?}", expr.kind),
        }
    }

    fn lower_stmt(&mut self, stmt: &Stmt, func: &mut FunctionContext) -> Option<Value> {
        match &stmt.kind {
            StmtKind::Expr(e) => self.lower_expr(e, func),
            StmtKind::Let(pat, expr) => match &pat.kind {
                PatKind::Binding(_s) => {
                    let value = self.lower_expr(expr, func).unwrap();
                    let node = self.mir_context.resolution_map[&pat.id].clone();
                    let ty = func.builder.func.dfg.value_type(value);
                    let variable = func.builder.declare_var(ty);
                    func.builder.def_var(variable, value);
                    func.variables.insert(node, variable);
                    None
                }
                _ => unimplemented!("{:#?}", pat.kind),
            },
            StmtKind::Assign(lhs, rhs) => match &lhs.kind {
                ExprKind::Variable(_) => {
                    let value = self.lower_expr(rhs, func).unwrap();
                    let node = self.mir_context.resolution_map[&lhs.id].clone();
                    let variable = func.variables[&node];
                    func.builder.def_var(variable, value);
                    None
                }
                _ => unimplemented!("{:#?}", lhs.kind),
            },
            _ => unimplemented!("{:#?}", stmt.kind),
        }
    }
}
