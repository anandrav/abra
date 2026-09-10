use crate::mir;
use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::env::temp_dir;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};
use std::{fs, process};

pub(crate) fn lower(_program: mir::Program, output_path: &PathBuf) {
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

    // TODO: make this shim actually call the main function instead of just returning 0
    // main function shim
    {
        let config = module.target_config();
        let mut signature = module.make_signature();
        signature.returns.push(AbiParam::new(types::I32));
        let main = module
            .declare_function("main", Linkage::Export, &signature)
            .unwrap();
        let mut context = module.make_context();
        context.func.signature = signature;
        let mut builder_context = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut builder_context);
        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.seal_block(block);
        let status = builder.ins().iconst(types::I32, 0);
        builder.ins().return_(&[status]);
        builder.finalize(config);
        module.define_function(main, &mut context).unwrap();
    }

    let object_contents = module.finish().emit().unwrap();
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
