use crate::mir;
use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::{fs::File, io::Write};

pub(crate) fn lower(program: mir::Program) {
    // TODO: lower mir to cranelift blocks

    generate_object_file();

    // TODO: then link to runtime and generate binary?

    unimplemented!()
}

fn generate_object_file() {
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
        let translation_unit_name = b"output_a_binary";
        let libcall_names = cranelift_module::default_libcall_names();
        let builder =
            ObjectBuilder::new(isa.clone(), translation_unit_name, libcall_names).unwrap();
        ObjectModule::new(builder)
    };
}
