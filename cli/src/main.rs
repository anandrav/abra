extern crate abra_core;

use abra_core::{vm::Vm, Effect, SourceFile, Type};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// file to run
    #[arg()]
    file: String,
}

fn main() {
    let args = Args::parse();

    let mut source_files = Vec::new();
    source_files.push(SourceFile {
        name: "prelude.abra".to_string(),
        contents: abra_core::prelude::_PRELUDE.to_string(),
    });

    let Ok(contents) = std::fs::read_to_string(&args.file) else {
        eprintln!("file '{}' not found", args.file);
        std::process::exit(1);
    };
    source_files.push(SourceFile {
        name: args.file,
        contents,
    });

    let effects = vec![
        Effect {
            name: "print_string",
            type_signature: (vec![Type::String], Type::Unit),
            func: |vm: &mut Vm| {
                let s = vm.top().get_string(vm);
                print!("{}", s);
                vm.pop();
                vm.push_nil();
            },
        },
        Effect {
            name: "readline",
            type_signature: (vec![], Type::String),
            func: |vm: &mut Vm| {
                let mut input = String::new();
                std::io::stdin().read_line(&mut input).unwrap();
                vm.push_str(&input[0..input.len() - 1]);
            },
        },
    ];

    match abra_core::compile_bytecode(source_files, effects.clone()) {
        Ok(program) => {
            let mut vm = abra_core::vm::Vm::new(program);
            loop {
                if vm.is_done() {
                    return;
                }
                vm.run();
                vm.gc();
                if let Some(pending_effect) = vm.get_pending_effect() {
                    let effect = effects[pending_effect as usize].clone();
                    (effect.func)(&mut vm);
                    vm.clear_pending_effect();
                }
            }
        }
        Err(err) => {
            eprintln!("{}", err);
        }
    }
}
