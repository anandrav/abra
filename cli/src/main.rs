extern crate abra_core;

use abra_core::effects::FromRepr;
use abra_core::effects::Type;
use abra_core::effects::VariantArray;
use abra_core::effects::{self, EffectTrait};
use abra_core::SourceFile;
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

    let effects = CliEffects::enumerate();
    match abra_core::compile_bytecode(source_files, effects) {
        Ok(program) => {
            let mut vm = abra_core::vm::Vm::new(program);
            loop {
                if vm.is_done() {
                    return;
                }
                vm.run();
                vm.gc();
                if let Some(pending_effect) = vm.get_pending_effect() {
                    let effect = CliEffects::from_repr(pending_effect as usize).unwrap();
                    match effect {
                        CliEffects::PrintString => {
                            let s = vm.top().get_string(&vm);
                            print!("{}", s);
                            vm.pop();
                            vm.push_nil();
                        }
                        CliEffects::Read => {
                            let mut input = String::new();
                            std::io::stdin().read_line(&mut input).unwrap();
                            vm.push_str(&input[0..input.len() - 1]);
                        }
                        CliEffects::LoadLib => {
                            todo!();
                        }
                    }
                    vm.clear_pending_effect();
                }
            }
        }
        Err(err) => {
            eprintln!("{}", err);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, VariantArray, FromRepr)]
pub enum CliEffects {
    PrintString,
    Read,
    LoadLib,
}

impl EffectTrait for CliEffects {
    fn type_signature(&self) -> (Vec<Type>, Type) {
        match self {
            // print_string: string -> void
            CliEffects::PrintString => (vec![Type::String], Type::Unit),
            // readline: void -> string
            CliEffects::Read => (vec![], Type::String),
            // loadlib: string -> int
            CliEffects::LoadLib => (vec![Type::String], Type::Int),
        }
    }

    fn function_name(&self) -> &'static str {
        match self {
            CliEffects::PrintString => "print_string",
            CliEffects::Read => "readline",
            CliEffects::LoadLib => "loadlib",
        }
    }
}
