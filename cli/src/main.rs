extern crate abra_core;

use abra_core::effects::{self, DefaultEffects, EffectTrait};
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
        return;
    };
    source_files.push(SourceFile {
        name: args.file,
        contents,
    });

    let effects = effects::DefaultEffects::enumerate();
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
                    let effect = DefaultEffects::from_repr(pending_effect as usize).unwrap();
                    match effect {
                        abra_core::effects::DefaultEffects::PrintString => {
                            let s = vm.top().get_string(&vm);
                            print!("{}", s);
                            vm.pop();
                            vm.push_nil();
                        }
                        abra_core::effects::DefaultEffects::Read => {
                            unimplemented!()
                            // let mut input = String::new();
                            // std::io::stdin().read_line(&mut input).unwrap();
                            // vm.set_effect_result(
                            //     abra_core::eval_tree::Expr::from(input.trim()).into(),
                            // );
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
