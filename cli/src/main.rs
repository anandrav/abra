extern crate abra_core;

use abra_core::SourceFile;

use abra_core::interpreter::InterpreterStatus;
use abra_core::side_effects::{self, EffectTrait};
use clap::Parser;
use once_cell::sync::Lazy;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Name of the person to greet
    #[arg(short, long)]
    files: Option<Vec<String>>,
}

fn main() {
    let args = Args::parse();

    if let Some(files) = args.files {
        let mut source_files = Vec::new();
        source_files.push(SourceFile {
            name: "prelude.abra".to_string(),
            contents: abra_core::_PRELUDE.to_string(),
        });
        for file in files {
            let contents = std::fs::read_to_string(&file).unwrap();
            source_files.push(SourceFile {
                name: file,
                contents,
            });
        }
        match abra_core::compile::<side_effects::Effect>(source_files) {
            Ok(runtime) => {
                let mut interpreter = runtime.toplevel_interpreter();
                let steps = i32::MAX;
                let mut effect_result = None;
                loop {
                    let status = interpreter.run(steps, effect_result.take());
                    match status {
                        InterpreterStatus::Error(msg) => {
                            println!("{}", msg);
                        }
                        InterpreterStatus::Finished => break,
                        InterpreterStatus::OutOfSteps => continue,
                        InterpreterStatus::Effect(code, args) => {
                            let effect = &EFFECT_LIST[code as usize];
                            match effect {
                                abra_core::side_effects::Effect::PrintString => match &*args[0] {
                                    abra_core::eval_tree::Expr::Str(string) => {
                                        print!("{}", string);
                                        effect_result =
                                            Some(abra_core::eval_tree::Expr::Unit.into());
                                    }
                                    _ => panic!("wrong arguments for {:#?} effect", effect),
                                },
                            }
                        }
                    }
                }
            }
            Err(err) => {
                println!("{}", err);
            }
        }
    } else {
        println!("REPL not implemented");
    }
}

static EFFECT_LIST: Lazy<Vec<abra_core::side_effects::Effect>> =
    Lazy::new(abra_core::side_effects::Effect::enumerate);
