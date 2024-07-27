extern crate abra_core;

use abra_core::interpreter::InterpreterStatus;
use abra_core::side_effects::{self, EffectTrait};
use abra_core::SourceFile;
use clap::Parser;
use once_cell::sync::Lazy;

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
        contents: abra_core::_PRELUDE.to_string(),
    });

    let Ok(contents) = std::fs::read_to_string(&args.file) else {
        eprintln!("file '{}' not found", args.file);
        return;
    };
    source_files.push(SourceFile {
        name: args.file,
        contents,
    });

    match abra_core::compile::<side_effects::DefaultEffects>(source_files) {
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
                            abra_core::side_effects::DefaultEffects::PrintString => match &*args[0]
                            {
                                abra_core::eval_tree::Expr::Str(string) => {
                                    print!("{}", string);
                                    effect_result = Some(abra_core::eval_tree::Expr::Unit.into());
                                }
                                _ => panic!("wrong arguments for {:#?} effect", effect),
                            },
                            abra_core::side_effects::DefaultEffects::Read => {
                                let mut input = String::new();
                                std::io::stdin().read_line(&mut input).unwrap();
                                effect_result =
                                    Some(abra_core::eval_tree::Expr::from(input.trim()).into());
                            }
                        }
                    }
                }
            }
        }
        Err(err) => {
            eprintln!("{}", err);
        }
    }
}

static EFFECT_LIST: Lazy<Vec<abra_core::side_effects::DefaultEffects>> =
    Lazy::new(abra_core::side_effects::DefaultEffects::enumerate);
