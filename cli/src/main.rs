extern crate abra_core;

use abra_core::interpreter::InterpreterStatus;
use abra_core::side_effects::{self, EffectTrait};
use abra_core::SourceFile;
use clap::Parser;
use colored::*;
use once_cell::sync::Lazy;
use rustyline::error::ReadlineError;
use rustyline::{DefaultEditor, Result};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Name of the person to greet
    #[arg(short, long)]
    files: Option<Vec<String>>,
}

fn main() -> Result<()> {
    let args = Args::parse();

    if let Some(files) = args.files {
        let mut source_files = Vec::new();
        source_files.push(SourceFile {
            name: "prelude.abra".to_string(),
            contents: abra_core::_PRELUDE.to_string(),
        });
        for file in files {
            let contents = std::fs::read_to_string(&file).unwrap();
            //.unwrap_or_else(|_| panic!("file '{}' not found", file));
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
                Ok(())
            }
            Err(err) => {
                println!("{}", err);
                Ok(())
            }
        }
    } else {
        println!(
            "{}",
            r#"
        ___                      
        -   -_, ,,                
       (  ~/||  ||            _   
       (  / ||  ||/|, ,._-_  < \,       Version 0.1.0
        \/==||  || ||  ||    /-||       https://github.com/anandrav/abra
        /_ _||  || |'  ||   (( || 
       (  - \\, \\/    \\,   \/\\ 
        "#
            .magenta()
            .bold()
        );
        let mut rl = DefaultEditor::new().unwrap();
        loop {
            let readline = rl.readline(">> ");
            match readline {
                Ok(line) => {
                    let _ = rl.add_history_entry(line.as_str());
                    println!("Line: {}", line);
                }
                Err(ReadlineError::Interrupted) => {
                    break;
                }
                Err(ReadlineError::Eof) => {
                    break;
                }
                Err(err) => {
                    println!("Error: {:?}", err);
                    break;
                }
            }
        }
        Ok(())
    }
}

static EFFECT_LIST: Lazy<Vec<abra_core::side_effects::Effect>> =
    Lazy::new(abra_core::side_effects::Effect::enumerate);
