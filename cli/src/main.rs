extern crate abra_core;

use std::collections::HashMap;
use std::ffi::CStr;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

// use abra_core::addons::AddonDesc;
use abra_core::effects::EffectTrait;
use abra_core::effects::FromRepr;
use abra_core::effects::Type;
use abra_core::effects::VariantArray;
use abra_core::SourceFile;
use clap::Parser;
use libloading::Library;
use libloading::Symbol;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// File to run
    #[arg(
        help = "The main Abra script file to compile and execute",
        value_name = "FILE"
    )]
    file: String,

    /// Directory containing Abra modules
    #[arg(
        short,
        long,
        value_name = "DIRECTORY",
        help = "Path to the directory containing Abra dependencies"
    )]
    include_dir: Option<String>,
}

fn main() {
    let args = Args::parse();

    let mut source_files = Vec::new();
    source_files.push(SourceFile {
        name: "prelude.abra".to_string(),
        contents: abra_core::prelude::_PRELUDE.to_string(),
    });

    let contents = std::fs::read_to_string(&args.file).unwrap();
    source_files.push(SourceFile {
        name: args.file.clone(),
        contents,
    });
    let Ok(current_dir) = std::env::current_dir() else {
        eprintln!("Could not get current directory");
        std::process::exit(1);
    };
    let current_dir_files = std::fs::read_dir(current_dir).unwrap();
    for file in current_dir_files {
        let file = file.unwrap();
        let file_name = file.file_name();
        let file_name = file_name.to_str().unwrap();
        if file_name.ends_with(".abra") && file_name != args.file {
            let contents = std::fs::read_to_string(file.path()).unwrap();
            source_files.push(SourceFile {
                name: file_name.to_string(),
                contents,
            });
        }
    }

    if let Some(include_dir) = args.include_dir {
        let include_dir_files = std::fs::read_dir(include_dir).unwrap();
        for file in include_dir_files {
            let file = file.unwrap();
            let file_name = file.file_name();
            let file_name = file_name.to_str().unwrap();
            if file_name.ends_with(".abra") {
                let contents = std::fs::read_to_string(file.path()).unwrap();
                source_files.push(SourceFile {
                    name: file_name.to_string(),
                    contents,
                });
            }
        }
    }

    let effects = CliEffects::enumerate();

    // dylib
    static LIB_IDX_COUNTER: std::sync::atomic::AtomicUsize = AtomicUsize::new(0);
    let mut libname_to_idx: HashMap<String, usize> = HashMap::new();
    let mut libs: Vec<Library> = vec![];

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
                            vm.pop();
                            print!("{}", s);
                            vm.push_nil();
                        }
                        CliEffects::Read => {
                            let mut input = String::new();
                            std::io::stdin().read_line(&mut input).unwrap();
                            vm.push_str(&input[0..input.len() - 1]);
                        }
                        CliEffects::LoadLib => {
                            let s = vm.top().get_string(&vm);
                            vm.pop();
                            let lookup = libname_to_idx.get(&s);
                            match lookup {
                                Some(idx) => {
                                    vm.push_int(*idx as i64);
                                }
                                None => {
                                    let lib = unsafe { Library::new(s.clone()) };
                                    match lib {
                                        Ok(lib) => {
                                            let f: Result<Symbol<unsafe extern "C" fn() -> ()>, _> =
                                                unsafe { lib.get(b"addon_description") };
                                            match f {
                                                Ok(f) => {
                                                    // let addon_desc =
                                                    //     unsafe { f().as_ref().unwrap() };
                                                    // println!(
                                                    //     "the addon is named {}",
                                                    //     addon_desc.name
                                                    // );

                                                    let idx = LIB_IDX_COUNTER
                                                        .fetch_add(1, Ordering::Relaxed);
                                                    libname_to_idx.insert(s, idx);
                                                    libs.push(lib);
                                                    vm.push_int(idx as i64);
                                                }
                                                Err(e) => {
                                                    eprintln!("Could not load lib {}\n", s);
                                                    eprintln!("{}", e);
                                                    std::process::exit(1);
                                                }
                                            }
                                        }
                                        Err(e) => {
                                            eprintln!("Could not load lib {}\n", s);
                                            eprintln!("{}", e);
                                            std::process::exit(1);
                                        }
                                    }
                                }
                            }
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
