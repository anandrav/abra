use std::collections::HashMap;
use std::ffi::CStr;
use std::path::PathBuf;
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
    include_dirs: Vec<String>,
}

fn main() {
    let args = Args::parse();

    let mut source_files = Vec::new();
    source_files.push(SourceFile {
        name: "prelude.abra".to_string(),
        path: "prelude.abra".into(), // TODO: does path really make sense in this context? Should path be optional?
        contents: abra_core::prelude::_PRELUDE.to_string(),
    });

    let contents = std::fs::read_to_string(&args.file).unwrap();
    source_files.push(SourceFile {
        name: args.file.clone(),
        path: args.file.clone().into(),
        contents,
    });

    for include_dir in &args.include_dirs {
        add_modules_toplevel(include_dir.into(), &args.file, &mut source_files);
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

fn add_modules_toplevel(include_dir: PathBuf, main_file: &str, source_files: &mut Vec<SourceFile>) {
    let dir = std::fs::read_dir(&include_dir).unwrap();
    for entry in dir {
        let entry = entry.unwrap();
        let metadata = entry.metadata().unwrap();
        let name = entry.file_name();
        let name = name.to_str().unwrap();
        if metadata.is_file() && name.ends_with(".abra") && name != main_file {
            // get the corresponding directory if it exists
            let dir_name = &name[0..name.len() - ".abra".len()];
            let dir_path = include_dir.join(dir_name);

            let contents = std::fs::read_to_string(entry.path()).unwrap();
            source_files.push(SourceFile {
                name: name.to_string(),
                path: include_dir.join(name),
                contents,
            });
        } else if metadata.is_dir() {
            // add_module_dir(include_dir.join(name), source_files);
        }
    }
}

// fn add_module_dir(include_dir: PathBuf, source_files: &mut Vec<SourceFile>) {
//     let dir = std::fs::read_dir(&include_dir).unwrap();
//     for entry in dir {
//         let entry = entry.unwrap();
//         let metadata = entry.metadata().unwrap();
//         if !metadata.is_file() {
//             continue;
//         }
//         let name = entry.file_name();
//         let name = name.to_str().unwrap();
//         if name == "Cargo.toml" {
//             let contents = std::fs::read_to_string(entry.path()).unwrap();
//             source_files.push(SourceFile {
//                 name: name.to_string(),
//                 contents,
//             });
//         }
//     }
// }

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
