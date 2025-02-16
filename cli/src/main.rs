use abra_core::effects::EffectTrait;
use abra_core::effects::FromRepr;
use abra_core::effects::VariantArray;
use abra_core::effects::{Nominal, Type};
use abra_core::FileData;
use abra_core::FileProviderDefault;
use clap::Parser;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None, arg_required_else_help = true)]
struct Args {
    /// File to run
    #[arg(
        help = "The main Abra file to compile and execute",
        value_name = "FILE"
    )]
    file: String,

    /// Directory containing Abra modules
    #[arg(
        short,
        long,
        value_name = "DIRECTORY",
        help = "Override the default module directory (~/.abra/modules)."
    )]
    modules: Option<String>,

    /// Additional arguments to pass to the Abra program
    #[arg(
        help = "Arguments to pass to the Abra program",
        value_name = "ARGS",
        trailing_var_arg = true
    )]
    args: Vec<String>,
}

fn main() {
    let args = Args::parse();

    let mut source_files = Vec::new();

    let contents = std::fs::read_to_string(&args.file).unwrap();
    let main_file_path: PathBuf = args.file.clone().into();
    source_files.push(FileData::new(
        main_file_path.clone(),
        main_file_path.clone(),
        contents,
    ));

    source_files.push(FileData::new(
        "prelude.abra".into(),
        "prelude.abra".into(), // TODO: does full_path really make sense in this context? Should path be optional?
        abra_core::prelude::PRELUDE.to_string(),
    ));

    let modules: PathBuf = match args.modules {
        Some(modules) => {
            let current_dir = std::env::current_dir().unwrap();
            current_dir.join(modules)
        }
        None => {
            let home_dir = home::home_dir()
                .expect("Could not determine home directory when looking for ~/.abra/modules");
            home_dir.join(".abra/modules")
        }
    };
    // add_modules_toplevel(modules, &args.file, &mut source_files);

    let effects = CliEffects::enumerate();

    let main_file_dir = if main_file_path.is_absolute() {
        main_file_path.parent().unwrap()
    } else {
        &std::env::current_dir()
            .unwrap()
            .join(main_file_path.parent().unwrap())
    };
    let file_provider = FileProviderDefault::new(main_file_dir.into(), modules);

    match abra_core::compile_bytecode(source_files, effects, file_provider) {
        Ok(program) => {
            let mut vm = abra_core::vm::Vm::new(program);
            loop {
                if vm.is_done() {
                    return;
                }
                if let Some(error) = vm.get_error() {
                    eprintln!("{}", error);
                    std::process::exit(1);
                }
                vm.run();
                // vm.gc();
                if let Some(pending_effect) = vm.get_pending_effect() {
                    let effect = CliEffects::from_repr(pending_effect as usize).unwrap();
                    match effect {
                        CliEffects::PrintString => {
                            let s = vm.top().get_string(&vm);
                            vm.pop();
                            print!("{}", s);
                            vm.push_nil();
                        }
                        CliEffects::ReadLine => {
                            let mut input = String::new();
                            std::io::stdin().read_line(&mut input).unwrap();
                            // remove trailing newline
                            if input.ends_with('\n') {
                                input.pop();
                                if input.ends_with('\r') {
                                    input.pop();
                                }
                            }
                            vm.push_str(input);
                        }
                        CliEffects::GetArgs => {
                            for arg in &args.args {
                                vm.push_str(arg.clone());
                            }
                            vm.construct_array(args.args.len());
                        }
                    }
                    vm.clear_pending_effect();
                }
            }
        }
        Err(err) => {
            eprintln!("{}", err);
            std::process::exit(1);
        }
    }
}

fn add_modules_toplevel(include_dir: PathBuf, main_file: &str, source_files: &mut Vec<FileData>) {
    let dir = std::fs::read_dir(&include_dir).unwrap();
    for entry in dir {
        let entry = entry.unwrap();
        let metadata = entry.metadata().unwrap();
        let name = entry.file_name();
        let name = name.to_str().unwrap();
        if metadata.is_file() && name.ends_with(".abra") && name != main_file {
            // get the corresponding directory if it exists
            let dir_name = &name[0..name.len() - ".abra".len()];

            let contents = std::fs::read_to_string(entry.path()).unwrap();
            source_files.push(FileData::new(name.into(), include_dir.join(name), contents));
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
    ReadLine,
    GetArgs,
}

impl EffectTrait for CliEffects {
    fn type_signature(&self) -> (Vec<Type>, Type) {
        match self {
            // print_string: string -> void
            CliEffects::PrintString => (vec![Type::String], Type::Unit),
            // readline: void -> string
            CliEffects::ReadLine => (vec![], Type::String),
            // get_args: void -> array<string>
            CliEffects::GetArgs => (vec![], Type::Nominal(Nominal::Array, vec![Type::String])),
        }
    }

    fn function_name(&self) -> &'static str {
        match self {
            CliEffects::PrintString => "print_string",
            CliEffects::ReadLine => "readline",
            CliEffects::GetArgs => "get_args",
        }
    }
}
