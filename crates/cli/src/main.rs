use abra_core::FileData;
use abra_core::FileProviderDefault;
use abra_core::effects::EffectTrait;
use abra_core::effects::FromRepr;
use abra_core::effects::VariantArray;
use abra_core::effects::{Nominal, Type};
use clap::Parser;
use std::path::PathBuf;
use std::process::exit;

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

    /// Directory containing compiled shared objects from Abra modules
    #[arg(
        short,
        long,
        value_name = "DIRECTORY",
        help = "Override the default shared objects directory (~/.abra/shared_objects)."
    )]
    shared_objects: Option<String>,

    /// Additional arguments to pass to the Abra program
    #[arg(
        help = "Arguments to pass to the Abra program",
        value_name = "ARGS",
        trailing_var_arg = true
    )]
    args: Vec<String>,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let mut source_files = Vec::new();

    let contents = match std::fs::read_to_string(&args.file) {
        Ok(c) => c,
        Err(err) => {
            eprintln!("Could not open file '{}': {}", args.file, err);
            exit(1);
        }
    };
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

    let modules_dir: PathBuf = match args.modules {
        Some(modules) => {
            let current_dir = std::env::current_dir().expect("Can't get current directory.");
            current_dir.join(modules)
        }
        None => {
            let home_dir = home::home_dir().expect("Can't get home directory.");
            home_dir.join(".abra/modules")
        }
    };
    let shared_objects_dir: PathBuf = match args.shared_objects {
        Some(shared_objects_dir) => {
            let current_dir = std::env::current_dir().expect("Can't get current directory.");
            current_dir.join(shared_objects_dir)
        }
        None => {
            let home_dir = home::home_dir().expect("Can't get home directory.");
            home_dir.join(".abra/shared_objects")
        }
    };

    let effects = CliEffects::enumerate();

    let main_file_dir = if main_file_path.is_absolute() {
        main_file_path.parent().unwrap()
    } else {
        &std::env::current_dir()
            .unwrap()
            .join(main_file_path.parent().unwrap())
    };
    let file_provider =
        FileProviderDefault::new(main_file_dir.into(), modules_dir, shared_objects_dir);

    match abra_core::compile_bytecode(source_files, effects, file_provider) {
        Ok(program) => {
            let mut vm = abra_core::vm::Vm::new(program);
            loop {
                if vm.is_done() {
                    return Ok(());
                }
                if let Some(error) = vm.get_error() {
                    eprintln!("{}", error);
                    std::process::exit(1);
                }
                vm.run();
                vm.gc();
                if let Some(pending_effect) = vm.get_pending_effect() {
                    let effect = CliEffects::from_repr(pending_effect as usize).unwrap();
                    match effect {
                        CliEffects::PrintString => {
                            let s = vm.top()?.get_string(&vm)?;
                            vm.pop()?;
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
