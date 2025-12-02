/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
use abra_core::FileData;
use abra_core::OsFileProvider;
use std::io;
use std::io::Write;
use std::path::PathBuf;
use std::process::exit;

mod host_funcs;
use host_funcs::*;

struct Args {
    file: String,
    modules: Option<String>,
    shared_objects: Option<String>,
    assembly: bool,
    _args: Vec<String>,
}

impl Args {
    fn parse() -> Result<Self, lexopt::Error> {
        use lexopt::prelude::*;

        let mut file = None;
        let mut modules = None;
        let mut shared_objects = None;
        let mut assembly = false;
        let mut args = Vec::new();
        let mut parser = lexopt::Parser::from_env();

        while let Some(arg) = parser.next()? {
            match arg {
                Short('m') | Long("modules") => {
                    modules = Some(parser.value()?.parse()?);
                }
                Short('s') | Long("shared-objects") => {
                    shared_objects = Some(parser.value()?.parse()?);
                }
                Short('a') | Long("assembly") => {
                    assembly = true;
                }
                Short('h') | Long("help") => {
                    print_help();
                    exit(0);
                }
                Value(val) => {
                    if file.is_none() {
                        file = Some(val.parse()?);
                    } else {
                        // If file is already found, everything else is a trailing arg
                        args.push(val.parse()?);
                    }
                }
                _ => return Err(arg.unexpected()),
            }
        }

        let Some(file) = file else {
            print_help();
            exit(0);
        };

        Ok(Args {
            file,
            modules,
            shared_objects,
            assembly,
            _args: args,
        })
    }
}

use std::io::IsTerminal;

fn c(code: &str) -> &str {
    let use_color = std::io::stdout().is_terminal();

    if use_color { code } else { "" }
}

fn print_help() {
    let title = c("\x1b[38;2;230;100;230m");
    let cyan = c("\x1b[38;2;100;230;230m");
    let bold = c("\x1b[1m");
    let reset = c("\x1b[0m");

    println!(
        "{title}{bold}Usage:{reset} {cyan}abra [OPTIONS] <FILE> [ARGS]...{reset}

{title}{bold}Arguments:{reset}
    {cyan}<FILE>{reset}    The main Abra file to compile and execute
    {cyan}[ARGS]{reset}    Arguments for the Abra program

{title}{bold}Options:{reset}
    {cyan}-m, --modules <DIRECTORY>{reset}          Override the default module directory
    {cyan}-s, --shared-objects <DIRECTORY>{reset}   Override the default shared objects directory
    {cyan}-a, --assembly{reset}                     Print the assembly for the Abra program
    {cyan}-h, --help{reset}                         Print help"
    );
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Parse args using lexopt logic
    let args = match Args::parse() {
        Ok(a) => a,
        Err(err) => {
            let red = c("\x1b[38;2;230;100;100m");
            let bold = c("\x1b[1m");
            let reset = c("\x1b[0m");
            eprintln!("{red}{bold}error:{reset} {}\n", err);
            print_help();
            exit(1);
        }
    };

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
        "prelude.abra".into(),
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

    let main_file_dir = if main_file_path.is_absolute() {
        main_file_path.parent().unwrap()
    } else {
        &std::env::current_dir()
            .unwrap()
            .join(main_file_path.parent().unwrap())
    };
    let file_provider = OsFileProvider::new(main_file_dir.into(), modules_dir, shared_objects_dir);

    let main_file_name = main_file_path.file_name().unwrap().to_str().unwrap();

    if args.assembly {
        match abra_core::compile_and_dump_assembly(main_file_name, file_provider) {
            Ok(_) => return Ok(()),
            Err(err) => {
                err.emit();
                exit(1);
            }
        }
    }

    match abra_core::compile_bytecode(main_file_name, file_provider) {
        Ok(program) => {
            let mut vm = abra_core::vm::Vm::new(program);
            loop {
                vm.run();
                if vm.is_done() {
                    return Ok(());
                }
                if let Some(error) = vm.get_error() {
                    eprint!("{error}");
                    exit(1);
                }
                if let Some(pending_host_func) = vm.get_pending_host_func() {
                    let host_func_args: HostFunctionArgs =
                        HostFunctionArgs::from_vm(&mut vm, pending_host_func);
                    match host_func_args {
                        HostFunctionArgs::PrintString(s) => {
                            print!("{s}");
                            io::stdout().flush().unwrap();
                            HostFunctionRet::PrintString.into_vm(&mut vm);
                        }
                        HostFunctionArgs::Readline => {
                            let mut input = String::new();
                            io::stdin().read_line(&mut input).unwrap();
                            if input.ends_with('\n') {
                                input.pop();
                                if input.ends_with('\r') {
                                    input.pop();
                                }
                            }
                            HostFunctionRet::Readline(input).into_vm(&mut vm);
                        }
                    }
                }
            }
        }
        Err(err) => {
            err.emit();
            exit(1);
        }
    }
}
