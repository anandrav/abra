/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use abra_core::vm::AbraInt;
use crate::ffi::core::exec::{ExecError, Output};
use std::io::Write;
use std::process::{Command, Stdio};

pub fn command(content: String) -> AbraInt {
    let content_elems: Vec<_> = content.split(' ').collect();

    let mut cmd = Command::new(content_elems[0]);
    for elem in &content_elems[1..] {
        cmd.arg(elem);
    }

    let output = cmd.output();
    match output {
        Ok(output) => {
            print!("{}", String::from_utf8_lossy(&output.stdout));
            eprint!("{}", String::from_utf8_lossy(&output.stderr));
            0
        }
        Err(err) => err.raw_os_error().unwrap() as AbraInt,
    }
}

fn io_err_to_exec_error(e: std::io::Error) -> ExecError {
    match e.kind() {
        std::io::ErrorKind::NotFound => ExecError::NotFound(e.to_string()),
        std::io::ErrorKind::PermissionDenied => ExecError::PermissionDenied(e.to_string()),
        _ => ExecError::Other(e.to_string()),
    }
}

pub fn run(content: String) -> Result<Output, ExecError> {
    let content_elems: Vec<_> = content.split(' ').collect();
    if content_elems.is_empty() {
        return Err(ExecError::Other("empty command".to_string()));
    }

    let mut cmd = Command::new(content_elems[0]);
    for elem in &content_elems[1..] {
        cmd.arg(elem);
    }

    let output = cmd.output().map_err(io_err_to_exec_error)?;
    Ok(Output {
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        status: output.status.code().unwrap_or(-1) as AbraInt,
    })
}

pub fn run_sh(content: String) -> Result<Output, ExecError> {
    let shell = if cfg!(target_os = "windows") {
        "cmd"
    } else {
        "sh"
    };
    let flag = if cfg!(target_os = "windows") {
        "/C"
    } else {
        "-c"
    };

    let output = Command::new(shell)
        .arg(flag)
        .arg(&content)
        .output()
        .map_err(io_err_to_exec_error)?;

    Ok(Output {
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        status: output.status.code().unwrap_or(-1) as AbraInt,
    })
}

pub fn run_pipeline(
    programs: Vec<String>,
    all_args: Vec<Vec<String>>,
    stdin_input: Option<String>,
) -> Result<Output, ExecError> {
    if programs.is_empty() {
        return Err(ExecError::Other("empty pipeline".to_string()));
    }

    if programs.len() == 1 {
        // Single command — simple path
        let mut cmd = Command::new(&programs[0]);
        cmd.args(&all_args[0]);

        if stdin_input.is_some() {
            cmd.stdin(Stdio::piped());
        }

        if let Some(ref input) = stdin_input {
            let mut child = cmd
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .map_err(io_err_to_exec_error)?;

            if let Some(ref mut child_stdin) = child.stdin {
                child_stdin
                    .write_all(input.as_bytes())
                    .map_err(io_err_to_exec_error)?;
            }
            drop(child.stdin.take());

            let output = child.wait_with_output().map_err(io_err_to_exec_error)?;
            Ok(Output {
                stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
                status: output.status.code().unwrap_or(-1) as AbraInt,
            })
        } else {
            let output = cmd.output().map_err(io_err_to_exec_error)?;
            Ok(Output {
                stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
                status: output.status.code().unwrap_or(-1) as AbraInt,
            })
        }
    } else {
        // Multi-command pipeline
        let mut children = Vec::new();
        let mut prev_stdout: Option<Stdio> = None;

        for (i, (program, args)) in programs.iter().zip(all_args.iter()).enumerate() {
            let mut cmd = Command::new(program);
            cmd.args(args);

            // First process: stdin from user input or inherited
            if i == 0 {
                if stdin_input.is_some() {
                    cmd.stdin(Stdio::piped());
                }
            } else {
                // Middle/last: stdin from previous process
                cmd.stdin(prev_stdout.take().unwrap());
            }

            cmd.stdout(Stdio::piped());
            cmd.stderr(Stdio::piped());

            let mut child = cmd.spawn().map_err(io_err_to_exec_error)?;
            if i < programs.len() - 1 {
                // Take ownership of stdout so it can be passed as stdin to the next process
                prev_stdout = Some(child.stdout.take().unwrap().into());
            }
            children.push(child);
        }

        // Write stdin to first process if provided
        if let Some(ref input) = stdin_input {
            if let Some(ref mut first_stdin) = children[0].stdin {
                first_stdin
                    .write_all(input.as_bytes())
                    .map_err(io_err_to_exec_error)?;
            }
            drop(children[0].stdin.take());
        }

        // Wait for last process and collect output
        let last = children.len() - 1;
        let output = children
            .remove(last)
            .wait_with_output()
            .map_err(io_err_to_exec_error)?;

        // Wait for remaining processes
        for mut child in children {
            let _ = child.wait();
        }

        Ok(Output {
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            status: output.status.code().unwrap_or(-1) as AbraInt,
        })
    }
}
