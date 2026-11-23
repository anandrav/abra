/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ffi::core::exec::{ExecError, InputSource, Output, OutputEvent, OutputTarget, Process};
use abra_core::vm::AbraInt;
use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Arc, Mutex, OnceLock, mpsc};
use std::thread;
use std::time::Duration;

struct RunningProcess {
    children: Mutex<Vec<Child>>,
    output: Mutex<mpsc::Receiver<Result<OutputEvent, ExecError>>>,
    input: Mutex<Option<thread::JoinHandle<Result<(), ExecError>>>>,
}

static PROCESSES: OnceLock<Mutex<HashMap<AbraInt, Arc<RunningProcess>>>> = OnceLock::new();
static NEXT_HANDLE: AtomicI64 = AtomicI64::new(1);

fn processes() -> &'static Mutex<HashMap<AbraInt, Arc<RunningProcess>>> {
    PROCESSES.get_or_init(|| Mutex::new(HashMap::new()))
}

fn process(handle: AbraInt) -> Result<Arc<RunningProcess>, ExecError> {
    processes()
        .lock()
        .unwrap()
        .get(&handle)
        .cloned()
        .ok_or_else(|| ExecError::Other("process handle is closed or invalid".to_string()))
}

fn io_err_to_exec_error(e: std::io::Error) -> ExecError {
    match e.kind() {
        std::io::ErrorKind::NotFound => ExecError::NotFound(e.to_string()),
        std::io::ErrorKind::PermissionDenied => ExecError::PermissionDenied(e.to_string()),
        _ => ExecError::Other(e.to_string()),
    }
}

fn parse_command(content: &str) -> Result<Vec<String>, ExecError> {
    let mut words = Vec::new();
    let mut word = String::new();
    let mut quote = None;
    let mut started = false;
    let mut chars = content.chars();
    while let Some(c) = chars.next() {
        if quote == Some('\'') {
            if c == '\'' {
                quote = None;
            } else {
                word.push(c);
            }
        } else if c == '\\' {
            let Some(next) = chars.next() else {
                return Err(ExecError::Other("command ends with an escape".to_string()));
            };
            if next != '\n' {
                if quote == Some('"') && !matches!(next, '"' | '\\' | '$' | '`') {
                    word.push('\\');
                }
                word.push(next);
                started = true;
            }
        } else if quote == Some('"') {
            if c == '"' {
                quote = None;
            } else {
                word.push(c);
            }
        } else if c == '\'' || c == '"' {
            quote = Some(c);
            started = true;
        } else if c.is_whitespace() {
            if started {
                words.push(std::mem::take(&mut word));
                started = false;
            }
        } else {
            word.push(c);
            started = true;
        }
    }
    if quote.is_some() {
        return Err(ExecError::Other(
            "unterminated quote in command".to_string(),
        ));
    }
    if started {
        words.push(word);
    }
    if words.is_empty() || words[0].is_empty() {
        return Err(ExecError::Other("empty command".to_string()));
    }
    Ok(words)
}

fn output_file(target: &OutputTarget) -> Result<Option<File>, ExecError> {
    if let OutputTarget::File((path, append)) = target {
        OpenOptions::new()
            .create(true)
            .write(true)
            .append(*append)
            .truncate(!append)
            .open(path)
            .map(Some)
            .map_err(io_err_to_exec_error)
    } else {
        Ok(None)
    }
}

fn output_stdio(target: &OutputTarget, file: &Option<File>) -> Result<Stdio, ExecError> {
    match target {
        OutputTarget::Pipe => Ok(Stdio::piped()),
        OutputTarget::Inherit => Ok(Stdio::inherit()),
        OutputTarget::Discard => Ok(Stdio::null()),
        OutputTarget::File(_) => file
            .as_ref()
            .unwrap()
            .try_clone()
            .map(Stdio::from)
            .map_err(io_err_to_exec_error),
    }
}

fn read_output(
    mut stream: impl Read + Send + 'static,
    stderr: bool,
    sender: mpsc::Sender<Result<OutputEvent, ExecError>>,
) {
    thread::spawn(move || {
        let mut buffer = [0; 8192];
        let mut pending = Vec::new();
        loop {
            let count = match stream.read(&mut buffer) {
                Ok(count) => count,
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                Err(e) => {
                    let _ = sender.send(Err(io_err_to_exec_error(e)));
                    return;
                }
            };
            pending.extend_from_slice(&buffer[..count]);
            let end = if count == 0 {
                pending.len()
            } else {
                match std::str::from_utf8(&pending) {
                    Err(e) if e.error_len().is_none() => e.valid_up_to(),
                    _ => pending.len(),
                }
            };
            if end > 0 {
                let text = String::from_utf8_lossy(&pending[..end]).into_owned();
                pending.drain(..end);
                let event = if stderr {
                    OutputEvent::Stderr(text)
                } else {
                    OutputEvent::Stdout(text)
                };
                if sender.send(Ok(event)).is_err() {
                    return;
                }
            }
            if count == 0 {
                return;
            }
        }
    });
}

fn detach_command(command: &mut Command) {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        // Only async-signal-safe calls belong between fork and exec.
        unsafe {
            command.pre_exec(|| {
                if libc::setsid() == -1
                    || libc::signal(libc::SIGHUP, libc::SIG_IGN) == libc::SIG_ERR
                {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
    }
    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt;
        command.creation_flags(0x00000008 | 0x00000200); // DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP
    }
}

fn start_pipeline(
    commands: Vec<Vec<String>>,
    input: InputSource,
    stdout: OutputTarget,
    stderr: OutputTarget,
    detached: bool,
) -> Result<RunningProcess, ExecError> {
    if commands.is_empty() {
        return Err(ExecError::Other("empty pipeline".to_string()));
    }
    if detached && (matches!(stdout, OutputTarget::Pipe) || matches!(stderr, OutputTarget::Pipe)) {
        return Err(ExecError::Other(
            "detached output cannot be piped back to Abra".to_string(),
        ));
    }
    if detached && matches!(input, InputSource::Text(_)) {
        return Err(ExecError::Other(
            "detached input must come from a file or be discarded".to_string(),
        ));
    }
    let shared_file = match (&stdout, &stderr) {
        (OutputTarget::File((a, append_a)), OutputTarget::File((b, append_b))) if a == b => {
            if append_a != append_b {
                return Err(ExecError::Other(
                    "stdout and stderr must use the same append mode for a shared file".to_string(),
                ));
            }
            true
        }
        _ => false,
    };
    let stdout_file = output_file(&stdout)?;
    let stderr_file = if shared_file {
        Some(
            stdout_file
                .as_ref()
                .unwrap()
                .try_clone()
                .map_err(io_err_to_exec_error)?,
        )
    } else {
        output_file(&stderr)?
    };
    let (sender, receiver) = mpsc::channel();
    let mut children: Vec<Child> = Vec::new();
    let mut previous_stdout = None;
    let started = (|| {
        for (i, words) in commands.iter().enumerate() {
            let mut command = Command::new(&words[0]);
            command.args(&words[1..]);
            if detached {
                detach_command(&mut command);
            }
            if i == 0 {
                command.stdin(match &input {
                    InputSource::Inherit if !detached => Stdio::inherit(),
                    InputSource::Inherit | InputSource::Discard => Stdio::null(),
                    InputSource::Text(_) => Stdio::piped(),
                    InputSource::File(path) => {
                        Stdio::from(File::open(path).map_err(io_err_to_exec_error)?)
                    }
                });
            } else {
                command.stdin(Stdio::from(previous_stdout.take().unwrap()));
            }
            let last = i == commands.len() - 1;
            command.stdout(if last {
                output_stdio(&stdout, &stdout_file)?
            } else {
                Stdio::piped()
            });
            command.stderr(output_stdio(&stderr, &stderr_file)?);
            let mut child = command.spawn().map_err(io_err_to_exec_error)?;
            if last {
                if let Some(stream) = child.stdout.take() {
                    read_output(stream, false, sender.clone());
                }
            } else {
                previous_stdout = child.stdout.take();
            }
            if let Some(stream) = child.stderr.take() {
                read_output(stream, true, sender.clone());
            }
            children.push(child);
        }
        Ok::<(), ExecError>(())
    })();
    if let Err(e) = started {
        for child in &mut children {
            let _ = child.kill();
            let _ = child.wait();
        }
        return Err(e);
    }
    let writer = if let InputSource::Text(text) = input {
        let mut stdin = children[0].stdin.take().unwrap();
        Some(thread::spawn(move || {
            stdin
                .write_all(text.as_bytes())
                .map_err(io_err_to_exec_error)
        }))
    } else {
        None
    };
    Ok(RunningProcess {
        children: Mutex::new(children),
        output: Mutex::new(receiver),
        input: Mutex::new(writer),
    })
}

fn pipeline_commands(
    commands: Vec<String>,
    all_args: Vec<Vec<String>>,
) -> Result<Vec<Vec<String>>, ExecError> {
    if commands.len() != all_args.len() {
        return Err(ExecError::Other(
            "pipeline arguments do not match commands".to_string(),
        ));
    }
    commands
        .into_iter()
        .zip(all_args)
        .map(|(command, args)| {
            let mut words = parse_command(&command)?;
            words.extend(args);
            Ok(words)
        })
        .collect()
}

fn register_process(running: RunningProcess) -> Process {
    let pid = running.children.lock().unwrap().last().unwrap().id() as AbraInt;
    let handle = NEXT_HANDLE.fetch_add(1, Ordering::Relaxed);
    processes()
        .lock()
        .unwrap()
        .insert(handle, Arc::new(running));
    Process { pid, handle }
}

pub fn spawn_pipeline(
    commands: Vec<String>,
    all_args: Vec<Vec<String>>,
    input: InputSource,
    stdout: OutputTarget,
    stderr: OutputTarget,
) -> Result<Process, ExecError> {
    start_pipeline(
        pipeline_commands(commands, all_args)?,
        input,
        stdout,
        stderr,
        false,
    )
    .map(register_process)
}

pub fn run_pipeline(
    commands: Vec<String>,
    all_args: Vec<Vec<String>>,
    input: InputSource,
    stdout: OutputTarget,
    stderr: OutputTarget,
) -> Result<Output, ExecError> {
    let running = spawn_pipeline(commands, all_args, input, stdout, stderr)?;
    collect_output(running.handle)
}

fn collect_output(handle: AbraInt) -> Result<Output, ExecError> {
    let mut stdout = String::new();
    let mut stderr = String::new();
    loop {
        match process_read_output(handle) {
            Ok(Some(OutputEvent::Stdout(text))) => stdout.push_str(&text),
            Ok(Some(OutputEvent::Stderr(text))) => stderr.push_str(&text),
            Ok(None) => break,
            Err(e) => {
                let _ = process_kill(handle);
                let _ = process_wait(handle);
                return Err(e);
            }
        }
    }
    Ok(Output {
        stdout,
        stderr,
        status: process_wait(handle)?,
    })
}

pub fn run_sh(
    content: String,
    stdout: OutputTarget,
    stderr: OutputTarget,
) -> Result<Output, ExecError> {
    let (shell, flag) = if cfg!(windows) {
        ("cmd", "/C")
    } else {
        ("sh", "-c")
    };
    let running = start_pipeline(
        vec![vec![shell.to_string(), flag.to_string(), content]],
        InputSource::Inherit,
        stdout,
        stderr,
        false,
    )?;
    collect_output(register_process(running).handle)
}

pub fn detach_pipeline(
    commands: Vec<String>,
    all_args: Vec<Vec<String>>,
    input: InputSource,
    stdout: OutputTarget,
    stderr: OutputTarget,
) -> Result<AbraInt, ExecError> {
    let running = start_pipeline(
        pipeline_commands(commands, all_args)?,
        input,
        stdout,
        stderr,
        true,
    )?;
    let mut children = running.children.into_inner().unwrap();
    let pid = children.last().unwrap().id() as AbraInt;
    thread::spawn(move || {
        for child in &mut children {
            let _ = child.wait();
        }
    });
    Ok(pid)
}

pub fn process_read_output(handle: AbraInt) -> Result<Option<OutputEvent>, ExecError> {
    let running = process(handle)?;
    match running.output.lock().unwrap().recv() {
        Ok(event) => event.map(Some),
        Err(_) => Ok(None),
    }
}

pub fn process_poll(handle: AbraInt) -> Result<Option<AbraInt>, ExecError> {
    let running = process(handle)?;
    let mut children = running.children.lock().unwrap();
    let mut finished = true;
    let mut status = None;
    for child in children.iter_mut() {
        match child.try_wait().map_err(io_err_to_exec_error)? {
            Some(exit) => status = Some(exit.code().unwrap_or(-1) as AbraInt),
            None => finished = false,
        }
    }
    Ok(if finished { status } else { None })
}

pub fn process_wait(handle: AbraInt) -> Result<AbraInt, ExecError> {
    let running = process(handle)?;
    let result = (|| {
        let status = loop {
            if let Some(status) = process_poll(handle)? {
                break status;
            }
            thread::sleep(Duration::from_millis(10));
        };
        if let Some(writer) = running.input.lock().unwrap().take() {
            writer
                .join()
                .map_err(|_| ExecError::Other("stdin writer failed".to_string()))??;
        }
        Ok(status)
    })();
    processes().lock().unwrap().remove(&handle);
    result
}

pub fn process_kill(handle: AbraInt) -> Result<(), ExecError> {
    let running = process(handle)?;
    for child in running.children.lock().unwrap().iter_mut() {
        if child.try_wait().map_err(io_err_to_exec_error)?.is_none() {
            child.kill().map_err(io_err_to_exec_error)?;
        }
    }
    Ok(())
}
