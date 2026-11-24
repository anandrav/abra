/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::io::{BufRead, BufReader, Read, Write};
use std::path::PathBuf;
use std::process::{Child, Command, Output, Stdio};
use std::sync::{Once, mpsc};
use std::thread;
use std::time::{Duration, Instant};

fn command(fixture: &str) -> Command {
    let cli_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_dir = cli_dir.parent().unwrap();
    static BUILD_CORE: Once = Once::new();
    BUILD_CORE.call_once(|| {
        let output = Command::new("cargo")
            .args(["build", "--offline", "-p", "abra_module_core"])
            .current_dir(repo_dir)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "core module build failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    });
    let mut command = Command::new(env!("CARGO_BIN_EXE_abra"));
    command
        .arg("--standard-modules")
        .arg(repo_dir.join("modules"))
        .arg(cli_dir.join("tests/fixtures").join(fixture))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    command
}

fn wait_output(mut child: Child) -> Output {
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        if child.try_wait().unwrap().is_some() {
            return child.wait_with_output().unwrap();
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            let output = child.wait_with_output().unwrap();
            panic!(
                "program timed out: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        thread::sleep(Duration::from_millis(10));
    }
}

fn run(fixture: &str, input: &[u8]) -> Output {
    let mut child = command(fixture).spawn().unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    wait_output(child)
}

#[test]
fn read_line() {
    let output = run("io_lines.abra", "first\r\n\nsecond\rtail 😀".as_bytes());
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        output.stdout,
        "line:first\nline:\nline:second\nline:tail 😀\nEOF\n".as_bytes()
    );
    let output = run("io_lines.abra", b"\xff\n");
    assert_eq!(output.status.code(), Some(2));
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("ERROR:invalid data:"));
    assert!(!stderr.contains("panic") && !stderr.contains("traceback"));
}

#[test]
fn input() {
    let output = run("io_input.abra", b"Ada\n\n");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"Name: Ada\n\n");

    for (input, expected) in [
        (b"".as_slice(), "end of input"),
        (b"\xff\n".as_slice(), "invalid data"),
    ] {
        let output = run("io_input.abra", input);
        assert_eq!(output.status.code(), Some(1));
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.contains("Could not read input:") && stderr.contains(expected));
        assert!(!stderr.contains("panic") && !stderr.contains("traceback"));
    }
}

#[test]
fn waiting_for_stdin_does_not_block_other_tasks() {
    let mut child = command("io_async.abra").spawn().unwrap();
    let stdout = child.stdout.take().unwrap();
    let (sender, receiver) = mpsc::channel();
    let reader = thread::spawn(move || {
        let mut stdout = BufReader::new(stdout);
        let mut line = String::new();
        stdout.read_line(&mut line).unwrap();
        sender.send(line).unwrap();
        let mut remaining = String::new();
        stdout.read_to_string(&mut remaining).unwrap();
        remaining
    });
    let line = receiver.recv_timeout(Duration::from_secs(2));
    if line.is_err() {
        let _ = child.kill();
    } else {
        child.stdin.take().unwrap().write_all(b"hello\n").unwrap();
    }
    let output = wait_output(child);
    let remaining = reader.join().unwrap();
    assert_eq!(line.unwrap(), "worker progressed\n");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(remaining, "hello\n");
}
