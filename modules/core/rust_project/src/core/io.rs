/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ffi::core::io::IoError;
use std::io::{self, Read};
use std::sync::Mutex;

static SKIP_LF: Mutex<bool> = Mutex::new(false);

pub fn read_line() -> Result<Option<String>, IoError> {
    let mut skip_lf = SKIP_LF.lock().unwrap();
    let stdin = io::stdin();
    let mut input = stdin.lock();
    read_line_from(&mut input, &mut skip_lf).map_err(|error| {
        if error.kind() == io::ErrorKind::InvalidData {
            IoError::InvalidData(error.to_string())
        } else {
            IoError::Other(error.to_string())
        }
    })
}

fn read_line_from(input: &mut impl Read, skip_lf: &mut bool) -> io::Result<Option<String>> {
    let mut line = Vec::new();
    loop {
        let mut byte = [0];
        let count = match input.read(&mut byte) {
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            result => result?,
        };
        if count == 0 {
            if line.is_empty() {
                return Ok(None);
            }
            break;
        }
        if *skip_lf {
            *skip_lf = false;
            if byte[0] == b'\n' {
                continue;
            }
        }
        if byte[0] == b'\r' {
            *skip_lf = true;
            break;
        }
        if byte[0] == b'\n' {
            break;
        }
        line.push(byte[0]);
    }
    String::from_utf8(line)
        .map(Some)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
}
