/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::process::Command;

pub fn command(content: String) -> i64 {
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
        Err(err) => err.raw_os_error().unwrap() as i64,
    }
}
