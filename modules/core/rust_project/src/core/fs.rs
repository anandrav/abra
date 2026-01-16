/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::fs::{self, OpenOptions};
use std::io::Write;

pub fn fread(path: String) -> Option<String> {
    fs::read_to_string(path).ok()
}

pub fn fwrite(path: String, content: String) {
    fs::write(path, content).expect("Unable to write to file");
}

pub fn fexists(path: String) -> bool {
    fs::exists(path).unwrap()
}

pub fn fremove(path: String) {
    fs::remove_file(path).unwrap()
}

pub fn frename(old_path: String, new_path: String) {
    fs::rename(old_path, new_path).unwrap();
}

pub fn fcopy(src: String, dest: String) {
    fs::copy(src, dest).unwrap();
}

pub fn fappend(path: String, content: String) {
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .unwrap();

    // Write the text followed by a newline.
    writeln!(file, "{content}").unwrap();
}
