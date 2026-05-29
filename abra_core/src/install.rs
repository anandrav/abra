/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::path::PathBuf;

pub fn standard_modules_dir() -> PathBuf {
    let exe = std::env::current_exe().expect("Can't locate current executable.");
    let exe = std::fs::canonicalize(&exe).unwrap_or(exe);
    exe.parent()
        .and_then(|bin| bin.parent())
        .expect("Executable path has no grandparent.")
        .join("share/abra/modules")
}
