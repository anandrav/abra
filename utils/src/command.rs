/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#[macro_export]
macro_rules! command {
    ($s:expr) => {{
        use std::process::Command;
        let parts: Vec<&str> = $s.split_whitespace().collect();
        let (cmd, args) = parts
            .split_first()
            .expect("command! macro called with an empty string");
        Command::new(cmd).args(args).output()
    }};
}
