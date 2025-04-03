/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// functions used for testing

use std::fmt::Display;

pub fn unwrap_or_panic<T, E: Display>(result: Result<T, E>) -> T {
    match result {
        Ok(value) => value,
        Err(e) => {
            eprintln!("Error: {}", e);
            panic!("Exiting due to error.");
        }
    }
}
