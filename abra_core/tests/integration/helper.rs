/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// functions used for testing

use abra_core::ErrorSummary;

pub fn unwrap_or_panic<T>(result: Result<T, ErrorSummary>) -> T {
    match result {
        Ok(value) => value,
        Err(e) => {
            panic!("{}", e.to_string_ansi());
        }
    }
}
