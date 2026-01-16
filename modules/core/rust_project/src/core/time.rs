/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::thread;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

pub fn get_time() -> f64 {
    let now = SystemTime::now();
    let duration_since_epoch = now.duration_since(UNIX_EPOCH).expect("Time went backwards");
    duration_since_epoch.as_secs_f64()
}

pub fn sleep(seconds: f64) {
    let duration = Duration::from_secs_f64(seconds);
    thread::sleep(duration);
}
