use std::time::{SystemTime, UNIX_EPOCH};

use crate::time::Time;

pub fn get_time() -> Time {
    let now = SystemTime::now();

    let duration_since_epoch = now.duration_since(UNIX_EPOCH).expect("Time went backwards");

    let seconds = duration_since_epoch.as_secs();
    let nanoseconds = duration_since_epoch.subsec_nanos();

    Time {
        seconds: seconds as i64,
        nanoseconds: nanoseconds as i64,
    }
}
