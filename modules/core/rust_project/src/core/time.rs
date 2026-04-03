/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::thread;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use abra_core::vm::AbraInt;
use chrono::{Datelike, Local, NaiveDate, NaiveDateTime, NaiveTime, TimeZone, Timelike, Utc};

use crate::ffi::core::time::DateTime;

pub fn get_time() -> f64 {
    let now = SystemTime::now();
    let duration_since_epoch = now.duration_since(UNIX_EPOCH).expect("Time went backwards");
    duration_since_epoch.as_secs_f64()
}

pub fn sleep(seconds: f64) {
    let duration = Duration::from_secs_f64(seconds);
    thread::sleep(duration);
}

fn chrono_utc_to_datetime(dt: chrono::DateTime<Utc>) -> DateTime {
    DateTime {
        year: dt.year() as AbraInt,
        month: dt.month() as AbraInt,
        day: dt.day() as AbraInt,
        hour: dt.hour() as AbraInt,
        minute: dt.minute() as AbraInt,
        second: dt.second() as AbraInt,
        timestamp: dt.timestamp() as f64 + dt.timestamp_subsec_nanos() as f64 / 1_000_000_000.0,
    }
}

fn naive_to_datetime(ndt: NaiveDateTime) -> DateTime {
    let utc = ndt.and_utc();
    chrono_utc_to_datetime(utc)
}

pub fn now_utc() -> DateTime {
    chrono_utc_to_datetime(Utc::now())
}

pub fn now_local() -> DateTime {
    let local = Local::now();
    DateTime {
        year: local.year() as AbraInt,
        month: local.month() as AbraInt,
        day: local.day() as AbraInt,
        hour: local.hour() as AbraInt,
        minute: local.minute() as AbraInt,
        second: local.second() as AbraInt,
        timestamp: local.timestamp() as f64
            + local.timestamp_subsec_nanos() as f64 / 1_000_000_000.0,
    }
}

pub fn from_timestamp(timestamp: f64) -> DateTime {
    let secs = timestamp.floor() as i64;
    let nanos = ((timestamp - timestamp.floor()) * 1_000_000_000.0) as u32;
    let dt = chrono::DateTime::from_timestamp(secs, nanos).unwrap_or(Utc.timestamp_nanos(0));
    chrono_utc_to_datetime(dt)
}

pub fn make_datetime(
    year: AbraInt,
    month: AbraInt,
    day: AbraInt,
    hour: AbraInt,
    minute: AbraInt,
    second: AbraInt,
) -> Option<DateTime> {
    let date = NaiveDate::from_ymd_opt(year as i32, month as u32, day as u32)?;
    let time = NaiveTime::from_hms_opt(hour as u32, minute as u32, second as u32)?;
    let ndt = NaiveDateTime::new(date, time);
    Some(naive_to_datetime(ndt))
}

fn datetime_to_naive(dt: &DateTime) -> NaiveDateTime {
    let date = NaiveDate::from_ymd_opt(dt.year as i32, dt.month as u32, dt.day as u32)
        .unwrap_or(NaiveDate::from_ymd_opt(1970, 1, 1).unwrap());
    let time = NaiveTime::from_hms_opt(dt.hour as u32, dt.minute as u32, dt.second as u32)
        .unwrap_or(NaiveTime::from_hms_opt(0, 0, 0).unwrap());
    NaiveDateTime::new(date, time)
}

pub fn format(dt: DateTime, fmt: String) -> String {
    datetime_to_naive(&dt).format(&fmt).to_string()
}

pub fn parse(s: String, fmt: String) -> Option<DateTime> {
    let ndt = NaiveDateTime::parse_from_str(&s, &fmt).ok()?;
    Some(naive_to_datetime(ndt))
}

pub fn weekday_of(dt: DateTime) -> String {
    datetime_to_naive(&dt).format("%A").to_string()
}
