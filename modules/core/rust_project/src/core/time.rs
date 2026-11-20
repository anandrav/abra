/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::thread;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use abra_core::vm::AbraInt;
use jiff::{Timestamp, ZonedDateTime, civil, tz::TimeZone};

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

fn zoned_to_datetime(dt: ZonedDateTime) -> DateTime {
    let timestamp = dt.timestamp();
    DateTime {
        year: dt.year() as AbraInt,
        month: dt.month() as AbraInt,
        day: dt.day() as AbraInt,
        hour: dt.hour() as AbraInt,
        minute: dt.minute() as AbraInt,
        second: dt.second() as AbraInt,
        timestamp: timestamp.as_second() as f64
            + timestamp.subsec_nanosecond() as f64 / 1_000_000_000.0,
    }
}

fn civil_to_datetime(dt: civil::DateTime) -> Option<DateTime> {
    let utc = dt.to_zoned_datetime(TimeZone::UTC).ok()?;
    Some(zoned_to_datetime(utc))
}

pub fn now_utc() -> DateTime {
    zoned_to_datetime(Timestamp::now().to_zoned_datetime(TimeZone::UTC))
}

pub fn now_local() -> DateTime {
    zoned_to_datetime(ZonedDateTime::now())
}

pub fn from_timestamp(timestamp: f64) -> DateTime {
    let secs = timestamp.floor() as i64;
    let nanos = ((timestamp - timestamp.floor()) * 1_000_000_000.0) as i32;
    let dt = Timestamp::new(secs, nanos).unwrap_or(Timestamp::UNIX_EPOCH);
    zoned_to_datetime(dt.to_zoned_datetime(TimeZone::UTC))
}

pub fn make_datetime(
    year: AbraInt,
    month: AbraInt,
    day: AbraInt,
    hour: AbraInt,
    minute: AbraInt,
    second: AbraInt,
) -> Option<DateTime> {
    let dt = civil::DateTime::new(
        year.try_into().ok()?,
        month.try_into().ok()?,
        day.try_into().ok()?,
        hour.try_into().ok()?,
        minute.try_into().ok()?,
        second.try_into().ok()?,
        0,
    )
    .ok()?;
    civil_to_datetime(dt)
}

fn datetime_to_civil(dt: &DateTime) -> civil::DateTime {
    let date = civil::Date::new(
        dt.year.try_into().unwrap_or(i16::MAX),
        dt.month.try_into().unwrap_or(i8::MAX),
        dt.day.try_into().unwrap_or(i8::MAX),
    )
    .unwrap_or(civil::date(1970, 1, 1));
    let time = civil::Time::new(
        dt.hour.try_into().unwrap_or(i8::MAX),
        dt.minute.try_into().unwrap_or(i8::MAX),
        dt.second.try_into().unwrap_or(i8::MAX),
        0,
    )
    .unwrap_or(civil::Time::midnight());
    civil::DateTime::from_parts(date, time)
}

pub fn format(dt: DateTime, fmt: String) -> String {
    datetime_to_civil(&dt).strftime(&fmt).to_string()
}

pub fn parse(s: String, fmt: String) -> Option<DateTime> {
    let dt = civil::DateTime::strptime(&fmt, &s).ok()?;
    civil_to_datetime(dt)
}

pub fn weekday_of(dt: DateTime) -> String {
    datetime_to_civil(&dt).strftime("%A").to_string()
}
