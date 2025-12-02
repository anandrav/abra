/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
use abra_core::vm::{AbraFloat, AbraInt};

pub(crate) fn string_len(s: String) -> AbraInt {
    s.len() as AbraInt
}

pub fn string_chars(s: String) -> Vec<String> {
    s.chars().map(String::from).collect()
}

pub fn string_lines(s: String) -> Vec<String> {
    s.lines().map(String::from).collect()
}

pub fn string_slice(s: String, begin: AbraInt, end: AbraInt) -> String {
    s[begin as usize..end as usize].to_string()
}

pub fn string_is_alphabetic(s: String) -> bool {
    s.chars().all(char::is_alphabetic)
}

pub fn string_is_alphanumeric(s: String) -> bool {
    s.chars().all(char::is_alphanumeric)
}

pub fn string_is_numeric(s: String) -> bool {
    s.chars().all(char::is_numeric)
}

pub fn string_to_upper(s: String) -> String {
    s.to_uppercase()
}

pub fn string_to_lower(s: String) -> String {
    s.to_lowercase()
}

pub fn string_to_int(s: String) -> Option<AbraInt> {
    s.parse::<AbraInt>().ok()
}

pub fn string_to_float(s: String) -> Option<AbraFloat> {
    s.parse::<AbraFloat>().ok()
}
