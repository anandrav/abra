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

pub fn string_split(s: String, delimiter: String) -> Vec<String> {
    s.split(&delimiter).map(String::from).collect()
}

pub fn string_trim(s: String) -> String {
    s.trim().to_string()
}

pub fn string_trim_start(s: String) -> String {
    s.trim_start().to_string()
}

pub fn string_trim_end(s: String) -> String {
    s.trim_end().to_string()
}

pub fn string_starts_with(s: String, prefix: String) -> bool {
    s.starts_with(&*prefix)
}

pub fn string_ends_with(s: String, suffix: String) -> bool {
    s.ends_with(&*suffix)
}

pub fn string_contains(s: String, substring: String) -> bool {
    s.contains(&*substring)
}

pub fn string_replace(s: String, old: String, new: String) -> String {
    s.replace(&*old, &new)
}

pub fn string_find(s: String, substring: String) -> Option<AbraInt> {
    s.find(&*substring).map(|i| i as AbraInt)
}

pub fn string_repeat(s: String, n: AbraInt) -> String {
    s.repeat(n as usize)
}

pub fn string_pad_left(s: String, width: AbraInt, pad: String) -> String {
    let width = width as usize;
    let len = s.chars().count();
    if len >= width {
        return s;
    }
    let pad_char = pad.chars().next().unwrap_or(' ');
    let padding: String = std::iter::repeat_n(pad_char, width - len).collect();
    format!("{}{}", padding, s)
}

pub fn string_pad_right(s: String, width: AbraInt, pad: String) -> String {
    let width = width as usize;
    let len = s.chars().count();
    if len >= width {
        return s;
    }
    let pad_char = pad.chars().next().unwrap_or(' ');
    let padding: String = std::iter::repeat_n(pad_char, width - len).collect();
    format!("{}{}", s, padding)
}

pub fn string_join(arr: Vec<String>, sep: String) -> String {
    arr.join(&sep)
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
