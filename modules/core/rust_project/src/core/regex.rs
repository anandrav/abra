/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use abra_core::vm::AbraInt;
use regex::Regex;

use crate::ffi::core::regex::Match;

pub fn matches(s: String, pattern: String) -> bool {
    let Ok(re) = Regex::new(&pattern) else {
        return false;
    };
    re.is_match(&s)
}

pub fn find(s: String, pattern: String) -> Option<Match> {
    let re = Regex::new(&pattern).ok()?;
    let m = re.find(&s)?;
    Some(Match {
        text: m.as_str().to_string(),
        start: m.start() as AbraInt,
        end: m.end() as AbraInt,
    })
}

pub fn find_all(s: String, pattern: String) -> Vec<Match> {
    let Ok(re) = Regex::new(&pattern) else {
        return Vec::new();
    };
    re.find_iter(&s)
        .map(|m| Match {
            text: m.as_str().to_string(),
            start: m.start() as AbraInt,
            end: m.end() as AbraInt,
        })
        .collect()
}

pub fn replace(s: String, pattern: String, replacement: String) -> String {
    let Ok(re) = Regex::new(&pattern) else {
        return s;
    };
    re.replace_all(&s, replacement.as_str()).into_owned()
}

pub fn replace_first(s: String, pattern: String, replacement: String) -> String {
    let Ok(re) = Regex::new(&pattern) else {
        return s;
    };
    re.replace(&s, replacement.as_str()).into_owned()
}

pub fn split(s: String, pattern: String) -> Vec<String> {
    let Ok(re) = Regex::new(&pattern) else {
        return vec![s];
    };
    re.split(&s).map(|part| part.to_string()).collect()
}

pub fn captures(s: String, pattern: String) -> Option<Vec<Option<String>>> {
    let re = Regex::new(&pattern).ok()?;
    let caps = re.captures(&s)?;
    let groups: Vec<Option<String>> = (0..caps.len())
        .map(|i| caps.get(i).map(|m| m.as_str().to_string()))
        .collect();
    Some(groups)
}

pub fn named_captures(s: String, pattern: String) -> Option<Vec<(String, String)>> {
    let re = Regex::new(&pattern).ok()?;
    let caps = re.captures(&s)?;
    let pairs: Vec<(String, String)> = re
        .capture_names()
        .flatten()
        .filter_map(|name| {
            caps.name(name)
                .map(|m| (name.to_string(), m.as_str().to_string()))
        })
        .collect();
    if pairs.is_empty() {
        None
    } else {
        Some(pairs)
    }
}
