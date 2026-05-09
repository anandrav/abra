/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use abra_core::vm::AbraInt;
use base64::prelude::*;

use super::{from_bytes, to_bytes};

pub fn bytes_from_string(s: String) -> Vec<AbraInt> {
    from_bytes(s.as_bytes())
}

pub fn string_from_bytes(bytes: Vec<AbraInt>) -> Result<String, String> {
    String::from_utf8(to_bytes(bytes)).map_err(|e| e.to_string())
}

pub fn hex_encode(bytes: Vec<AbraInt>) -> String {
    hex::encode(to_bytes(bytes))
}

pub fn hex_decode(s: String) -> Result<Vec<AbraInt>, String> {
    hex::decode(s).map(|b| from_bytes(&b)).map_err(|e| e.to_string())
}

pub fn base64_encode(bytes: Vec<AbraInt>, url_safe: bool, pad: bool) -> String {
    let b = match (url_safe, pad) {
        (false, true) => &BASE64_STANDARD,
        (false, false) => &BASE64_STANDARD_NO_PAD,
        (true, true) => &BASE64_URL_SAFE,
        (true, false) => &BASE64_URL_SAFE_NO_PAD,
    };
    b.encode(to_bytes(bytes))
}

pub fn base64_decode(s: String, url_safe: bool, pad: bool) -> Result<Vec<AbraInt>, String> {
    let b = match (url_safe, pad) {
        (false, true) => &BASE64_STANDARD,
        (false, false) => &BASE64_STANDARD_NO_PAD,
        (true, true) => &BASE64_URL_SAFE,
        (true, false) => &BASE64_URL_SAFE_NO_PAD,
    };
    b.decode(s.as_bytes())
        .map(|b| from_bytes(&b))
        .map_err(|e| e.to_string())
}
