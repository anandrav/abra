/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use abra_core::vm::AbraInt;
use base64::prelude::*;

use super::{from_bytes, to_bytes};

pub fn string_to_bytes(s: String) -> Vec<AbraInt> {
    from_bytes(s.as_bytes())
}

pub fn bytes_to_string(bytes: Vec<AbraInt>) -> Result<String, String> {
    String::from_utf8(to_bytes(bytes)).map_err(|e| e.to_string())
}

pub fn hex_encode(bytes: Vec<AbraInt>) -> String {
    hex::encode(to_bytes(bytes))
}

pub fn hex_decode(s: String) -> Result<Vec<AbraInt>, String> {
    hex::decode(s).map(|b| from_bytes(&b)).map_err(|e| e.to_string())
}

pub fn base64_encode(bytes: Vec<AbraInt>) -> String {
    BASE64_STANDARD.encode(to_bytes(bytes))
}

pub fn base64_decode(s: String) -> Result<Vec<AbraInt>, String> {
    BASE64_STANDARD
        .decode(s.as_bytes())
        .map(|b| from_bytes(&b))
        .map_err(|e| e.to_string())
}
