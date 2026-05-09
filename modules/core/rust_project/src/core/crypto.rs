/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use abra_core::vm::AbraInt;
use hmac::{Hmac, KeyInit, Mac};
use sha2::{Digest, Sha256};

use super::{from_bytes, to_bytes};

pub fn sha256(data: Vec<AbraInt>) -> Vec<AbraInt> {
    let hash = Sha256::digest(to_bytes(data));
    from_bytes(&hash)
}

pub fn hmac_sha256(key: Vec<AbraInt>, msg: Vec<AbraInt>) -> Vec<AbraInt> {
    type HmacSha256 = Hmac<Sha256>;
    let mut mac = HmacSha256::new_from_slice(&to_bytes(key))
        .expect("HMAC accepts keys of any length");
    mac.update(&to_bytes(msg));
    from_bytes(&mac.finalize().into_bytes())
}
