/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

pub(crate) mod random;
pub(crate) mod strings;
pub(crate) mod time;

pub(crate) mod fs;

pub(crate) mod exec;

pub(crate) mod env;

pub(crate) mod regex;

pub(crate) mod http;

pub(crate) mod crypto;
pub(crate) mod encoding;

use abra_core::vm::AbraInt;

// Convert Abra `array<int>` to bytes. Each element must be in 0..=255.
pub(crate) fn to_bytes(v: Vec<AbraInt>) -> Vec<u8> {
    v.into_iter()
        .map(|n| {
            assert!(
                (0..=255).contains(&n),
                "byte value out of range: {n} (must be 0..=255)"
            );
            n as u8
        })
        .collect()
}

pub(crate) fn from_bytes(b: &[u8]) -> Vec<AbraInt> {
    b.iter().map(|&x| x as AbraInt).collect()
}
