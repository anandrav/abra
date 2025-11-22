/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use abra_core::vm::AbraInt;
use rand::Rng;

pub fn random_float(min: f64, max: f64) -> f64 {
    let mut rng = rand::rng();
    rng.random_range(min..max)
}

pub fn random_int(min: AbraInt, max: AbraInt) -> AbraInt {
    let mut rng = rand::rng();
    rng.random_range(min..max)
}
