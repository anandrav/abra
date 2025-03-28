/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ffi::test_ffi::*;

pub fn pass_int(i: i64) -> i64 {
    i
}

pub fn pass_bool(b: bool) -> bool {
    b
}

pub fn pass_void(v: ()) {
    v
}

pub fn pass_string(s: String) -> String {
    s
}

pub fn pass_struct(s: MyStruct) -> MyStruct {
    s
}

pub fn pass_enum(s: MyEnum) -> MyEnum {
    s
}

pub fn pass_tuple(t: (bool, i64, String)) -> (bool, i64, String) {
    t
}

pub fn pass_maybe(m: Result<String, i64>) -> Result<String, i64> {
    m
}

pub fn pass_array(a: Vec<i64>) -> Vec<i64> {
    a
}
