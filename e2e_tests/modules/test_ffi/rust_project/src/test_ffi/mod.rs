/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
use crate::ffi::test_ffi::*;
use abra_core::vm::AbraInt;

pub fn pass_int(i: AbraInt) -> AbraInt {
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

pub fn pass_tuple(t: (bool, AbraInt, String)) -> (bool, AbraInt, String) {
    t
}

pub fn pass_option(o: Option<String>) -> Option<String> {
    o
}

pub fn pass_array(a: Vec<AbraInt>) -> Vec<AbraInt> {
    a
}

pub fn pass_nested_array(a: Vec<Vec<String>>) -> Vec<Vec<String>> {
    a
}

pub fn pass_result_struct(r: Result<MyStruct, MyEnum>) -> Result<MyStruct, MyEnum> {
    r
}

pub fn pass_multi_params(
    programs: Vec<String>,
    all_args: Vec<Vec<String>>,
    stdin: Option<String>,
) -> String {
    format!(
        "programs={:?} all_args={:?} stdin={:?}",
        programs, all_args, stdin
    )
}

pub fn pass_two_arrays(
    programs: Vec<String>,
    all_args: Vec<Vec<String>>,
) -> String {
    format!(
        "programs={:?} all_args={:?}",
        programs, all_args
    )
}

pub fn pass_nested_and_option(
    all_args: Vec<Vec<String>>,
    stdin: Option<String>,
) -> String {
    format!(
        "all_args={:?} stdin={:?}",
        all_args, stdin
    )
}

pub fn pass_array_and_option(
    programs: Vec<String>,
    stdin: Option<String>,
) -> String {
    format!(
        "programs={:?} stdin={:?}",
        programs, stdin
    )
}
