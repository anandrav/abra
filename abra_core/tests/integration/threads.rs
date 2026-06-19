/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::helper::expect_value;

#[test]
fn threads_and_channels() {
    let src = r#"
let sender: channel<int> = channel()
let receiver: channel<int> = channel()

task {
    for _ in 10 {
        let n = sender.read()
        receiver.write(n * 2)
    }
}

for i in 10 {
    sender.write(i)
}

var sum = 0
for _ in 10 {
   sum += receiver.read()
}

sum
"#;
    expect_value(src, 90);
}

#[test]
fn threads_and_channels_capture_int() {
    let src = r#"
let sender: channel<int> = channel()
let receiver: channel<int> = channel()

let n = 10

task {
    for _ in n {
        let n = sender.read()
        receiver.write(n * 2)
    }
}

for i in n {
    sender.write(i)
}

var sum = 0
for _ in n {
   sum += receiver.read()
}

sum
"#;
    expect_value(src, 90);
}
