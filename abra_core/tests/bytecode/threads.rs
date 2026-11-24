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

#[test]
fn capture_structs_enums_arrays() {
    let src = r#"
type Message = { words: array<array<string>> }

let message: option<Message> = .some(Message([['original']]))
let done: channel<bool> = channel()

task {
    let copied = message!
    copied.words[0][0] = 'changed'
    copied.words[0].push('new')
    done.write(copied.words[0][0] == 'changed' and copied.words[0].len() == 2)
}

let copied_ok = done.read()
let original = message!
copied_ok and original.words[0][0] == 'original' and original.words[0].len() == 1
"#;
    expect_value(src, true);
}

#[test]
fn channel_messages_survive_producer_exit() {
    let src = r#"
let messages: channel<string> = channel()
let done: channel<void> = channel()

task {
    messages.write('hello' .. ' world')
    done.write(nil)
}

done.read()
messages.read()
"#;
    expect_value(src, "hello world");
}
