# Standard Library

Abra ships with a small collection of modules under `core/` and `ard/`. Bring a module into scope with `use`:

```
use core/strings
use core/map
use ard/term
```

A few things — the most fundamental types, interfaces, and functions — are always available without `use`. These come from the **prelude**, which is implicitly imported into every Abra file.

## Prelude

### Built-in functions

The prelude provides basic I/O and program control:

```
println("hello")             // print with newline (also: print, panic, assert)
let args = get_args()        // command-line arguments as array<string>
```

Reading stdin is provided by `core/io`.

### Built-in types

`option<T>` represents a value that might be missing; `result<T, E>` represents a value that might be an error. Both are heavily used by the standard library:

```
let n: option<int> = "42".to_int()    // .some(42) or .none
let r: result<string, FsError> = read("file.txt")
```

`range` is a half-open numeric interval, used in `for` loops and slicing:

```
for i in range(1, 10) { println(i) }   // 1 through 9
```

### Built-in interfaces

These power most of Abra's operators. You'll usually use them implicitly, by writing `+` or `==`. To make your own type work with these operators, implement the corresponding interface.

| Interface  | Powers                       | Notes                                     |
|------------|------------------------------|-------------------------------------------|
| `Num`      | `+` `-` `*` `/` `^`          | Implemented for `int` and `float`         |
| `Equal`    | `==` `!=`                    |                                           |
| `Ord`      | `<` `<=` `>` `>=`            |                                           |
| `Hash`     | (used by map and set keys)   |                                           |
| `Clone`    |                              | Deep-copy a value                         |
| `ToString` | `..` and `print`/`println`   | Convert any value to a string             |
| `Unwrap`   | `!`                          | Pull value out of `option` or `result`    |
| `Try`      | `?`                          | Early-return on `none` / `err`            |
| `Index`    | `x[i]` and `x[i] = v`        | Bracket access for arrays, maps, etc.    |
| `Iterable` | `for x in y`                 | Lets a type be used in a `for` loop       |

### Array methods

Arrays come with a useful set of methods built in. Most are obvious from their names:

```
let xs = [3, 1, 4, 1, 5, 9, 2, 6]

xs.len()                  // 8
xs.contains(4)            // true
xs.find(5)                // .some(4) — index of first match
xs.sort()                 // in-place, requires Ord
xs.push(7)
xs.pop()

let zeros = array.filled(0, 5)         // [0, 0, 0, 0, 0]
xs.sort_by((a, b) -> a > b)            // sort descending
```

## core/strings

String manipulation: slicing, splitting, searching, trimming, case conversion, and parsing numbers.

```
use core/strings

let csv = "  alice, bob, carol  "
let names = csv.trim().split(",")
for name in names {
    println(name.trim().to_upper())
}
// ALICE
// BOB
// CAROL

let n = "42".to_int()!     // parse as int
```

## core/map

Hash map with separate chaining. Keys must implement `Hash` and `Equal`. Bracket syntax (`m[k]`, `m[k] = v`) works in addition to `insert`/`get`.

```
use core/map

let counts: map<string, int> = map.new()
for word in ["apple", "banana", "apple", "cherry", "apple"] {
    let n = match counts.try_get(word) {
        .some(c) -> c
        .none -> 0
    }
    counts[word] = n + 1
}
println(counts["apple"])   // 3
```

## core/set

Hash set built on `core/map`. Useful for fast membership checks and deduplication. Element type must implement `Hash` and `Equal`.

```
use core/set

let seen: set<int> = set.new()
let unique = []
for n in [1, 2, 2, 3, 1, 4] {
    if not seen.contains(n) {
        seen.insert(n)
        unique.push(n)
    }
}
println(unique)   // [ 1, 2, 3, 4 ]
```

## core/math

Small grab-bag: absolute value, generic `min`/`max`, integer bounds.

```
use core/math

let n = (-5).abs()             // 5
let m = max(10, 20)            // 20
let bound = int_max()          // 9223372036854775807
```

## core/linked_list

An immutable singly-linked list with the usual functional combinators (`map`, `filter`, `fold`, `reverse`). Useful for recursive algorithms and small functional programs.

```
use core/linked_list

let xs = list.from_array([1, 2, 3, 4, 5])
let evens_doubled = xs.filter(x -> x % 2 == 0).map(x -> x * 2)
println(evens_doubled)   // [ 4, 8 ]
```

## core/fs

File system operations: read and write files, manage directories, query metadata. Most functions return `result<T, FsError>` so you can use `?` to propagate failures.

```
use core/fs

fn copy_if_missing(src: string, dest: string) -> result<void, FsError> {
    if exists(dest)? {
        return .ok(nil)
    }
    let contents = read(src)?
    write(dest, contents)
}
```

## core/env

Read and write environment variables.

```
use core/env

let home = get_var("HOME")
set_var("MY_FLAG", "1")
```

## core/http

HTTP requests return `result<Response, HttpError>`. `Response` contains `status: int`, `body: string`, and `headers: array<(string, string)>`.

```
use core/http
use core/json

let response = get('https://example.com/search', query = [('q', 'cats & dogs')], headers = [('Authorization', 'Bearer token')], timeout = 10.0)!.check_status()!
println(response.status)
println(response.body)

let payload = JsonValue.object()
payload['message'] = .Str('hello')
let sent = post_json('https://example.com', payload, headers = [('X-Custom', 'value')])!
let updated = request('PUT', 'https://example.com', body = 'updated text').send()!
```

`get(url)`, `post(url, body = '')`, and `post_json(url, value)` provide the common requests. Each accepts `headers = []`, `query = []`, and `timeout = 30.0` as named arguments. Headers and query parameters are arrays of `(name, value)` string pairs. Query values are URL-encoded and appended to any existing query; repeated keys and empty values are supported. Pass original values, without pre-encoding them. Timeouts are positive, finite seconds and cover sending the request and reading its body.

`request(method, url)` constructs a `Request` and accepts `headers = []`, `query = []`, `body = ''`, and `timeout = 30.0` as named arguments. `.header(name, value)`, `.body(text)`, and `.json_body(value)` also set the request data; `.send()` performs the request. JSON helpers add `Content-Type: application/json` only when no Content-Type is present, comparing header names case-insensitively.

`response.ok()` means the status is 200–299. HTTP 4xx/5xx statuses still return `.ok(Response)`; `?` and `!` handle transport errors. `response.check_status()` returns `result<Response, HttpError>`: 2xx returns the response, and any other status returns `.Other('HTTP <status>: <body>')`. Inside a function returning a compatible result, use `get(url)?.check_status()?` to propagate both transport and status errors. `response.header(name)` returns `option<string>` using a case-insensitive lookup, and `response.json()` returns `result<JsonValue, string>`.

`HttpError` is `.ConnectionFailed(string)`, `.Timeout(string)`, or `.Other(string)` and implements `ToString`. Invalid URLs, methods, headers, and timeouts return errors. Response bodies are read completely as text.

For byte streaming, use `get_stream(url, timeout = 30.0, headers = [], query = [])` or `request(...).send_streaming()`. These return `result<StreamingResponse, HttpError>` as soon as the status and headers are available. `StreamingResponse` has `status`, `headers`, and `body: HttpStream`, plus `ok()`, `header(name)`, `check_status()`, and `close()`.

```abra
fn show_chunks(url: string) -> result<void, HttpError> {
    let response = get_stream(url)?.check_status()?
    while true {
        match response.body.read_chunk()? {
            .none -> break
            .some(bytes) -> println(bytes.len())
        }
    }
    response.close()?
    .ok(nil)
}
```

`body.read_chunk(max_bytes = 8192, timeout = .some(30.0))` returns `result<option<array<int>>, HttpError>`. Each `.some(bytes)` contains between 1 and `max_bytes` bytes, with integer values 0–255; `.none` means EOF. Reads return available data without waiting to fill `max_bytes`. Chunk boundaries can split a UTF-8 character or a protocol message, so assemble complete text or frames before decoding.

For streaming, the request's `timeout` covers opening the connection through receiving response headers. Each read has its own timeout in positive, finite seconds; `timeout = .none` waits indefinitely. A read timeout returns `.Timeout`, rather than an empty chunk. EOF and body read errors release the stream. Invalid read arguments return errors and leave the stream usable.

Call `response.close()` or `response.body.close()` when stopping early, including before propagating errors from processing received bytes. Closing cancels pending reads and releases the response; repeated closes succeed. Reads after EOF or close return an error. `StreamingResponse.check_status()` closes non-2xx responses and returns `.Other('HTTP <status>')` without reading the error body. To inspect that body, check `status` yourself and read it before closing.

## core/exec

`exec()` accepts a command string with spaces, single/double quotes, and backslash escapes. It launches the executable directly; shell expansion, redirects, and shell operators belong in `run_sh()`.

```
use core/exec
use core/strings

let out = exec('git status').run()!
let out = exec('git commit -m "fix loop crash"').run()!

// Dynamic arguments remain single arguments, including spaces or quotes.
let url = 'https://example.com/project.git'
let out = exec('git clone').arg(url).run()!

let out = exec('cat').stdin('a\nb\nc\n').pipe('wc -l').run()!
println(out.stdout.trim())   // 3

let out = run_sh('ls | wc -l')!
```

`exec(command, args = [], stdin = .Inherit)` constructs a command. `.arg(value)` and `.args(values)` append arguments to its last pipeline stage. `.pipe(command, args = [])` adds a stage.

`InputSource` is `.Pipe`, `.Inherit`, `.Discard`, `.Text(string)`, or `.File(path)`. Inherit uses Abra's stdin; discard supplies EOF. With `spawn()`, `.Pipe` keeps stdin open for later writes. `run()` rejects `.Pipe`; use `.stdin(text)` or `stdin = .Text(text)` to supply its input.

`OutputTarget` is `.Pipe`, `.Inherit`, `.Discard`, or `.File(path, append = false)`. Inherit writes directly to Abra's corresponding output stream. Files are created and truncated by default; `append = true` preserves their contents.

`run(stdout = .Pipe, stderr = .Pipe)` waits and returns `result<Output, ExecError>`. Only piped output is collected into `Output.stdout` and `Output.stderr`. A pipeline returns its final command's exit status and captures stderr from every stage. Signal termination has status `-1`.

A command that starts successfully and exits with a nonzero status still returns `.ok(Output)`. `?` and `!` handle `ExecError`, not the child exit status. Check `out.success()` or `out.status` to detect command failure; `success()` means `status == 0`.

```
exec('git clone').arg(url).run(stdout = .Inherit, stderr = .Inherit)!
exec('builder').run(stdout = .File('build.log'), stderr = .File('errors.log', append = true))!
exec('cat', stdin = .File('input.txt')).run()!
```

`spawn(stdout = .Inherit, stderr = .Inherit)` returns `result<Process, ExecError>` immediately after starting the children. Its `pid` identifies the final pipeline stage. Choose `.Pipe` to read live output chunks:

```
let child = exec('builder').spawn(stdout = .Pipe, stderr = .Pipe)!
var event = child.read_output()!
while event.is_some() {
    match event! {
        .Stdout(text) -> print(text)
        .Stderr(text) -> eprint(text)
    }
    event = child.read_output()!
}
let status = child.wait()!
```

`read_output()` blocks until a stdout/stderr chunk is available and returns `.none` when all piped streams close. Chunks are strings, not necessarily complete lines; stdout and stderr are drained concurrently. Piped output is queued in memory until read, so consume it as it arrives when output is large.

Use `stdin = .Pipe` to send input while a child is running:

```
let child = exec('cat', stdin = .Pipe).spawn()!
child.write_stdin('first\n')!
child.write_stdin('last\n', close = true)!
let status = child.wait()!
```

`write_stdin(text, close = false)` writes the complete string as UTF-8 without adding a newline. Input is sent directly, so no separate flush is needed. `close = true` closes stdin after the write; `close_stdin()` closes it without writing. Closing an already closed stdin succeeds. Writing without a pipe, after closing it, or after the child closes its input returns `ExecError`. The input pipe feeds the first stage of a pipeline.

The methods on `Process` return:

| Method | Return type | Behavior |
| --- | --- | --- |
| `write_stdin(text, close = false)` | `result<void, ExecError>` | Sends text to piped stdin, optionally closing it afterward. |
| `close_stdin()` | `result<void, ExecError>` | Closes piped stdin to send EOF. |
| `read_output()` | `result<option<OutputEvent>, ExecError>` | The next `.Stdout(string)` or `.Stderr(string)` chunk, or `.none` at EOF. |
| `poll()` | `result<option<int>, ExecError>` | `.none` while any stage runs; `.some(status)` once all stages finish. Leaves stdin open. |
| `wait()` | `result<int, ExecError>` | Closes piped stdin, waits for all stages, and returns the final stage's exit status. |
| `kill()` | `result<void, ExecError>` | Terminates the running stages. |

Call `wait()` to reap the children and release the process handle; it discards unread output, and subsequent operations on that handle return an error. Close stdin and read any desired output before waiting if the child needs EOF to finish. After `kill()`, still call `wait()` to release the handle.

`detach(stdout = .Discard, stderr = .Discard)` starts an independent process and returns `result<int, ExecError>` containing its PID. Inherited input becomes EOF; file input is supported, but text input and piped input/output are rejected. On Unix the child starts a new session and ignores terminal hangup; on Windows it starts detached from the console.

```
let pid = exec('worker').detach(
    stdout = .File('worker.log', append = true),
    stderr = .File('worker-errors.log', append = true),
)!
```

`run(command, stdout = .Pipe, stderr = .Pipe)` returns `result<Output, ExecError>` and is a convenience for `exec(command).run(...)`. `run_sh(command, stdout = .Pipe, stderr = .Pipe)` returns the same type and interprets its command through the shell. `command(command)` inherits stdout/stderr and returns `result<int, ExecError>` containing the child exit status, including nonzero statuses. Empty commands, malformed quotes, launch failures, and file errors return `ExecError`.

## core/io

```
use core/io

let name = input(prompt = 'Name: ')
println('Hello, ' .. name)
```

`input(prompt = '') -> string` prints its prompt without a newline, reads one line, and removes its line ending. A blank line returns `''`. EOF or a read error prints a clear message to stderr and exits with status 1, without a panic traceback.

For callers that need to handle EOF and errors, `read_line() -> result<option<string>, IoError>` returns `.ok(.some(line))`, `.ok(.none)` at EOF, or `.err(error)`. A blank line is `.ok(.some(''))`. LF, CRLF, and bare CR endings are removed; a final line without an ending is also returned. Invalid UTF-8 returns `.InvalidData(message)`; other read failures return `.Other(message)`.

```
while true {
    match read_line() {
        .ok(.some(line)) -> println(line)
        .ok(.none) -> break
        .err(error) -> {
            eprintln(error.str())
            exit(1)
        }
    }
}
```

Waiting for stdin suspends only the calling task. Other tasks continue running through the existing foreign-call worker mechanism. Concurrent reads are serialized; use one reader task when line ownership matters.

The old prelude `readline()` host call has been removed. Scripts now import `core/io` and use `input()` or `read_line()`.

## core/net

Unix-domain stream sockets for communication between local processes. This module currently supports Unix systems; other platforms return `SocketError`.

`listen_unix(path, backlog = 128)` creates a `UnixListener`. The socket file has owner-only permissions (`0600`) before listening starts. An existing file or socket is never overwritten. `connect_unix(path)` returns a connected `UnixStream`.

```
use core/net
use core/encoding

let stream = connect_unix('/tmp/worker.sock')!
stream.write_all(bytes_from_string('ping\n'), timeout = .some(5.0))!
let response = stream.read(max_bytes = 4096, timeout = .some(5.0))!
stream.close()!
```

Listener methods:

| Method | Return type | Behavior |
| --- | --- | --- |
| `accept(timeout = .none)` | `result<UnixStream, SocketError>` | Waits for a connection and returns its stream. |
| `close()` | `result<void, SocketError>` | Closes the listener and cancels pending accepts. Leaves the socket file in place. |

Stream methods:

| Method | Return type | Behavior |
| --- | --- | --- |
| `read(max_bytes = 8192, timeout = .none)` | `result<option<array<int>>, SocketError>` | Reads up to `max_bytes` bytes; `.none` means EOF. |
| `write_all(bytes, timeout = .none)` | `result<void, SocketError>` | Writes the entire byte array. Each byte must be from 0 through 255. |
| `shutdown(how = .Both)` | `result<void, SocketError>` | Disables `.Read`, `.Write`, or `.Both` directions. Write shutdown sends EOF while leaving reads available. |
| `close()` | `result<void, SocketError>` | Closes the stream and cancels pending reads and writes. |

Timeouts are optional positive, finite seconds. `.none` waits indefinitely. A timeout leaves the handle usable; a failed `write_all()` may already have sent part of its input. `connect_unix()` uses a blocking connection attempt, like Rust's `UnixStream::connect()`.

Reads return bytes, not messages or decoded text. Chunks can split UTF-8 characters; assemble the needed bytes before calling `core/encoding.string_from_bytes()`. EOF does not close the handle, so the other direction can remain usable after a peer's write shutdown.

Copies of listeners and streams share the same native handle. Coordinate readers and writers across tasks, and close each handle when finished. Closing is idempotent and invalidates every copy of that handle; other operations on closed handles return an error. Socket paths have platform-dependent length limits.

Like Python and Rust, closing a listener leaves its filesystem path behind. Remove it explicitly with `core/fs.remove(path)` when appropriate. `SocketError` distinguishes `NotFound`, `PermissionDenied`, `AddressInUse`, `ConnectionRefused`, `Timeout`, and `Other`; use `e.str()` for its message.

## core/random

Random integers and floats over half-open ranges.

```
use core/random

let roll = random_int(1, 7)         // 1 through 6
let jitter = random_float(0.0, 1.0)
```

## core/time

Wall-clock time, sleep, and a `DateTime` type with `strftime`-style formatting.

```
use core/time

let start = get_time()
sleep(0.5)
println("waited " .. elapsed(start) .. "s")

let now = now_local()
println(format(now, "%Y-%m-%d %H:%M:%S"))
println("today is " .. now.weekday())
```

## core/json

Parse and serialize JSON. Bracket syntax indexes into objects; `.try_get(key)` is the safe alternative.

```
use core/json

let data = parse("""{"name": "Alice", "scores": [10, 20, 30]}""")!
println(data["name"].as_string()!)       // Alice
println(data["scores"].at(1).as_number()!)  // 20.0

// Build a JSON value
let out = JsonValue.object()
out["greeting"] = .Str("hello")
out["count"] = .Number(3.0)
println(stringify_pretty(out))
```

## core/http

A small HTTP client built on top of `core/json`. Convenience functions for `get`/`post`, and a builder for full control.

```
use core/http
use core/json

let resp = get("https://api.example.com/items/42")!
if resp.ok() {
    let item = resp.json()!
    println(item["name"].as_string()!)
}
```

## core/regex

Regular expressions: testing, finding, replacing, splitting, and extracting capture groups. Uses Rust's `regex` engine.

```
use core/regex

let s = "Build #1234 on 2026-05-02"
let m = find(s, "\\d{4}-\\d{2}-\\d{2}")!
println(m.text)   // 2026-05-02

let parts = split("foo, bar,baz , qux", "\\s*,\\s*")
println(parts)    // [ foo, bar, baz, qux ]
```

## core/colors

ANSI escape-code helpers for coloring and styling terminal output. Each function takes any value that implements `ToString`. Compose by nesting.

- Foreground: `black`, `red`, `green`, `yellow`, `blue`, `magenta`, `cyan`, `white`, and `bright_*` versions of each.
- Background: `on_black`, `on_red`, `on_green`, `on_yellow`, `on_blue`, `on_magenta`, `on_cyan`, `on_white`.
- Attributes: `bold`, `dim`, `italic`, `underline`, `reverse`, `strikethrough`.

```
use core/colors

println(red("error: ") .. "could not connect")
println(bold(green("Success!")))
println(on_yellow(black(" WARNING ")))
```

## ard/term

Build text-based interactive programs in the terminal, backed by `crossterm`. Provides raw mode, an alternate screen, drawing and cursor primitives, and a unified event stream covering keys, mouse, and resize. The example programs `snake.abra`, `mandelbrot.abra`, and `game_of_life.abra` are good starting points.

```
use ard/term
use core/time

enable_raw_mode()
enter_alternate_screen()
hide_cursor()
clear()

var quit = false
while not quit {
    mark("press q to quit", 0, 0)
    flush()
    while poll_event(1) {
        match get_event() {
            .Key(key, _) -> match key {
                .Char('q') -> quit = true
                .Esc -> quit = true
                _ -> {}
            }
            .Resize(w, h) -> {} // terminal was resized to w x h
            _ -> {}
        }
    }
    sleep(0.05)
}

show_cursor()
leave_alternate_screen()
disable_raw_mode()
flush()
```

### Types

- `Event = Key(KeyCode, Modifiers) | Mouse(MouseEvent, Modifiers) | Resize(int, int) | Other`
- `KeyCode = Char(string) | Enter | Tab | BackTab | Backspace | Delete | Insert | Esc | Left | Right | Up | Down | Home | End | PageUp | PageDown | Function(int) | Other` — `Function(n)` represents F1 through F12.
- `Modifiers = { ctrl: bool, alt: bool, shift: bool }`
- `MouseButton = LeftButton | RightButton | MiddleButton`
- `MouseEvent = Down(MouseButton, int, int) | Up(MouseButton, int, int) | Drag(MouseButton, int, int) | Move(int, int) | ScrollUp(int, int) | ScrollDown(int, int)` — coordinates are `(x, y)`.

### Functions

- Modes: `enable_raw_mode`, `disable_raw_mode`, `enter_alternate_screen`, `leave_alternate_screen`, `enable_mouse`, `disable_mouse`, `set_title(s)`, `bell()`.
- Events: `poll_event(ms) -> bool`, `get_event() -> Event`.
- Drawing: `clear`, `clear_line`, `clear_to_end_of_line`, `clear_to_end_of_screen`, `mark(s, x, y)`, `flush`.
- Cursor: `hide_cursor`, `show_cursor`, `move_to(x, y)`, `move_up(n)`, `move_down(n)`, `move_left(n)`, `move_right(n)`, `save_cursor`, `restore_cursor`.
- Size: `get_size() -> option<(int, int)>` returns `(cols, rows)`.
