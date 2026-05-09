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
let line = readline()        // read a line from stdin
let args = get_args()        // command-line arguments as array<string>
```

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

## core/exec

Run external processes. There are simple one-liners and a builder for more control (arguments with spaces, stdin, pipelines).

```
use core/exec

// Quick: run via the shell
let out = run_sh("ls | wc -l")!
println(out.stdout.trim())

// Builder: pipe input through a command
let out = exec("cat").stdin("a\nb\nc\n").pipe("wc", ["-l"]).run()!
println(out.stdout.trim())   // 3
```

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
