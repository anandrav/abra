# Standard Library

Abra ships with a small collection of modules under `core/` and `ard/`. Bring a module into scope with `use`:

```
use core/strings
use core/map
use ard/term
```

Some functions, types, and interfaces are always available without `use`. These come from the **prelude**, which is implicitly imported into every Abra file.

## Prelude

The prelude defines the most fundamental types and operations. You don't need to import any of these.

### Functions

```
print(x)                  // print without newline
println(x)                // print with newline
panic(msg)                // abort the program with an error
assert(cond, msg)         // panic if condition is false
readline()                // read a line from stdin
get_args()                // command-line arguments as array<string>
range_inclusive(begin, end)   // an inclusive range [begin, end]
```

### Types

```
type option<T> = some(T) | none
type result<T, E> = ok(T) | err(E)
type range = { begin: int, end: int }
type ControlFlow<B, C> = Break(B) | Continue(C)
```

### Interfaces

| Interface     | Purpose                            | Operators it powers       |
|---------------|------------------------------------|---------------------------|
| `Num`         | arithmetic                         | `+`, `-`, `*`, `/`, `^`   |
| `Equal`       | equality                           | `==`, `!=`                |
| `Ord`         | ordering                           | `<`, `<=`, `>`, `>=`      |
| `Hash`        | hashing                            | (used by map/set keys)    |
| `Clone`       | deep copy                          |                           |
| `ToString`    | conversion to string               | `..` and `print`/`println`|
| `Unwrap`      | extract value from container       | `!`                       |
| `Try`         | early-return on failure            | `?`                       |
| `Index`       | bracket-syntax access              | `x[i]` and `x[i] = v`     |
| `Iterable`    | for-loop support                   | `for x in y`              |
| `Iterator`    | iteration protocol                 |                           |

### Array methods

Arrays implement many methods directly in the prelude:

```
arr.len()
arr.is_empty()
arr.push(x)
arr.pop()
arr.swap(i, j)
arr.remove(i)              // swap with last, then pop
arr.clear()
arr.bounds()               // range(0, len)

array.filled(x, n)         // create an array of n copies (requires Clone)

arr.find(x)                // option<int>; requires Equal
arr.contains(x)            // bool;        requires Equal

arr.sort()                 // requires Ord
arr.sort_by(cmp)           // cmp: (T, T) -> bool   (less-than-or-equal)
arr.sort_by_key(key_fn)    // key_fn: T -> U Ord
```

## Modules

### `core/strings`

Adds methods to the `string` type and provides `join`:

```
s.len()
s.chars()                  // array<string>, one char per element
s.lines()                  // split by newlines
s.slice(begin, end)        // substring [begin, end)
s.split(delim)             // array<string>
s.trim()
s.trim_start()
s.trim_end()
s.starts_with(p)
s.ends_with(suf)
s.contains(sub)
s.find(sub)                // option<int>
s.replace(old, new)
s.repeat(n)
s.pad_left(width, pad)
s.pad_right(width, pad)
s.to_upper()
s.to_lower()
s.to_int()                 // option<int>
s.to_float()               // option<float>
s.is_alphabetic()
s.is_alphanumeric()
s.is_numeric()

join(arr, sep)             // join an array<string> into one string
```

### `core/map`

Hash map. Keys must implement `Hash` and `Equal`.

```
let m: map<string, int> = map.new()
m.insert(k, v)
m.get(k)            // panics if missing
m.try_get(k)        // option<V>
m.contains(k)
m.remove(k)         // bool
m.len()
```

`map` also implements `Index`, so `m["alice"] = 100` and `m["alice"]` work.

### `core/set`

Hash set built on top of `core/map`. Element type must implement `Hash` and `Equal`.

```
let s: set<int> = set.new()
s.insert(item)
s.contains(item)
s.remove(item)      // bool
s.len()
```

### `core/math`

```
n.abs()             // works on int and float
int_max()
int_min()
max(a, b)           // generic; requires Ord
min(a, b)
```

### `core/linked_list`

An immutable singly-linked list, useful for recursive algorithms.

```
type list<T> = empty | cons(T, list<T>)

list.from_array(a)
l.fold(f, acc)
l.map(f)
l.for_each(f)
l.filter(f)
l.reverse()
```

### `core/fs`

File system operations. Most functions return `result<T, FsError>`.

```
read(path)
write(path, contents)
append(path, contents)
copy(src, dest)
rename(old, new)
remove(path)
exists(path)

mkdir(path)
mkdir_all(path)
rmdir(path)
rmdir_all(path)
list_dir(path)

is_file(path)
is_dir(path)
file_size(path)
modified_time(path)

join_path(base, child)     // NOT join — that's in core/strings
parent(path)
filename(path)
extension(path)
stem(path)
absolute(path)

glob(pattern)
walk_dir(path)

getcwd()
temp_dir()
temp_file()
```

### `core/env`

```
get_var(key)
set_var(key, value)
```

### `core/exec`

Run external processes.

```
command(s)              // returns exit code; prints stdout/stderr
run(s)                  // splits on spaces; returns result<Output, ExecError>
run_sh(s)               // runs via sh -c; supports pipes/redirects

// Builder for full control:
exec(prog).args([...]).stdin(input).pipe(prog2, [...]).run()
```

`Output` has `stdout`, `stderr`, `status`, and `success()`.

### `core/random`

```
random_int(min, max)        // [min, max)
random_float(min, max)      // [min, max)
```

### `core/time`

```
get_time()                  // seconds since epoch (float)
sleep(seconds)
elapsed(start)              // get_time() - start

// DateTime type
now_utc()
now_local()
from_timestamp(t)
make_datetime(y, mo, d, h, mi, s)   // option<DateTime>
format(dt, fmt)             // strftime: %Y %m %d %H %M %S
parse(s, fmt)
weekday_of(dt)

// DateTime methods
dt.add_seconds(s)
dt.add_days(n)
dt.diff(other)
dt.weekday()
```

### `core/json`

JSON parser and serializer.

```
type JsonValue =
    | Null
    | Bool(bool)
    | Number(float)
    | Str(string)
    | Array(array<JsonValue>)
    | Object(map<string, JsonValue>)

parse(s)                // result<JsonValue, string>
stringify(v)
stringify_pretty(v)

v["key"]                // via Index — panics if missing
v.try_get(key)          // option<JsonValue>
v.at(i)                 // arrays
v.set_at(i, val)
v.push(val)
v.as_string()           // option<string>
v.as_number()           // option<float>
v.as_bool()
v.as_array()
v.as_object()
v.is_null()

JsonValue.object()      // empty object
JsonValue.array()       // empty array
```

### `core/http`

HTTP client.

```
get(url)
post(url, body)
post_json(url, value)

// Builder:
request(method, url).header(k, v).body(s).json_body(v).send()

// Response
resp.ok()               // 200-299
resp.json()             // result<JsonValue, string>
resp.header(name)       // option<string>
```

### `core/regex`

Regex matching, replace, split, captures.

```
matches(s, pattern)
find(s, pattern)            // option<Match>
find_all(s, pattern)
replace(s, pattern, repl)   // $1, $2 for captures
replace_first(s, pattern, repl)
split(s, pattern)
captures(s, pattern)        // option<array<option<string>>>
named_captures(s, pattern)
```

### `core/colors`

ANSI color and style helpers. Each takes any value that implements `ToString`.

```
red(s)  green(s)  yellow(s)  blue(s)  magenta(s)  cyan(s)  white(s)
bold(s) dim(s)  underline(s)
```

### `ard/term`

Build text-based interactive programs in the terminal.

```
enable_raw_mode()
disable_raw_mode()
clear()
flush()                 // call after drawing to update display
hide_cursor()
show_cursor()
mark(s, x, y)           // place a string at the given position
poll_key_event(ms)      // bool — true if a key event is queued
get_key_event()         // KeyCode enum
get_size()              // option<(int, int)>: (width, height)

type KeyCode =
    | Left | Right | Up | Down
    | Char(string) | Esc | Space | Other
```
