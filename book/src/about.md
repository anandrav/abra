# About Abra

Abra aims to be the most **user-friendly** programming language.

More specifically, Abra is optimized for these use cases:

1. Giving beginners a gentle introduction to programming
2. Allowing experienced programmers to prototype quickly

Some noteworthy features that support these use cases include:

### Hindley-Milner Type System
Abra is a statically-typed language with Hindley-Milner type inference. Types help programmers avoid bugs by catching errors at compile time. At the same time, type inference saves programmers time by removing the need for type annotations everywhere.

### Garbage Collection
Abra is garbage-collected, so programmers don't have to manually manage memory themselves, and they can save brainpower for other aspects of their program instead.

### Adhoc Polymorphism
In addition, Abra has a concept of "interfaces" which is very similar to "traits" in Rust or "typeclasses" in Haskell. These enable programmers to use the '+' operator on both integers and floats, or print several kinds of datatypes without having to use separate functions for each (print() as opposed to print\_string(), print\_int(), print\_float() etc.)
