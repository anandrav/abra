# About Abra

The primary goal of Abra is to be a **user-friendly** programming language.

More specifically, Abra is optimized for these use cases:

1. Giving beginner programmers a gentle introduction to writing code
2. Allowing experienced programmers to prototype quickly
3. Easily embed code inside a video game or game engine

Abra does this through the combination of these features:

- a strong static type system with error messages that prevent the user from making mistakes
- a garbage collector to remove the mental overhead of manually freeing memory, passing around allocators, writing lifetime annotations, or worrying about reference-count cycles.
- a small stack-based virtual machine made available through a library with a simple C API for reading/writing values
- lightweight syntax and minimal boilerplate. Semicolons and commas are often optional

Abra is not the only language to have a type system and a garbage collector. Some others include:

- OCaml
- Haskell
- TypeScript
- Java
- C#
- Go

However, Abra is distinct from more mainstream choices like TypeScript, Java, and C# because it has Hindley-Milner-style type inference, and considerably less boilerplate.
Abra is distinct from OCaml because it has ad-hoc polymorphism.
Abra is distinct from Haskell because it is not a pure, lazy functional language with monadic IO. Abra is distinct from Go because Go does not have algebraic data types or polymorphism.
Abra is distinct from Lua, a popular choice for game scripting, because Abra has a strong static type system.

Abra isn't necessarily a better choice than these other languages. For many use cases, it would be much better to just use something like TypeScript or C#. These comparisons are meant to illustrate Abra's unique advantages for particular projects and for novice programmers.

Abra is not suitable for these use cases and does not aim to be:
- low-level graphics programming
- operating systems
- embedded systems