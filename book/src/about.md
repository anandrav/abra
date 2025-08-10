# About Abra

The primary goal of Abra is to be the most **user-friendly** programming language.

More specifically, Abra is optimized for these use cases:

1. Giving beginner programmers a gentle introduction to writing code
2. Allowing experienced programmers to prototype quickly

Abra does this through the combination of these features:

- a strong static type system with error messages that guide the user
- a garbage collector to remove the mental overhead of manually freeing memory or passing around allocators or writing
  lifetime annotations

Abra is not the only language to have a type system and a garbage collector. Some others include:

- OCaml
- Haskell
- TypeScript
- Java
- C#

However, Abra is distinct from more mainstream choices like TypeScript, Java, C# because it has powerful
Hindley-Milner-style type inference.
Abra is distinct from OCaml because it has ad-hoc polymorphism.
Abra is distinct from Haskell because it is not a pure, lazy functional language with monadic IO.

Abra is not optimized for these use cases and does not aim to be:

- graphics
- operating systems
- embedded systems