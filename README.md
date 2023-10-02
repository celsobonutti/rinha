# Rinha de Compilers

This is the Lean4 implementation for the compiler contest called Rinha de Compilers.

It's very basic and uses `mathlib` modules whenever possible.

There are some sparse proofs, but that's not a goal for this project.

## Compile target
This project compiles `rinha` files to a `racket` representation, then uses the `racket` compiler runtime.

## Type checker

It implements a modified Algorithm W with support for intersection types, tuples and uncurried functions.
When a type is an intersection (e.g. oneOf [int, string]), the typechecker will allow unifying it with any of the types in the list,
and defers any possible type mismatch to the `racket` runtime, which uses `contracts` to handle that.
