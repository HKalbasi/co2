# CO2

## Rewrite a C project in Rust

1. Convert it to a co2 project
2. Use Rust dependencies instead of C
  1. Use Rust std instead of libc
  2. Use crates.io instead of hand coded things
  3. Use Rust wrappers of C dependencies instead of themself.
3. Split your project into multiple crates
  1. Make the public API of each crate minimal and idiomatic in Rust
4. Rewrite each crate into Rust, one by one.
  1. Use tests to keep the behavior stable in each rewrite.