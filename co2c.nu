#!/usr/bin/env nu

const me = path self | path dirname

def --wrapped main [...args] {
    rm ($me)/co2c/src/exp.rs
    touch ($me)/co2c/src/exp.rs
    cargo build -r --manifest-path=($me)/Cargo.toml
    rm -f ./a.out
    RUST_BACKTRACE=1 RUST_LOG=info ^($me)/target/release/co2c ...$args e> ($me)/last_err.txt
}