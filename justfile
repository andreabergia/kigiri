# https://github.com/casey/just

default: build test lint

build:
    cargo build

test:
    RUST_LOG=trace cargo nextest run

test-verbose:
    RUST_LOG=trace cargo nextest run --no-capture

lint:
    cargo clippy --fix --allow-dirty --allow-staged -- -W clippy::all

clean:
    cargo clean

find-unused-dependencies:
    cargo +nightly udeps --all-targets
