# https://github.com/casey/just

default: build fmt test lint

build:
    cargo build

test:
    RUST_LOG=trace cargo nextest run

test-verbose:
    RUST_LOG=trace cargo nextest run --no-capture

lint:
    cargo fmt --all --check
    cargo clippy --fix --allow-dirty --allow-staged -- -W clippy::all

clean:
    cargo clean
    cargo llvm-cov clean

find-unused-dependencies:
    cargo +nightly udeps --all-targets

fmt:
    cargo fmt --all

insta:
    cargo insta review

audit:
    cargo audit

audit-fix:
    cargo audit fix --dry-run

coverage:
    cargo llvm-cov nextest

coverage-html:
    cargo llvm-cov nextest --html

coverage-lcov:
    cargo llvm-cov nextest --lcov --output-path coverage.info
