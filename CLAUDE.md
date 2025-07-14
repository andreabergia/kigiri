# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Development Commands

This project uses `just` as the build tool. Available commands:

- `just` or `just build fmt test lint` - Run the full development workflow
- `just build` - Build the project with `cargo build`
- `just test` - Run tests with `RUST_LOG=trace cargo nextest run`
- `just test-verbose` - Run tests with output capture disabled
- `just fmt` - Format code with `cargo fmt --all`
- `just lint` - Check formatting and run clippy with fixes
- `just clean` - Clean build artifacts
- `just insta` - Review snapshot tests with `cargo insta review`

Note: The project uses `cargo nextest` for testing instead of standard `cargo test`.

## Project Architecture

This is a Rust-based compiler/programming language implementation organized as a workspace with four main crates. The compiler uses LLVM as its backend for native code generation.

### Core Pipeline
The compilation process follows a multi-phase pipeline:

1. **parser** - Lexing and parsing using Pest grammar
   - `grammar.pest` defines the language grammar
   - Produces an AST from source code
   - Entry points: `parse()`, `parse_as_block()`, `parse_as_expression()`

2. **semantic_analysis** - Type checking and semantic validation
   - Two-phase process: declaration collection then type resolution
   - `SemanticAnalyzer` orchestrates the analysis phases
   - Transforms parsed AST to typed AST (`PhaseTypeResolved`)
   - Symbol table management for scopes and variables

3. **codegen** - IR generation from typed AST
   - `ir_builder::build_ir_module()` converts typed AST to intermediate representation
   - Custom IR with basic blocks and instructions
   - Handles control flow and variable management

4. **backend_llvm** - LLVM code generation and compilation
   - `ir_to_llvm()` converts custom IR to LLVM IR
   - Uses inkwell (LLVM 18.1) for Rust-LLVM bindings
   - Leverages LLVM's optimization passes and native code generation
   - Final compilation target for producing executable binaries

### Compilation Phases
The codebase uses a phase-based compilation model where AST nodes are parameterized by compilation phase:
- `PhaseParsed` - Raw parsed AST
- `PhaseTypeResolved` - After semantic analysis with type information

### Testing
- Uses `insta` for snapshot testing
- Tests are organized per crate with some integration tests
- LLVM backend has generated semantic tests

### Key Dependencies
- `pest`/`pest_derive` for parsing
- `inkwell` for LLVM integration (version 0.6.0 with LLVM 18.1)
- `string-interner` for string interning
- `bumpalo` for arena allocation
- `insta` for snapshot testing