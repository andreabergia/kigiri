# Kigiri Compiler Improvement Plan

## Overview

This document outlines a comprehensive improvement plan for the Kigiri compiler based on analysis of the current
codebase. The plan addresses code quality, performance optimization, and development experience improvements.

## Current State Analysis

- **Codebase Size**: ~7,820 lines of Rust code
- **Test Coverage**: 95% line coverage with 187 tests (Excellent!)
- **Architecture**: 4-crate workspace with clean phase separation
- **Dependencies**: Modern, minimal dependency footprint

## Strengths to Maintain

- **Excellent test coverage** (95% line coverage)
- **Clean workspace structure** with logical crate separation
- **Phase-based compilation model** with proper AST parametrization
- **Modern dependencies** and workspace management
- **Comprehensive LLVM integration tests** with JIT execution

## Improvement Areas

### 1. Code Quality & Error Handling (High Priority)

#### Current Issues

- **Inconsistent error handling** - ✅ **Parser module complete**, remaining in other modules
- TODOs present in 4 files indicating incomplete features

**Note**: `unwrap()`, `expect()`, and `panic!` calls in test code are considered acceptable and are excluded from this
improvement plan.

#### Action Items

- [x] **Replace `unwrap()` calls in parser module (production code only)** ✅
    - ✅ Converted parser to use `Result` propagation throughout
    - ✅ Added custom `ParseError` enum with `thiserror`
    - ✅ Replaced all 32 panic-prone `unwrap()`/`expect()` calls in production code
    - ✅ Maintained meaningful error messages with context
- [x] **Replace remaining `unwrap()` calls in other modules (production code only)** ✅ **COMPLETE**
    - [x] **Semantic analysis module error handling** ✅ **COMPLETE**
        - ✅ Replaced `expect()` in `next_symbol_id()` with proper error handling
        - ✅ Updated all callers to handle `Result` types properly
        - ✅ No `panic!` calls remain in production code (2 `panic!` calls are in test code, which is acceptable)
    - [x] **Codegen module error handling** ✅ **COMPLETE**
        - ✅ Created `CodegenError::InternalError` enum with `thiserror`
        - ✅ Replaced all 15 `expect()` and `panic!()` calls in production code
        - ✅ Updated `build_ir_module` and all IR creation methods to return `Result`
        - ✅ Added proper error propagation throughout codegen pipeline
        - ✅ Updated all callers in backend_llvm and tests
        - ✅ All 186 tests continue to pass
    - [x] **Backend LLVM module error handling** ✅ **COMPLETE**
        - ✅ Simplified `CodeGenError` enum with `Builder` and `InternalError` variants
        - ✅ Replaced all `expect()` and `panic!` calls in production code (17 total)
        - ✅ Added helper functions `safe_resolve_string_id()` and `get_variable()` for consistent error handling
        - ✅ Updated all method signatures to return `Result` types and propagate errors with `?` operator
        - ✅ All error cases use descriptive `InternalError` messages for debugging
        - ✅ All 186 tests continue to pass with full functionality preserved
        - ✅ Code formatting and linting checks pass cleanly
- [x] **Remove `#![allow(unused)]` attributes** ✅
    - Clean up dead code and unused imports
    - Enable stricter linting (`#![deny(unused)]`)
    - Fix all compiler warnings
- [ ] **Address all TODO comments**
    - Complete incomplete features in 4 identified files
    - Document design decisions for remaining TODOs
    - Convert TODOs to GitHub issues if appropriate

### 2. Error Reporting & Diagnostics (Medium Priority)

#### Current State

- ✅ **Parser error handling foundation complete**
    - Custom `ParseError` enum with specific error types
    - Proper `Result` propagation throughout parser
    - Structured error messages with context
- ✅ **Eliminated panic-prone code paths**
    - All critical `unwrap()`/`expect()` calls replaced
    - Parser now returns errors instead of crashing

#### Remaining Action Items

- [ ] **Enhance error reporting system**
    - Add source location tracking (line/column) to all error types
    - Implement error severity levels (Error, Warning, Info)
    - Add helpful diagnostic suggestions
- [ ] **Implement parser error recovery**
    - Continue parsing after errors for better IDE support
    - Collect multiple errors in single compilation pass
    - Improve error message quality with code snippets
- [ ] **Create structured diagnostic framework**
    - Error codes for programmatic handling
    - Consistent error formatting
    - Support for error spans and highlights

### 3. Performance & LLVM Optimization (Medium Priority)

#### Current Issues

- LLVM optimization passes not fully utilized
- Single-threaded compilation pipeline
- No performance benchmarking infrastructure

#### Action Items

- [ ] **Optimize LLVM backend**
    - Enable and configure LLVM optimization passes
    - Benchmark compilation performance
    - Profile memory usage and optimize allocations
- [ ] **Add performance benchmarking**
    - Use `criterion` for micro-benchmarks
    - End-to-end compilation benchmarks
    - Track performance regressions
- [ ] **Consider parallel compilation**
    - Parallelize independent compilation phases
    - Thread-safe data structures where beneficial
    - Measure actual performance gains

### 5. Testing Enhancements (Low Priority)

#### Current Strengths

- Excellent 95% line coverage
- Comprehensive test suite with 187 tests
- Good use of snapshot testing with `insta`

#### Optional Improvements

- [ ] **Property-based testing** using `proptest`
    - Parser robustness with random inputs (optional)
    - AST transformation invariants testing
- [ ] **Fuzzing infrastructure** using `cargo-fuzz`
    - Parser crash detection (nice-to-have)
    - Complement existing excellent coverage

## Implementation Timeline

### Phase 1: Code Quality Foundation (Weeks 1-2) ✅ **COMPLETED**

- ✅ Remove `#![allow(unused)]` and clean dead code
- ✅ **Replace critical `unwrap()` calls in parser module**
    - ✅ Parser completely refactored with robust error handling
    - ✅ All 32 panic-prone calls replaced with proper `Result` types
    - ✅ Added `thiserror`-based error types with structured messages
- [x] **Replace remaining `unwrap()` calls in other modules (production code only)** ✅ **COMPLETE**
    - [x] Semantic analysis module **COMPLETE** - Zero panic-prone calls in production code
    - [x] Codegen module **COMPLETE** - Zero panic-prone calls in production code
    - [x] Backend LLVM module **COMPLETE** - Zero panic-prone calls in production code
- [ ] Address urgent TODOs in semantic analysis and backend

### Phase 2: Error Handling Polish (Weeks 3-4) **IN PROGRESS**

- ✅ **Complete error handling refactoring (All modules)**
    - ✅ Custom `ParseError`, `CodegenError`, and enhanced backend LLVM `CodeGenError` types with `thiserror`
    - ✅ Proper `Result` propagation throughout all crates
    - ✅ Extended to semantic analysis, codegen, and backend LLVM modules
    - ✅ Backend LLVM module error handling complete
- [ ] **Enhance error reporting with source locations**
    - [ ] Add line/column tracking to parser errors
    - [ ] Include code snippets in error messages
- [ ] **Implement parser error recovery**
    - [ ] Continue parsing after syntax errors
    - [ ] Collect multiple errors in single pass
- [ ] **Create structured diagnostic framework**
    - [ ] Error codes and consistent formatting

### Phase 3: Performance Optimization (Weeks 5-6)

- Optimize LLVM backend with optimization passes
- Add performance benchmarking infrastructure
- Profile memory usage and optimize allocations

### Phase 4: Advanced Features (Optional)

- Property-based testing (if needed)
- Parallel compilation (if beneficial)
- Incremental compilation support
- Advanced IDE support features

## Success Metrics

- **Code Quality**: ✅ **All modules**: Zero `unwrap()` calls in production code completed across all four crates
- **Error Handling**: ✅ **All modules**: Robust error handling with structured types across parser, semantic analysis, codegen, and backend LLVM
- **Performance**: Measurable LLVM optimization improvements
- **Development**: Clean `cargo clippy` with strict lints enabled
- **Maintainability**: All TODOs resolved or tracked as issues

## Dependencies & Tools

### New Dependencies (Minimal Additions)

- ✅ `thiserror` - Custom error types (added to all modules: parser, semantic analysis, codegen, backend LLVM)
- `criterion` - Performance benchmarking
- `anyhow` - Enhanced error context (optional)
- `tracing` - Structured logging (if needed)

## Risk Assessment

**Low Risk**

- Development tooling (external to codebase)
- Performance benchmarking (measurement only)

**Medium Risk**

- Error handling refactoring (API surface changes)
- LLVM optimization (potential behavior changes)

**High Risk**

- Parser error recovery (semantic behavior changes)
- Major architectural changes (not recommended given current quality)

## Notes

This plan recognizes that the Kigiri compiler already has excellent foundations, particularly in testing. The focus is
on polishing code quality, enhancing developer experience, and optimizing performance rather than major architectural
changes. The high test coverage provides confidence for safe refactoring and improvements.

