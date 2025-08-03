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

#### Action Items

- [x] **Replace `unwrap()` calls in parser module** ✅
    - ✅ Converted parser to use `Result` propagation throughout
    - ✅ Added custom `ParseError` enum with `thiserror`
    - ✅ Replaced all 32 panic-prone `unwrap()`/`expect()` calls in parser
    - ✅ Maintained meaningful error messages with context
- [ ] **Replace remaining `unwrap()` calls in other modules**
    - [ ] Semantic analysis module error handling
    - [ ] Codegen module error handling  
    - [ ] Backend LLVM module error handling
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

### Phase 1: Code Quality Foundation (Weeks 1-2) **PARTIALLY COMPLETED**

- ✅ Remove `#![allow(unused)]` and clean dead code
- ✅ **Replace critical `unwrap()` calls in parser module**
    - ✅ Parser completely refactored with robust error handling
    - ✅ All 32 panic-prone calls replaced with proper `Result` types
    - ✅ Added `thiserror`-based error types with structured messages
- [ ] **Replace remaining `unwrap()` calls in other modules**
    - [ ] Semantic analysis, codegen, and backend modules
- [ ] Address urgent TODOs in semantic analysis and backend

### Phase 2: Error Handling Polish (Weeks 3-4) **IN PROGRESS**

- ✅ **Complete error handling refactoring (Parser module)**
    - ✅ Custom `ParseError` types with `thiserror`
    - ✅ Proper `Result` propagation throughout
    - [ ] Extend to semantic analysis and codegen modules
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

- **Code Quality**: ✅ **Parser module only**: Zero `unwrap()` calls completed, others remain
- **Error Handling**: ✅ **Parser module**: Robust error handling with structured types
- **Performance**: Measurable LLVM optimization improvements
- **Development**: Clean `cargo clippy` with strict lints enabled
- **Maintainability**: All TODOs resolved or tracked as issues

## Dependencies & Tools

### New Dependencies (Minimal Additions)

- ✅ `thiserror` - Custom error types (already added to parser)
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

## Recent Progress Update

**Parser Error Handling Complete (January 2025)**

The parser module has been successfully refactored with comprehensive error handling:

- ✅ **Eliminated parser panic risks**: Replaced 32 `unwrap()`/`expect()` calls in parser with proper error handling
- ✅ **Structured error types**: Added custom `ParseError` enum with `thiserror` for clear error categories
- ✅ **Result propagation**: Converted all parsing functions to return `ParseResult<T>`
- ✅ **Error context preservation**: Maintained descriptive error messages throughout
- ✅ **Simplified error structure**: Streamlined to essential error types (syntax, parsing, internal)
- ✅ **Boxing optimization**: Used `Box<PestError>` to reduce enum size warnings
- ✅ **Quality assurance**: All 186 tests pass, linting clean, code properly formatted

The parser now provides robust error handling that prevents crashes while maintaining excellent performance and
developer experience. **Note**: This completes error handling for the parser module only - other modules 
(semantic analysis, codegen, backend) still contain `unwrap()`/`expect()` calls that need similar treatment.