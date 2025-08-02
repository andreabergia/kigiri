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

- Inconsistent error handling (35 `unwrap()`, 90 `expect()`, 6 `panic!`)
- TODOs present in 4 files indicating incomplete features
- `#![allow(unused)]` in all crates suggesting dead code

#### Action Items

- [ ] **Replace `unwrap()` calls** with proper error handling
    - Convert to `Result` propagation where appropriate
    - Add meaningful error messages with `expect()`
    - Focus on production code paths first
- [ ] **Remove `#![allow(unused)]` attributes**
    - Clean up dead code and unused imports
    - Enable stricter linting (`#![deny(unused)]`)
    - Fix all compiler warnings
- [ ] **Address all TODO comments**
    - Complete incomplete features in 4 identified files
    - Document design decisions for remaining TODOs
    - Convert TODOs to GitHub issues if appropriate

### 2. Error Reporting & Diagnostics (Medium Priority)

#### Current Issues

- Basic error reporting without source locations
- No error recovery in parser for IDE support
- Limited diagnostic suggestions

#### Action Items

- [ ] **Enhance error reporting system**
    - Add source location tracking to all error types
    - Implement error severity levels (Error, Warning, Info)
    - Add helpful diagnostic suggestions
- [ ] **Implement parser error recovery**
    - Continue parsing after errors for better IDE support
    - Collect multiple errors in single compilation pass
    - Improve error message quality
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

### 4. Development Experience (Low Priority)

#### Current Issues

- No security scanning tools
- Limited development workflow automation
- No incremental compilation support

#### Action Items

- [x] **Add security and quality tooling**
    - ✅ Integrate `cargo-audit` for vulnerability scanning
    - Add `cargo-deny` for license compliance
    - Set up automated dependency updates
- [ ] **Enhance development workflow**
    - Add pre-commit hooks for code quality
    - ✅ Integrate with CI/CD pipeline
    - Add code coverage reporting automation
- [ ] **Future IDE support preparation**
    - Language server protocol foundation
    - Debug adapter protocol considerations
    - Syntax highlighting definitions

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

### Phase 1: Code Quality Foundation (Weeks 1-2)

- Remove `#![allow(unused)]` and clean dead code
- Replace critical `unwrap()` calls in production paths
- Address urgent TODOs in semantic analysis and backend

### Phase 2: Error Handling Polish (Weeks 3-4)

- Complete error handling refactoring
- Enhance error reporting with source locations
- Implement parser error recovery
- Create structured diagnostic framework

### Phase 3: Performance Optimization (Weeks 5-6)

- Optimize LLVM backend with optimization passes
- Add performance benchmarking infrastructure
- Profile memory usage and optimize allocations

### Phase 4: Development Experience (Weeks 7-8)

- ✅ Security tooling integration
- Development workflow automation
- ✅ CI/CD pipeline enhancements
- Code quality automation

### Phase 5: Advanced Features (Optional)

- Property-based testing (if needed)
- Parallel compilation (if beneficial)
- Incremental compilation support
- Advanced IDE support features

## Success Metrics

- **Code Quality**: Zero `unwrap()` calls in production code
- **Performance**: Measurable LLVM optimization improvements
- **Development**: Clean `cargo clippy` with strict lints enabled
- **Maintainability**: All TODOs resolved or tracked as issues

## Dependencies & Tools

### New Dependencies (Minimal Additions)

- `criterion` - Performance benchmarking
- `anyhow` - Enhanced error context (optional)
- `tracing` - Structured logging (if needed)

### Development Tools

- ✅ `cargo-audit` - Security vulnerability scanning
- `cargo-deny` - License and dependency policy enforcement
- `cargo-tarpaulin` or `cargo-llvm-cov` - Code coverage automation

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