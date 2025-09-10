# Untyped Integer Implementation Plan

## Overview

Implement type inference for untyped integer literals (e.g., `42` vs `42i32`) using a constraint-based approach, following Rust's integer fallback design.

## Background Research

### Rust's Integer Fallback Behavior

Rust defaults unconstrained integer literals to `i32` and floating-point literals to `f64`. This fallback occurs at the end of type inference when no other constraints determine the type (RFC 212).

### Current Architecture Analysis

- **Parser**: `LiteralValue::UntypedInteger(String)` represents untyped integers
- **Semantic Analysis**: 3-phase pipeline (TopLevelDeclarationCollector → TypeResolver → ReturnPathAnalyzer)  
- **Constraint System**: Already implemented in `semantic_analysis/src/type_constraints.rs`
- **AST Phases**: `PhaseParsed` → `PhaseTypeResolved` with parameterized AST nodes

## Implementation Strategy

### Phase 1: Constraint System Extension

1. **Add `IsIntegerType` constraint**
   ```rust
   enum Constraint {
       TypeEqual { symbol: StringId, required_type: Type },
       TypeSameAs { symbol: StringId, other: StringId },
       IsIntegerType { symbol: StringId },  // New
   }
   ```

2. **Extend constraint solver**
   - Handle `IsIntegerType` constraints during iteration
   - Apply `i32` fallback to unresolved integer constraints at end of solving

### Phase 2: Constraint Generation

3. **Implement AST walker for constraint generation**
   - Visit expressions and statements
   - Generate `IsIntegerType` for untyped integer literals
   - Generate `TypeSameAs` for operations requiring same types
   - Generate `TypeEqual` for explicit type constraints

4. **Constraint generation rules**:
   - `LiteralValue::UntypedInteger(_)` → `IsIntegerType { symbol }`
   - Binary operations → `TypeSameAs` between operands
   - Assignments → `TypeEqual` or `TypeSameAs` constraints
   - Function calls → `TypeEqual` for arguments and return values

### Phase 3: Integration

5. **Type assignment pass**
   - Apply solved constraints back to AST nodes
   - Convert `UntypedInteger` literals to concrete types

6. **Semantic analyzer integration**
   - Insert constraint-based inference before existing `TypeResolver`
   - Or replace relevant parts of `TypeResolver` with constraint solving

### Phase 4: Testing & Validation

7. **Comprehensive test scenarios**:
   - Basic inference: `let x = 42;` → `x: i32`
   - Propagation: `let x = 42; let y = x;` → both `i32`
   - Mixed constraints: `let x = 42; x + 1i64;` → type error
   - Function calls with inference
   - Complex expressions with multiple untyped literals

8. **Integration testing**
   - End-to-end compilation pipeline
   - Error message quality
   - Performance impact assessment

## Key Design Decisions

- **Default Type**: `i32` for unresolved integer constraints (matches Rust)
- **Integration Point**: Between declaration collection and current type resolution
- **Symbol Tracking**: Leverage existing `StringId` system
- **Error Handling**: Extend existing `SemanticAnalysisError` types

## Implementation Order

1. Add `IsIntegerType` constraint variant
2. Extend constraint solver for integer fallback
3. Implement constraint generation walker
4. Create type assignment pass
5. Integrate into semantic analyzer pipeline
6. Add comprehensive tests
7. Refine error handling and messages
8. Performance testing and optimization

## Success Criteria

- [ ] Untyped integers infer to `i32` when unconstrained
- [ ] Type propagation works correctly through operations
- [ ] Appropriate type errors for conflicting constraints
- [ ] All existing tests continue to pass
- [ ] New test coverage for inference scenarios
- [ ] Clear error messages for inference failures

## Notes

This approach follows industry-standard constraint-based type inference used by Rust, Swift, Kotlin, and other modern compilers. The three-pass design (constraint generation → solving → assignment) is the proven pattern for handling complex type inference scenarios.