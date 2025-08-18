# Extensible Type System Implementation Plan

## Overview

This document outlines the implementation plan for replacing Kigiri's simple type system with an extensible type system
that supports:

- Enhanced primitive types (i8/i16/i32/i64, u8/u16/u32/u64, f32/f64)
- Composite types (arrays, tuples, function types)
- User-defined types (structs, enums, type aliases)
- Future extensibility for advanced features

## Current State Analysis

### Existing Type System

- **Location**: `semantic_analysis/src/types.rs:8`
- **Types**: Simple enum with `Int`, `Double`, `Bool`
- **LLVM Mapping**: `Int` → `i64`, `Double` → `f64`, `Bool` → `i1`
- **Usage**: Hardcoded throughout pipeline in 4 main files:
    - `semantic_analysis/src/types.rs` - Type definitions
    - `semantic_analysis/src/phase_type_resolver.rs` - Type checking
    - `codegen/src/ir.rs` - IR generation
    - `backend_llvm/src/ir_to_llvm.rs` - LLVM code generation

### Integration Points

- Parser: Type name parsing and literal inference
- Semantic Analysis: Type checking and compatibility
- Codegen: IR instruction type information
- LLVM Backend: Native type mapping and operations

## Design Architecture

### 1. Type Identification System

```rust
// Unique identifier for each type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(u32);

// Central registry for all type definitions
#[derive(Debug, Default)]
pub struct TypeRegistry {
    types_by_name: HashMap<StringId, TypeId>,
}
```

### 2. Hierarchical Type Definitions

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum TypeDefinition {
    Primitive(PrimitiveType),
    Composite(CompositeType),
    UserDefined(UserDefinedType),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PrimitiveType {
    // Signed integers
    I8,
    I16,
    I32,
    I64,
    // Unsigned integers  
    U8,
    U16,
    U32,
    U64,
    // Floating point
    F32,
    F64,
    // Special types
    Bool,
    Void,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CompositeType {
    Array { element_type: TypeId, size: usize },
    Slice { element_type: TypeId },
    Tuple { fields: Vec<TypeId> },
    Function { params: Vec<TypeId>, return_type: Option<TypeId> },
    Pointer { pointee_type: TypeId },
}

#[derive(Debug, Clone, PartialEq)]
pub enum UserDefinedType {
    Struct(StructDefinition),
    Enum(EnumDefinition),      // Future
    Alias { name: StringId, target: TypeId },
}
```

### 3. LLVM Integration Strategy

**Key Insight**: LLVM tracks signedness in operations, not storage:

- Storage: Both `i32` signed/unsigned use `i32_type()`
- Operations: Different instructions (`icmp slt` vs `icmp ult`, `sdiv` vs `udiv`)

```rust
impl TypeId {
    pub fn llvm_type<'ctx>(&self, registry: &TypeRegistry, context: &'ctx Context) -> BasicTypeEnum<'ctx> {
        match registry.get_definition(*self) {
            TypeDefinition::Primitive(prim) => match prim {
                PrimitiveType::I8 | PrimitiveType::U8 => context.i8_type().into(),
                PrimitiveType::I16 | PrimitiveType::U16 => context.i16_type().into(),
                PrimitiveType::I32 | PrimitiveType::U32 => context.i32_type().into(),
                PrimitiveType::I64 | PrimitiveType::U64 => context.i64_type().into(),
                PrimitiveType::F32 => context.f32_type().into(),
                PrimitiveType::F64 => context.f64_type().into(),
                PrimitiveType::Bool => context.bool_type().into(),
            },
            // ... composite and user-defined types
        }
    }

    pub fn is_signed_integer(&self, registry: &TypeRegistry) -> bool {
        matches!(
            registry.get_definition(*self),
            TypeDefinition::Primitive(PrimitiveType::I8 | PrimitiveType::I16 | 
                                     PrimitiveType::I32 | PrimitiveType::I64)
        )
    }
}
```

## Implementation Plan

### Phase 1: Core Type System Infrastructure (Week 1)

#### 1.1 Create New Type System Module

- **File**: `semantic_analysis/src/type_system.rs`
- **Content**: `TypeId`, `TypeDefinition`, `TypeRegistry`
- **Goal**: Complete type representation without breaking existing code

#### 1.2 Implement Type Registry

- Type definition storage and lookup
- Primitive type interning with caching
- Scoped type definitions for nested contexts
- Type compatibility and analysis methods

#### 1.3 Add Type Utility Methods

```rust
impl TypeId {
    pub fn bit_width(&self, registry: &TypeRegistry) -> u32;
    pub fn is_integer(&self, registry: &TypeRegistry) -> bool;
    pub fn is_float(&self, registry: &TypeRegistry) -> bool;
    pub fn size_bytes(&self, registry: &TypeRegistry) -> usize;
    pub fn alignment(&self, registry: &TypeRegistry) -> usize;
}
```

#### 1.4 Update Compilation Phases

```rust
pub trait CompilationPhase {
    // ... existing types ...
    type TypeSystem: Debug + PartialEq;
}

impl CompilationPhase for PhaseTypeResolved<'_> {
    type TypeSystem = TypeRegistry;
    // ... other types use TypeId instead of Type ...
}
```

### Phase 2: Primitive Type Migration (Week 2)

#### 2.1 Migrate Semantic Analysis

- **File**: `semantic_analysis/src/types.rs`
- Replace `Type` enum with `TypeId`
- Update `Type::parse()` to work with registry
- Maintain backward compatibility (`int` → `i64`, `double` → `f64`)

#### 2.2 Update Type Resolution

- **File**: `semantic_analysis/src/phase_type_resolver.rs`
- Integrate `TypeRegistry` into semantic analyzer
- Update type checking logic for new type system
- Handle type compatibility with new primitive types

#### 2.3 Parser Integration

- Update grammar to accept new type names (`i8`, `u32`, `f32`, etc.)
- Add type suffix support for literals (`42u32`, `3.14f32`)
- Maintain backward compatibility with existing syntax

### Phase 3: LLVM Backend Updates (Week 3)

#### 3.1 Enhanced LLVM Type Mapping

- **File**: `backend_llvm/src/ir_to_llvm.rs`
- Update all type mapping functions
- Add signed/unsigned operation variants:
    - Comparisons: `icmp slt` vs `icmp ult`
    - Division: `sdiv` vs `udiv`
    - Shifts: `ashr` vs `lshr`
    - Extensions: `sext` vs `zext`

#### 3.2 Operation Dispatch by Signedness

```rust
fn handle_binary_int_operands(&self, op: &BinaryOperator, type_id: TypeId, ...) {
    match op {
        BinaryOperator::Div => {
            if type_id.is_signed_integer(registry) {
                self.builder.build_int_signed_div(left, right, name)
            } else {
                self.builder.build_int_unsigned_div(left, right, name)
            }
        }
        // ... other operations
    }
}
```

#### 3.3 Codegen IR Updates

- **File**: `codegen/src/ir.rs`
- Replace `Type` with `TypeId` in IR structures
- Update IR generation to pass type registry context

### Phase 4: Composite Types Foundation (Week 4)

#### 4.1 Array Type Support

- Grammar: `[element_type; size]` syntax
- Semantic analysis: Array type creation and indexing
- LLVM: Array type generation and GEP instructions

#### 4.2 Struct Definition Parsing

- Grammar: `struct Name { field: type, ... }`
- AST nodes for struct definitions
- Symbol table integration for named types

#### 4.3 Basic Struct Codegen

- LLVM struct type generation
- Field access via GEP instructions
- Struct literal initialization

### Phase 5: Advanced Features (Week 5)

#### 5.1 Type Aliases

- Grammar: `type NewName = ExistingType;`
- Registry integration for alias resolution
- Maintain source type information for diagnostics

#### 5.2 Function Types

- First-class function type support
- Function pointer generation in LLVM
- Type checking for function assignments

#### 5.3 Enhanced Type Checking

- Structural compatibility rules
- Implicit conversions (numeric promotion)
- Better error messages with type information

### Phase 6: Testing & Integration (Week 6)

#### 6.1 Comprehensive Test Suite

- Unit tests for all type operations
- Integration tests for composite types
- LLVM codegen verification tests
- Backward compatibility tests

#### 6.2 Performance Validation

- Benchmark type registry operations
- Memory usage analysis for type interning
- Compilation speed comparison

#### 6.3 Documentation Updates

- Update language grammar documentation
- Add type system design documentation
- Create migration guide for users

## Migration Strategy

### Backward Compatibility

- Maintain existing type names: `int`, `double`, `bool`
- Map to new types: `int` → `i64`, `double` → `f64`
- Support both old and new syntax during transition

### Incremental Deployment

1. **Phase 1-2**: Internal type system migration (no user-visible changes)
2. **Phase 3**: Enable new primitive types (`i32`, `f32`, etc.)
3. **Phase 4-5**: Add composite and user-defined types
4. **Phase 6**: Full feature availability

### Risk Mitigation

- Comprehensive test coverage at each phase
- Feature flags for new type system components
- Gradual rollout with fallback to old system if needed

## Testing Strategy

### Unit Tests

- `TypeRegistry` operations (interning, lookup, scoping)
- Type compatibility and conversion rules
- LLVM type mapping correctness

### Integration Tests

- End-to-end compilation with new types
- Struct definition and usage
- Array operations and bounds checking

### Regression Tests

- All existing functionality preserved
- Performance characteristics maintained
- LLVM output equivalence for existing code

## Success Metrics

### Functionality

- [ ] All primitive types (i8-i64, u8-u64, f32, f64) supported
- [ ] Basic array types working with indexing
- [ ] Struct definition and field access
- [ ] Type aliases functional
- [ ] Backward compatibility maintained

### Quality

- [ ] Zero performance regression for existing code
- [ ] Memory usage within 10% of current system
- [ ] All tests passing (current: 187 tests)
- [ ] Clean `cargo clippy` output

### Extensibility

- [ ] Easy addition of new primitive types
- [ ] Straightforward composite type implementation
- [ ] Clear extension points for future features (generics, traits)

## Future Extensions

This design enables future features:

### Generics & Parametric Types

```rust
TypeDefinition::Generic(GenericDefinition {
name: StringId,
parameters: Vec<TypeParameter>,
body: TypeId,
})
```

### Trait System

```rust
TypeDefinition::Trait(TraitDefinition {
name: StringId,
methods: Vec<TraitMethod>,
})
```

### Advanced Features

- Union types
- Sum types (tagged unions)
- SIMD vector types
- Custom numeric types (fixed-point, decimal)

## Dependencies

### New Dependencies

- None required - design uses existing infrastructure
- Optional: `smallvec` for performance optimization of type lists

### Development Tools

- Existing test infrastructure sufficient
- `insta` snapshots for LLVM output verification
- `criterion` for performance benchmarking (already planned)

## Risk Assessment

### Low Risk

- Type registry implementation (new, isolated code)
- Primitive type expansion (well-understood LLVM mapping)
- Test suite expansion

### Medium Risk

- LLVM backend updates (complex but well-tested)
- Parser grammar changes (affects user syntax)
- Performance characteristics of type interning

### High Risk

- Major semantic analysis changes (core compiler logic)
- Backward compatibility maintenance (requires careful testing)
- Memory usage growth from type registry

## Conclusion

This plan provides a solid foundation for Kigiri's type system evolution while maintaining the compiler's excellent
quality standards. The phased approach minimizes risk while delivering incremental value, and the design enables future
advanced features without major architectural changes.

The type registry approach with `TypeId` provides the perfect balance of performance, extensibility, and maintainability
for a growing language implementation.