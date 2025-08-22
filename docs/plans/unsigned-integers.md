# Unsigned Integer Implementation Plan

## Overview

Add support for unsigned integer types (u8/u16/u32/u64) to the Kigiri compiler, following the same implementation pattern used for signed integers (i8/i16/i32/i64).

## Analysis

**Current Implementation Pattern:**
- Signed integers implemented across 4 pipeline phases: parser → semantic analysis → codegen → backend_llvm
- Recent commits show clean separation and consistent patterns
- Each phase follows established conventions for type handling

**Key Insight:**
Unsigned integers will use the same LLVM integer types as signed counterparts (i8_type(), i16_type(), etc.) since LLVM handles signedness at the operation level, not the type level.

## Implementation Plan

### Phase 1: Parser Layer

1. **grammar.pest:66** - Extend `intSuffix` rule:
   ```pest
   intSuffix = @{
       "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
   }
   ```

2. **ast.rs:143-151** - Add unsigned variants to `LiteralValue` enum:
   ```rust
   #[derive(Debug, PartialEq, Clone)]
   pub enum LiteralValue {
       I8(i8),
       I16(i16),
       I32(i32),
       I64(i64),
       U8(u8),    // Add
       U16(u16),  // Add
       U32(u32),  // Add
       U64(u64),  // Add
       F32(f32),
       F64(f64),
       Boolean(bool),
   }
   ```

3. **ast.rs:410-422** - Update `Display` impl for `LiteralValue`:
   ```rust
   LiteralValue::U8(value) => write!(f, "{}u8", value),
   LiteralValue::U16(value) => write!(f, "{}u16", value),
   LiteralValue::U32(value) => write!(f, "{}u32", value),
   LiteralValue::U64(value) => write!(f, "{}u64", value),
   ```

4. **parser.rs** - Update literal parsing logic to handle unsigned suffixes

### Phase 2: Semantic Analysis Layer

5. **types.rs:8-16** - Add unsigned variants to `Type` enum:
   ```rust
   #[derive(Debug, PartialEq, Clone, Copy)]
   pub enum Type {
       I8,
       I16,
       I32,
       I64,
       U8,   // Add
       U16,  // Add
       U32,  // Add
       U64,  // Add
       F32,
       F64,
       Bool,
   }
   ```

6. **types.rs:18-30** - Update `Display` impl:
   ```rust
   Type::U8 => write!(f, "u8"),
   Type::U16 => write!(f, "u16"),
   Type::U32 => write!(f, "u32"),
   Type::U64 => write!(f, "u64"),
   ```

7. **types.rs:33-43** - Update `to_string_short()` method:
   ```rust
   Type::U8 => "u8",
   Type::U16 => "u16",
   Type::U32 => "u32",
   Type::U64 => "u64",
   ```

8. **types.rs:45-55** - Update `of_literal()` method:
   ```rust
   LiteralValue::U8(_) => Type::U8,
   LiteralValue::U16(_) => Type::U16,
   LiteralValue::U32(_) => Type::U32,
   LiteralValue::U64(_) => Type::U64,
   ```

9. **types.rs:61-78** - Update `parse()` method:
   ```rust
   "u8" => Ok(Type::U8),
   "u16" => Ok(Type::U16),
   "u32" => Ok(Type::U32),
   "u64" => Ok(Type::U64),
   ```

10. **types.rs:80-82** - Update `is_integer()` method:
    ```rust
    pub fn is_integer(&self) -> bool {
        matches!(self, 
            Type::I8 | Type::I16 | Type::I32 | Type::I64 |
            Type::U8 | Type::U16 | Type::U32 | Type::U64
        )
    }
    ```

### Phase 3: Backend LLVM Layer

11. **ir_to_llvm.rs:132-141** - Update `llvm_int_type()` method:
    ```rust
    fn llvm_int_type(&self, type_: &Type) -> IntType<'c> {
        match type_ {
            Type::I8 | Type::U8 => self.context.i8_type(),
            Type::I16 | Type::U16 => self.context.i16_type(),
            Type::I32 | Type::U32 => self.context.i32_type(),
            Type::I64 | Type::U64 => self.context.i64_type(),
            Type::Bool => self.context.bool_type(),
            _ => panic!("cannot get llvm_int_type for {}", type_),
        }
    }
    ```

12. **ir_to_llvm.rs:151-161** - Update `llvm_type()` method:
    ```rust
    Type::U8 => self.context.i8_type().into(),
    Type::U16 => self.context.i16_type().into(),
    Type::U32 => self.context.i32_type().into(),
    Type::U64 => self.context.i64_type().into(),
    ```

13. **ir_to_llvm.rs** - Update `handle_constant()` method:
    ```rust
    LiteralValue::U8(value) => self.context.i8_type().const_int(*value as u64, false).as_basic_value_enum(),
    LiteralValue::U16(value) => self.context.i16_type().const_int(*value as u64, false).as_basic_value_enum(),
    LiteralValue::U32(value) => self.context.i32_type().const_int(*value as u64, false).as_basic_value_enum(),
    LiteralValue::U64(value) => self.context.i64_type().const_int(*value, false).as_basic_value_enum(),
    ```

### Phase 4: Testing

14. Add test cases for unsigned integer literals and type checking
15. Run `just test` to ensure no regressions
16. Update any snapshot tests affected by new type support
17. Run `just lint` to ensure code quality

## Files to Modify

- `parser/src/grammar.pest:66`
- `parser/src/ast.rs:143-151, 410-422`
- `parser/src/parser.rs`
- `semantic_analysis/src/types.rs:8-91` (multiple methods)
- `backend_llvm/src/ir_to_llvm.rs:132-161, handle_constant method`

## Testing Strategy

1. Create test cases with unsigned literals: `42u8`, `1000u16`, `50000u32`, `18446744073709551615u64`
2. Test type inference and checking for unsigned types
3. Test operations between signed and unsigned types (should require explicit casts)
4. Verify LLVM code generation produces correct integer types
5. Run full test suite to ensure no regressions

## Notes

- Unsigned types use same LLVM integer types as signed (signedness handled at operation level)
- Follow existing code patterns and conventions throughout
- Maintain consistency with signed integer implementation
- Consider future arithmetic operation semantics between signed/unsigned types