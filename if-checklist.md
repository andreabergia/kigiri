# If Statement Implementation Checklist

## Current Status
- ✅ **Grammar** - `ifStatement` rule defined in `grammar.pest:23`
- ✅ **Parser** - `parse_if_statement()` function implemented in `parser/src/parser.rs`
- ✅ **AST Definitions** - `Statement::If` and `IfElseBlock` enum defined in `parser/src/ast.rs`
- ✅ **Parsed AST** - Helper methods for if statement creation in `parsed_ast.rs`
- ✅ **Tests** - Grammar and parser tests for if statements

## Remaining Implementation Tasks

### 1. Semantic Analysis Phase (`semantic_analysis` crate)
- [ ] **Type Resolution** - Implement if statement handling in `phase_type_resolver.rs:` 
  - [ ] Resolve condition expression type and ensure it's boolean
  - [ ] Type check then-block statements
  - [ ] Type check else-block statements (if present)
  - [ ] Handle nested if-else chains
  - [ ] Ensure proper scope handling for variables in blocks

- [ ] **Top-level Declaration Collection** - Implement in `phase_top_level_declaration_collector.rs:`
  - [ ] Handle if statements in top-level collection phase
  - [ ] Ensure proper traversal of then/else blocks

- [ ] **AST Typed** - Implement Display formatting in `ast_typed.rs:`
  - [ ] Add proper formatting for typed if statements

### 2. Code Generation Phase (`codegen` crate)
- [ ] **IR Builder** - Implement if statement codegen in `ir_builder.rs:`
  - [ ] Generate condition evaluation IR
  - [ ] Create basic blocks for then/else branches
  - [ ] Handle conditional jumps between blocks
  - [ ] Manage control flow merge points
  - [ ] Handle nested if statements
  - [ ] Ensure proper variable scoping in blocks

- [ ] **IR Definitions** - Add if-related IR instructions if needed:
  - [ ] Branch instructions
  - [ ] Block management for control flow

### 3. LLVM Backend Phase (`backend_llvm` crate)
- [ ] **LLVM IR Generation** - Implement if statement handling:
  - [ ] Convert condition to LLVM boolean value
  - [ ] Generate LLVM basic blocks for then/else
  - [ ] Create conditional branch instructions
  - [ ] Handle block merging after if statement
  - [ ] Manage phi nodes for variables modified in branches
  - [ ] Optimize simple if patterns

### 4. Testing & Validation
- [ ] **Unit Tests**:
  - [ ] Semantic analysis tests for if statements
  - [ ] Codegen tests for if statement IR
  - [ ] LLVM backend tests for if compilation

- [ ] **Integration Tests**:
  - [ ] End-to-end compilation of if statements
  - [ ] Nested if statement compilation
  - [ ] If statements with function calls
  - [ ] If statements with variable assignments

- [ ] **Snapshot Tests**:
  - [ ] Update snapshot tests for semantic analysis
  - [ ] Update snapshot tests for codegen
  - [ ] Update snapshot tests for LLVM backend

### 5. Error Handling & Edge Cases
- [ ] **Semantic Errors**:
  - [ ] Non-boolean condition expressions
  - [ ] Type mismatches in branches
  - [ ] Undefined variables in conditions

- [ ] **Codegen Edge Cases**:
  - [ ] Empty then/else blocks
  - [ ] Return statements in if branches
  - [ ] Unreachable code after if statements

## Implementation Order
1. **Semantic Analysis** - Start with type resolution
2. **Codegen** - Implement IR generation for if statements
3. **LLVM Backend** - Add LLVM compilation support
4. **Testing** - Add comprehensive tests at each phase
5. **Integration** - End-to-end testing and validation

## Key Files to Modify
- `semantic_analysis/src/phase_type_resolver.rs` - Type checking
- `semantic_analysis/src/phase_top_level_declaration_collector.rs` - Declaration collection
- `semantic_analysis/src/ast_typed.rs` - Display formatting
- `codegen/src/ir_builder.rs` - IR generation
- `backend_llvm/src/lib.rs` - LLVM compilation
- Test files in each crate

## Technical Notes
- If statements introduce control flow branches requiring basic block management
- Condition expressions must be type-checked to ensure boolean result
- Variable scoping in then/else blocks needs careful handling
- LLVM phi nodes may be needed for variables modified in branches
- Consider optimization opportunities for simple if patterns