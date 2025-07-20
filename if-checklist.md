# If Statement Implementation Checklist

## Current Status (Updated: July 2025)
- ✅ **Grammar** - `ifStatement` rule defined in `grammar.pest:23`
- ✅ **Parser** - `parse_if_statement()` function implemented in `parser/src/parser.rs`
- ✅ **AST Definitions** - `Statement::If` and `IfElseBlock` enum defined in `parser/src/ast.rs`
- ✅ **Parsed AST** - Complete Display implementation for if statements
- ✅ **Semantic Analysis** - Full implementation completed with comprehensive tests
- ✅ **Tests** - 9 passing semantic analysis tests covering all if statement patterns

## Completed Implementation ✅

### 1. Semantic Analysis Phase (`semantic_analysis` crate) - ✅ COMPLETE
- ✅ **Type Resolution** - Complete implementation in `phase_type_resolver.rs:297-342`
  - ✅ Resolve condition expression type and ensure it's boolean
  - ✅ Type check then-block statements
  - ✅ Type check else-block statements (if present)
  - ✅ Handle nested if-else chains
  - ✅ Ensure proper scope handling for variables in blocks
  - ✅ Comprehensive error handling with `IfConditionMustBeBool`

- ✅ **Top-level Declaration Collection** - Complete in `phase_top_level_declaration_collector.rs:130-144`
  - ✅ Handle if statements in top-level collection phase
  - ✅ Ensure proper traversal of then/else blocks

- ✅ **AST Typed** - Complete Display formatting in `ast_typed.rs:283-318`
  - ✅ Add proper formatting for typed if statements

## Remaining Implementation Tasks

### 2. Code Generation Phase (`codegen` crate) - 🔄 PARTIALLY IMPLEMENTED
**Current Status**: IR architecture updated for control flow, if statement codegen still needs implementation

- ✅ **IR Architecture Changes** - Control flow foundation complete:
  - ✅ Add multi-basic-block support to IR (`Function` now contains `basic_blocks: BumpVec`)
  - ✅ Add `BlockId` type for basic block references
  - ✅ Extend `Function` struct to contain multiple basic blocks with `entry_block_id`
  - ✅ Add control flow graph management infrastructure

- ✅ **IR Instructions** - Control flow instructions implemented:
  - ✅ `Branch { condition: InstructionId, then_block: BlockId, else_block: BlockId }`
  - ✅ `Jump { target_block: BlockId }`
  - [ ] Consider `Phi` nodes for SSA form variable merging

- [ ] **IR Builder** - Implement if statement codegen in `ir_builder.rs`:
  - [ ] Generate condition evaluation IR
  - [ ] Create basic blocks for then/else branches
  - [ ] Handle conditional jumps between blocks
  - [ ] Manage control flow merge points
  - [ ] Handle nested if statements
  - [ ] Ensure proper variable scoping in blocks

### 3. LLVM Backend Phase (`backend_llvm` crate) - 🔄 PARTIALLY IMPLEMENTED
**Current Status**: Updated for multi-block functions, control flow instructions need implementation

- [ ] **LLVM IR Generation** - Implement if statement handling:
  - [ ] Convert condition to LLVM boolean value
  - [ ] Generate LLVM basic blocks for then/else
  - [ ] Create conditional branch instructions (`br` instruction)
  - [ ] Handle block merging after if statement
  - [ ] Manage phi nodes for variables modified in branches
  - ✅ Support multi-block function compilation (infrastructure updated)
  - ✅ Jump/Branch instruction placeholders added (currently `todo!()` implementations)

### 4. Testing & Validation
- ✅ **Semantic Analysis Tests**: 9 comprehensive tests passing
- [ ] **Codegen Tests**:
  - [ ] IR generation tests for if statements
  - [ ] Multi-basic-block IR structure tests
  - [ ] Control flow IR instruction tests

- [ ] **LLVM Backend Tests**:
  - [ ] LLVM compilation tests for if statements
  - [ ] End-to-end execution tests

- [ ] **Integration Tests**:
  - [ ] End-to-end compilation of if statements
  - [ ] Nested if statement compilation
  - [ ] If statements with function calls
  - [ ] If statements with variable assignments

- [ ] **Snapshot Tests**:
  - ✅ Semantic analysis snapshots complete
  - [ ] Update snapshot tests for codegen
  - [ ] Update snapshot tests for LLVM backend

### 5. Error Handling & Edge Cases
- ✅ **Semantic Errors** - Fully implemented:
  - ✅ Non-boolean condition expressions (`IfConditionMustBeBool` error)
  - ✅ Type mismatches in branches (handled by existing type system)
  - ✅ Undefined variables in conditions (handled by existing symbol resolution)

- [ ] **Codegen Edge Cases** - Not yet implemented:
  - [ ] Empty then/else blocks
  - [ ] Return statements in if branches
  - [ ] Unreachable code after if statements

## Implementation Progress
1. ✅ **Semantic Analysis** - COMPLETE (type resolution, error handling, tests)
2. 🔄 **Codegen** - IR ARCHITECTURE COMPLETE (if statement codegen implementation pending)
3. 🔄 **LLVM Backend** - INFRASTRUCTURE UPDATED (control flow instruction handling pending)
4. 🔄 **Testing** - Semantic tests complete, codegen/LLVM tests pending
5. ❌ **Integration** - Awaiting if statement codegen implementation

## Key Files to Modify

### ✅ Completed
- ✅ `semantic_analysis/src/phase_type_resolver.rs` - Type checking complete
- ✅ `semantic_analysis/src/phase_top_level_declaration_collector.rs` - Declaration collection complete
- ✅ `semantic_analysis/src/ast_typed.rs` - Display formatting complete

### ❌ Remaining 
- ✅ `codegen/src/ir.rs` - Multi-basic-block support and control flow instructions complete
- ❌ `codegen/src/ir_builder.rs` - Implement if statement IR generation (currently `todo!()` at line 137)
- 🔄 `backend_llvm/src/ir_to_llvm.rs` - Infrastructure updated, control flow instruction handling pending
- ❌ Test files in codegen and backend_llvm crates

## Technical Notes & Challenges

### Architecture Challenges
- ✅ **IR Redesign Complete**: IR now supports multiple basic blocks per function
- ✅ **Control Flow**: Conditional branching and block merging support added to IR
- **SSA Form**: May need phi nodes for variables modified in different branches (still pending)

### Implementation Notes
- ✅ Condition type checking complete (must be boolean)
- ✅ Variable scoping in then/else blocks working correctly
- ✅ Basic block management implemented with multi-block function support
- ✅ Control flow instructions (Jump, Branch) added to IR
- ❌ LLVM phi nodes and conditional branches not implemented
- ❌ If statement codegen in ir_builder still needs implementation

### Next Steps Priority
1. ✅ **Extend IR architecture** to support multiple basic blocks per function
2. ✅ **Add control flow instructions** (Branch, Jump) to IR instruction set  
3. **Implement if statement codegen** in `ir_builder.rs` (remove `todo!()` at line 137)
4. **Add LLVM compilation** for control flow instructions (implement Jump/Branch handling)