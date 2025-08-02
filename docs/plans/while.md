# While Loop Implementation Plan

Based on analysis of the existing `if` statement implementation, here's a comprehensive plan for adding `while` loops using Rust syntax.

## Overview

While loops will reuse the existing basic block infrastructure, control flow instructions, and semantic analysis patterns established for if statements. The key difference is the loop-back control flow pattern requiring 3 basic blocks instead of 2-3.

## Implementation Steps

### 1. Grammar Updates (`grammar.pest:18`)

Add `whileStatement` to the statement rule and define the while grammar:

```pest
statement = { whileStatement | ifStatement | (letStatement | assignmentStatement | returnStatement | expression) ~ ";" }
whileStatement = { "while" ~ expression ~ block }
```

### 2. AST Structure (`ast.rs:56`)

Add `WhileStatement` to the `Statement` enum, similar to the existing `If` variant:

```rust
pub enum Statement<'a, Phase: CompilationPhase> {
    // ... existing variants
    While(&'a WhileStatement<'a, Phase>),
}

#[derive(Debug, PartialEq)]
pub struct WhileStatement<'a, Phase: CompilationPhase> {
    pub condition: &'a Expression<'a, Phase>,
    pub body: &'a Block<'a, Phase>,
}
```

### 3. Parser Integration (`parser.rs`)

Follow the same pattern as `ifStatement` parsing - extract condition and body block from the pest parse tree.

### 4. Semantic Analysis

**Phase 1 (Declaration Collection)**: Map the while statement structure like the existing if statement mapping.

**Phase 2 (Type Resolution)**: 
- Validate the condition expression resolves to `Type::Bool` (same validation as if statements)
- Recursively analyze the body block with proper symbol table scoping

### 5. IR Generation (`ir_builder.rs`)

The key insight is that while loops need **3 basic blocks** vs if statements' 2-3 blocks:

```rust
fn handle_while_statement(
    &self,
    while_statement: &WhileStatement<PhaseTypeResolved>,
    symbol_table: &SymbolTable,
) -> FoundReturn {
    // Create basic blocks
    let condition_block = self.create_basic_block();
    let body_block = self.create_basic_block(); 
    let merge_block = self.create_basic_block_deferred();
    
    // Jump to condition evaluation
    self.push_to_current_bb(self.ir_allocator.new_jump(condition_block.id));
    
    // Condition block: evaluate condition and branch
    self.switch_to_basic_block(condition_block);
    let condition_instruction = self.handle_expression(while_statement.condition, symbol_table);
    let branch_instruction = self.ir_allocator
        .new_branch(condition_instruction, body_block.id, merge_block.id);
    self.push_to_current_bb(branch_instruction);
    
    // Body block: execute body, then jump back to condition
    self.switch_to_basic_block(body_block);
    let body_has_return = self.handle_block(while_statement.body);
    if body_has_return == FoundReturn::No {
        self.push_to_current_bb(self.ir_allocator.new_jump(condition_block.id));
    }
    
    // Merge block for after loop
    self.add_basic_block(merge_block);
    self.switch_to_basic_block(merge_block);
    
    FoundReturn::No // While loops don't guarantee returns
}
```

### 6. LLVM Backend

The existing `Jump` and `Branch` IR instructions already handle the required control flow patterns. No changes needed to `ir_to_llvm.rs`.

## Key Reuse from If Statements

1. **Basic Block Management**: Same `create_basic_block()` and `switch_to_basic_block()` mechanisms
2. **Condition Handling**: Identical boolean expression validation and IR generation  
3. **Control Flow Instructions**: Reuse existing `Jump` and `Branch` IR instructions
4. **Symbol Table Scoping**: Same block-level scoping as if statement bodies
5. **LLVM Generation**: Existing `handle_jump()` and `handle_branch()` methods work unchanged

## Control Flow Pattern

```
Entry Block
    ↓ (jump)
Condition Block ←──┐
    ↓ (branch)     │ (jump back)
Body Block ────────┘
    ↓ (if condition false)
Merge Block
```

This design leverages all the existing basic block infrastructure while creating the loop-back pattern that distinguishes while loops from if statements.

## Implementation Status

### Completed (commit 2e8b28e)

1. ✅ `parser/src/grammar.pest` - Added while statement grammar
2. ✅ `parser/src/ast.rs` - Added WhileStatement struct and Statement::While variant
3. ✅ `parser/src/parser.rs` - Added while statement parsing logic
4. ✅ `semantic_analysis/src/phase_top_level_declaration_collector.rs` - Added while statement mapping
5. ✅ `semantic_analysis/src/phase_type_resolver.rs` - Added while statement type checking
6. ✅ `semantic_analysis/src/ast_typed.rs` - Added typed AST support
7. ✅ `semantic_analysis/src/semantic_analyzer.rs` - Added semantic analysis integration
8. ✅ `parser/src/parsed_ast.rs` - Added parsed AST support

### Completed (commit 5b3a59d)

1. ✅ `codegen/src/ir_builder.rs` - Completed while statement IR generation with handle_while_statement method
2. ✅ Added comprehensive tests for while loop IR generation (simple loops, early returns, variable scoping)
3. ✅ All 183 tests pass including new while loop tests

### Remaining Work

1. LLVM backend integration (may already work with existing Jump/Branch instructions)
2. End-to-end testing with LLVM backend

## Testing Strategy

- Basic while loop with simple condition
- While loop with complex boolean expressions
- Nested while loops
- While loops with early returns
- Variable scoping within while loop bodies
- Integration with existing control flow (if statements inside while loops)