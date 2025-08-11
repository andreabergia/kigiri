# Break and Continue Implementation Plan

## Current Implementation Analysis

**Parser**: Only `while` loops exist (grammar.pest:24), parsed into `Statement::While` variant  
**Semantic Analysis**: Type-checks while condition as boolean (phase_type_resolver.rs:345-378)  
**IR Generation**: Creates condition/body/merge blocks with Jump/Branch instructions (ir_builder.rs:381-413)  
**LLVM Backend**: Handles Jump/Branch with unconditional/conditional branches (ir_to_llvm.rs:849-871)

## Implementation Plan

### ✅ Phase 1: Parser Changes (COMPLETED)
1. **✅ Grammar extension** (parser/src/grammar.pest:25-26):
   - Added `breakStatement = { "break" }` 
   - Added `continueStatement = { "continue" }`
   - Updated `statement` rule to include both

2. **✅ AST extension** (parser/src/ast.rs:74-75):
   - Added `Break` and `Continue` variants to `Statement` enum
   - Updated Display implementations (lines 285-290)

3. **✅ Parser logic** (parser/src/parser.rs:354-355):
   - Added parsing rules for break/continue statements
   - Added `statement_break()` and `statement_continue()` methods to ParsedAstAllocator

4. **✅ Testing Phase 1**:
   - Added unit tests for parsing break/continue statements (lines 756-799)
   - Added snapshot test for AST structure (lines 883-921) 
   - Added parser error handling tests for missing semicolons (lines 923-951)
   - All 80 parser tests passing ✅

**Result**: Parser now successfully parses `break;` and `continue;` statements into appropriate AST nodes.

### 🔄 Phase 2: Semantic Analysis Changes (READY)
**Current Status**: Project compiles with `todo!()` placeholders in place

1. **Replace todo!() placeholders with proper implementation**:
   - `semantic_analysis/src/ast_typed.rs:230` - Implement Break/Continue cases
   - `semantic_analysis/src/phase_top_level_declaration_collector.rs:106` - Implement Break/Continue cases  
   - `semantic_analysis/src/phase_type_resolver.rs:159` - Implement Break/Continue cases

2. **Loop context tracking** (semantic_analysis/src/phase_type_resolver.rs):
   - Add `LoopContext` struct to track current loop state
   - Modify `analyze_statement` to push/pop loop context during while analysis
   - Add validation for break/continue only within loops

3. **Error handling** (semantic_analysis/src/semantic_analyzer.rs):
   - Add `BreakOutsideLoop` and `ContinueOutsideLoop` error variants

4. **Testing Phase 2**:
   - Unit tests for semantic validation (break/continue inside/outside loops)
   - Error message tests for invalid usage
   - Integration tests combining parser + semantic analysis

### 📋 Phase 3: IR Generation Changes (PLANNED)  
1. **Replace todo!() placeholders** (codegen/src/ir_builder.rs):
   - Implement Break/Continue cases in statement handling

2. **Loop target tracking** (codegen/src/ir_builder.rs:381):
   - Modify `handle_while_statement` to track break (merge) and continue (condition) target blocks
   - Pass loop targets through statement handling context

3. **New IR instructions** (codegen/src/ir.rs:58):
   - Add `Break { target_block: BlockId }` and `Continue { target_block: BlockId }` to `InstructionPayload`
   - Update instruction type methods

4. **Statement handling**:
   - Add break/continue cases to `handle_statement` method
   - Generate appropriate jump instructions to target blocks

5. **Testing Phase 3**:
   - Unit tests for IR generation of break/continue
   - Snapshot tests for generated IR structure
   - Integration tests through semantic analysis → IR generation

### 📋 Phase 4: LLVM Backend Changes (PLANNED)
1. **Replace todo!() placeholders** (backend_llvm/src/ir_to_llvm.rs):
   - Implement Break/Continue cases in instruction handling

2. **Instruction handling** (backend_llvm/src/ir_to_llvm.rs:260):
   - Add cases for `Break` and `Continue` instruction payloads
   - Both generate unconditional branches using existing `handle_jump` method

3. **Testing Phase 4**:
   - Unit tests for LLVM code generation
   - End-to-end integration tests for complete compilation pipeline
   - Runtime behavior tests:
     - Simple break/continue in while loop
     - Nested loops with break/continue  
     - Early returns combined with break/continue

## Key Implementation Notes

- Break/continue are essentially structured jumps to specific loop control blocks
- Leverages existing Jump instruction infrastructure in IR and LLVM backend
- Requires loop context tracking for semantic validation
- Minimal changes needed to LLVM backend due to reuse of existing jump handling

## Progress Summary

- **✅ Phase 1 (Parser)**: Complete - Successfully parses break/continue statements
- **🔄 Phase 2 (Semantic Analysis)**: Ready to start - Replace `todo!()` placeholders  
- **📋 Phase 3 (IR Generation)**: Waiting for Phase 2 completion
- **📋 Phase 4 (LLVM Backend)**: Waiting for Phase 3 completion

## Current Status

The project compiles successfully with `todo!()` placeholders handling the new Break/Continue AST variants across all compilation phases. Phase 2 (Semantic Analysis) is ready to be implemented by replacing these placeholders with proper logic.