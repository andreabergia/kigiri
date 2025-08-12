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

### ✅ Phase 2: Semantic Analysis Changes (COMPLETED)

1. **✅ Replaced todo!() placeholders with proper implementation**:
   - `semantic_analysis/src/ast_typed.rs:285-290` - Fixed Display implementation for Break/Continue
   - `semantic_analysis/src/phase_top_level_declaration_collector.rs:161-162` - Pass through Break/Continue statements
   - `semantic_analysis/src/phase_type_resolver.rs:393-404` - Validate break/continue within loop context

2. **✅ Loop context tracking** (semantic_analysis/src/phase_type_resolver.rs):
   - Added `in_loop: bool` parameter to `analyze_block()`, `analyze_statement()`, and `analyze_if_else_block()` methods
   - Function bodies start with `in_loop: false` (line 128)
   - While statement analysis passes `in_loop: true` when analyzing body blocks (line 411)
   - Loop context propagated through nested blocks (line 328) and if/else statements (lines 363, 373, 444, 488, 494)

3. **✅ Error handling** (semantic_analysis/src/semantic_analyzer.rs:74-77):
   - Added `BreakOutsideLoop` and `ContinueOutsideLoop` error variants with proper error messages

4. **✅ Testing Phase 2** (semantic_analysis/src/semantic_analyzer.rs:804-906):
   - Added comprehensive test cases for break/continue validation:
     - `break_in_while_loop` - Valid break inside while loop
     - `continue_in_while_loop` - Valid continue inside while loop  
     - `break_and_continue_in_nested_blocks` - Valid usage in nested if/else within while
     - `break_outside_loop` - Error case for break outside loop
     - `continue_outside_loop` - Error case for continue outside loop
     - `break_in_if_outside_loop` - Error case for break in if statement outside loop
     - `continue_in_if_outside_loop` - Error case for continue in if statement outside loop

### 🔄 Phase 3: IR Generation Changes (READY)  
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
- **✅ Phase 2 (Semantic Analysis)**: Complete - Loop context tracking and validation implemented
- **🔄 Phase 3 (IR Generation)**: Ready to start - Replace `todo!()` placeholders in codegen
- **📋 Phase 4 (LLVM Backend)**: Waiting for Phase 3 completion

## Current Status

Phase 2 (Semantic Analysis) has been completed successfully. The implementation uses a clean approach:

- **Loop context tracking**: Added `in_loop: bool` parameter to core analysis methods, avoiding complex state management
- **Simple propagation**: Function bodies start with `in_loop: false`, while loop bodies use `in_loop: true`
- **Semantic validation**: Break and continue statements validated at lines 393-404 with clear error handling
- **Comprehensive testing**: 7 new test cases covering valid and invalid usage scenarios

The semantic analysis correctly validates break/continue statements and passes all tests. The implementation is simpler than originally planned, avoiding the need for dedicated context tracking structures. Phase 3 (IR Generation) is ready to begin.