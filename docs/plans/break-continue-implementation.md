# Break and Continue Implementation Plan

## Current Implementation Analysis

**Parser**: Only `while` loops exist (grammar.pest:24), parsed into `Statement::While` variant  
**Semantic Analysis**: Type-checks while condition as boolean (phase_type_resolver.rs:345-378)  
**IR Generation**: Creates condition/body/merge blocks with Jump/Branch instructions (ir_builder.rs:381-413)  
**LLVM Backend**: Handles Jump/Branch with unconditional/conditional branches (ir_to_llvm.rs:849-871)

## Implementation Plan

### Phase 1: Parser Changes
1. **Grammar extension** (grammar.pest:18):
   - Add `breakStatement = { "break" }` 
   - Add `continueStatement = { "continue" }`
   - Update `statement` rule to include both

2. **AST extension** (parser/src/ast.rs:55):
   - Add `Break` and `Continue` variants to `Statement` enum
   - Update Display implementations

3. **Parser logic** (parser/src/parser.rs):
   - Add parsing rules for break/continue statements

4. **Testing Phase 1**:
   - Unit tests for parsing break/continue statements
   - Snapshot tests for AST structure
   - Test parser error handling for malformed break/continue

### Phase 2: Semantic Analysis Changes
1. **Loop context tracking** (semantic_analysis/src/phase_type_resolver.rs):
   - Add `LoopContext` struct to track current loop state
   - Modify `analyze_statement` to push/pop loop context during while analysis
   - Add validation for break/continue only within loops

2. **Error handling** (semantic_analysis/src/semantic_analyzer.rs):
   - Add `BreakOutsideLoop` and `ContinueOutsideLoop` error variants

3. **Testing Phase 2**:
   - Unit tests for semantic validation (break/continue inside/outside loops)
   - Error message tests for invalid usage
   - Integration tests combining parser + semantic analysis

### Phase 3: IR Generation Changes  
1. **Loop target tracking** (codegen/src/ir_builder.rs:381):
   - Modify `handle_while_statement` to track break (merge) and continue (condition) target blocks
   - Pass loop targets through statement handling context

2. **New IR instructions** (codegen/src/ir.rs:58):
   - Add `Break { target_block: BlockId }` and `Continue { target_block: BlockId }` to `InstructionPayload`
   - Update instruction type methods

3. **Statement handling**:
   - Add break/continue cases to `handle_statement` method
   - Generate appropriate jump instructions to target blocks

4. **Testing Phase 3**:
   - Unit tests for IR generation of break/continue
   - Snapshot tests for generated IR structure
   - Integration tests through semantic analysis → IR generation

### Phase 4: LLVM Backend Changes
1. **Instruction handling** (backend_llvm/src/ir_to_llvm.rs:260):
   - Add cases for `Break` and `Continue` instruction payloads
   - Both generate unconditional branches using existing `handle_jump` method

2. **Testing Phase 4**:
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