use crate::ir::{BasicBlock, Function, FunctionArgument, Instruction, IrAllocator, Module};
use crate::{FunctionSignature, ir};
use ir::Variable;
use kigiri_memory::BumpVec;
use parser::{
    Block, BlockId, Expression, FunctionDeclaration, IfElseBlock, IfStatement, Statement,
    WhileStatement,
};
use semantic_analysis::{PhaseTypeResolved, Symbol, SymbolKind, SymbolTable, Type, VariableIndex};
use std::cell::RefCell;

struct FunctionIrBuilder<'i> {
    ir_allocator: &'i IrAllocator,
    pub(crate) first_bb: &'i BasicBlock<'i>,
    current_bb: RefCell<&'i BasicBlock<'i>>,
    basic_blocks: RefCell<BumpVec<'i, &'i BasicBlock<'i>>>,
}

#[derive(Debug, PartialEq)]
enum FoundReturn {
    Yes,
    No,
}

impl FoundReturn {
    fn and(&self, other: FoundReturn) -> FoundReturn {
        match (self, other) {
            (FoundReturn::Yes, FoundReturn::Yes) => FoundReturn::Yes,
            _ => FoundReturn::No,
        }
    }
}

impl<'i> FunctionIrBuilder<'i> {
    fn new(ir_allocator: &'i IrAllocator) -> Self {
        ir_allocator.reset_block_id();
        ir_allocator.reset_instruction_id();
        let basic_block = ir_allocator.basic_block();
        let mut basic_blocks = ir_allocator.basic_blocks();
        basic_blocks.push(basic_block);
        Self {
            ir_allocator,
            first_bb: basic_block,
            current_bb: RefCell::new(basic_block),
            basic_blocks: RefCell::new(basic_blocks),
        }
    }

    fn generate(&self, function: &FunctionDeclaration<PhaseTypeResolved>) -> &'i Function<'i> {
        let signature = self.generate_function_signature(function);

        let first_bb = self.first_bb;
        let found_return = self.handle_block(function.body);
        if found_return == FoundReturn::No {
            // If no return statement was found, we add an implicit return
            self.push_to_current_bb(self.ir_allocator.new_ret());
        }

        // Take ownership of the basic_blocks by creating a new vector and copying
        let mut new_basic_blocks = self.ir_allocator.basic_blocks();
        for bb in self.basic_blocks.borrow().iter() {
            new_basic_blocks.push(*bb);
        }
        self.ir_allocator
            .function(signature, new_basic_blocks, first_bb.id)
    }

    fn generate_function_signature(
        &self,
        function: &FunctionDeclaration<PhaseTypeResolved>,
    ) -> &'i FunctionSignature<'i> {
        self.ir_allocator.function_signature(
            function.signature.name,
            function.signature.return_type,
            self.ir_allocator
                .function_arguments(function.signature.arguments.iter().map(|arg| {
                    let argument_type = if let SymbolKind::Argument { argument_type, .. } = arg.kind
                    {
                        argument_type
                    } else {
                        panic!("expected an argument symbol kind for function argument");
                    };
                    FunctionArgument {
                        name: arg.name,
                        argument_type,
                    }
                })),
        )
    }
    fn handle_block(&self, block: &Block<PhaseTypeResolved>) -> FoundReturn {
        let mut found_return = FoundReturn::No;
        for statement in &block.statements {
            if self.handle_statement(statement, block.symbol_table) == FoundReturn::Yes {
                found_return = FoundReturn::Yes;
            }
        }
        found_return
    }

    fn handle_statement(
        &self,
        statement: &Statement<PhaseTypeResolved>,
        symbol_table: &SymbolTable,
    ) -> FoundReturn {
        match statement {
            Statement::Let { initializers } => {
                for initializer in initializers {
                    let symbol = symbol_table
                        .lookup_by_id(initializer.variable)
                        .expect("should find symbol in symbol table");
                    let value = self.handle_expression(initializer.value, symbol_table);

                    let SymbolKind::Variable {
                        index,
                        variable_type,
                    } = symbol.kind
                    else {
                        panic!("expected a variable symbol kind for let statement");
                    };
                    let instruction =
                        self.ir_allocator
                            .new_let(index, symbol.name, variable_type, value.id);
                    self.push_to_current_bb(instruction);
                    self.push_variable_to_current_bb(index, symbol, variable_type);
                }
                FoundReturn::No
            }
            Statement::Assignment {
                target: symbol,
                expression,
            } => {
                let symbol = symbol_table
                    .lookup_by_id(*symbol)
                    .expect("should find symbol in symbol table");
                let value = self.handle_expression(expression, symbol_table);

                let (variable_index, variable_type) = if let SymbolKind::Variable {
                    index,
                    variable_type,
                } = symbol.kind
                {
                    (index, variable_type)
                } else {
                    panic!("expected a variable symbol kind for let statement");
                };
                let instruction =
                    self.ir_allocator
                        .new_store(symbol.name, variable_type, variable_index, value);
                self.push_to_current_bb(instruction);
                FoundReturn::No
            }
            Statement::Return { expression } => {
                if let Some(value) = expression {
                    let instruction = self.handle_expression(value, symbol_table);
                    self.push_to_current_bb(self.ir_allocator.new_ret_expr(instruction));
                } else {
                    self.push_to_current_bb(self.ir_allocator.new_ret())
                }
                FoundReturn::Yes
            }
            Statement::Expression { expression } => {
                self.handle_expression(expression, symbol_table);
                FoundReturn::No
            }
            Statement::NestedBlock { .. } => todo!(),
            Statement::If(if_statement) => self.handle_if_statement(if_statement, symbol_table),
            Statement::While(while_statement) => {
                self.handle_while_statement(while_statement, symbol_table)
            }
        }
    }

    fn handle_expression(
        &self,
        expression: &Expression<PhaseTypeResolved>,
        symbol_table: &SymbolTable,
    ) -> &'i Instruction {
        match expression {
            Expression::Identifier {
                name: symbol_id, ..
            } => {
                let symbol = symbol_table
                    .lookup_by_id(*symbol_id)
                    .expect("should find identifier in symbol table");

                let instruction = match symbol.kind {
                    SymbolKind::Function { .. } => todo!(),
                    SymbolKind::Variable {
                        index,
                        variable_type,
                    } => self
                        .ir_allocator
                        .new_load_var(symbol.name, variable_type, index),
                    SymbolKind::Argument {
                        index,
                        argument_type,
                    } => self
                        .ir_allocator
                        .new_load_arg(symbol.name, argument_type, index),
                };

                self.push_to_current_bb(instruction);
                instruction
            }
            Expression::Literal { value, .. } => {
                let instruction = self.ir_allocator.new_const(value.clone());
                self.push_to_current_bb(instruction);
                instruction
            }
            Expression::Unary {
                operator, operand, ..
            } => {
                let operand_instruction = self.handle_expression(operand, symbol_table);

                let instruction = self
                    .ir_allocator
                    .new_unary(operator.clone(), operand_instruction);
                self.push_to_current_bb(instruction);
                instruction
            }
            Expression::Binary {
                result_type,
                operator,
                operand_type,
                left,
                right,
            } => {
                let left_instruction = self.handle_expression(left, symbol_table);
                let right_instruction = self.handle_expression(right, symbol_table);

                let instruction = self.ir_allocator.new_binary(
                    operator.clone(),
                    result_type,
                    operand_type,
                    left_instruction,
                    right_instruction,
                );
                self.push_to_current_bb(instruction);
                instruction
            }
            Expression::FunctionCall {
                name,
                args,
                return_type,
            } => {
                // Look up the function symbol to get the function name
                let function_symbol = symbol_table
                    .lookup_by_id(*name)
                    .expect("should find function in symbol table");

                // Generate IR for each argument
                let mut argument_instructions = Vec::new();
                for arg in args.iter() {
                    let arg_instruction = self.handle_expression(arg, symbol_table);
                    argument_instructions.push(arg_instruction);
                }

                // Create the function call instruction
                let instruction = self.ir_allocator.new_call(
                    function_symbol.name,
                    *return_type,
                    argument_instructions,
                );

                self.push_to_current_bb(instruction);
                instruction
            }
        }
    }

    fn handle_if_statement(
        &self,
        if_statement: &IfStatement<PhaseTypeResolved>,
        symbol_table: &SymbolTable,
    ) -> FoundReturn {
        let merge_block = self.create_basic_block_deferred();
        let result = self.handle_if_logic(if_statement, symbol_table, merge_block);

        // Merge block at the end
        self.add_basic_block(merge_block);
        self.switch_to_basic_block(merge_block);

        result
    }

    fn handle_if_else_block(
        &self,
        else_block: &IfElseBlock<PhaseTypeResolved>,
        symbol_table: &SymbolTable,
        merge_block: &'i BasicBlock<'i>,
    ) -> FoundReturn {
        match else_block {
            IfElseBlock::Block(block) => self.handle_then_else_block(block, merge_block.id),
            IfElseBlock::If(nested_if) => {
                self.handle_if_logic(nested_if, symbol_table, merge_block)
            }
        }
    }

    fn handle_if_logic(
        &self,
        if_statement: &IfStatement<PhaseTypeResolved>,
        symbol_table: &SymbolTable,
        merge_block: &'i BasicBlock<'i>,
    ) -> FoundReturn {
        // Handle "then"
        let then_block = self.create_basic_block();
        let else_bb = if if_statement.else_block.is_some() {
            Some(self.create_basic_block())
        } else {
            None
        };

        // Branch depending on the condition
        let condition_instruction = self.handle_expression(if_statement.condition, symbol_table);
        let branch_instruction = if let Some(else_bb) = else_bb {
            self.ir_allocator
                .new_branch(condition_instruction, then_block.id, else_bb.id)
        } else {
            self.ir_allocator
                .new_branch(condition_instruction, then_block.id, merge_block.id)
        };
        self.push_to_current_bb(branch_instruction);

        // Generate then block
        self.switch_to_basic_block(then_block);
        let then_has_return = self.handle_then_else_block(if_statement.then_block, merge_block.id);

        // Generate else block if present
        let mut else_has_return = FoundReturn::No;
        if let Some(else_bb) = else_bb {
            if let Some(else_block_ast) = if_statement.else_block {
                self.switch_to_basic_block(else_bb);
                else_has_return =
                    self.handle_if_else_block(else_block_ast, symbol_table, merge_block);
            }
        }

        // Return whether both branches have returns
        then_has_return.and(else_has_return)
    }

    fn handle_while_statement(
        &self,
        while_statement: &WhileStatement<PhaseTypeResolved>,
        symbol_table: &SymbolTable,
    ) -> FoundReturn {
        let condition_block = self.create_basic_block();
        let body_block = self.create_basic_block();
        let merge_block = self.create_basic_block_deferred();

        self.push_to_current_bb(self.ir_allocator.new_jump(condition_block.id));

        // Condition block
        self.switch_to_basic_block(condition_block);
        let condition_instruction = self.handle_expression(while_statement.condition, symbol_table);
        let branch_instruction =
            self.ir_allocator
                .new_branch(condition_instruction, body_block.id, merge_block.id);
        self.push_to_current_bb(branch_instruction);

        // Body block
        self.switch_to_basic_block(body_block);
        let body_has_return = self.handle_block(while_statement.body);
        if body_has_return == FoundReturn::No {
            self.push_to_current_bb(self.ir_allocator.new_jump(condition_block.id));
        }

        // Merge block
        self.add_basic_block(merge_block);
        self.switch_to_basic_block(merge_block);

        FoundReturn::No // While loops don't guarantee returns
    }

    /// Generates statements for the block and a jump to the merge block if no return is found
    fn handle_then_else_block(
        &self,
        block: &Block<PhaseTypeResolved>,
        merge_block_id: BlockId,
    ) -> FoundReturn {
        let found_return = self.handle_block(block);
        if found_return == FoundReturn::No {
            let jump_instruction = self.ir_allocator.new_jump(merge_block_id);
            self.push_to_current_bb(jump_instruction);
        }
        found_return
    }

    fn create_basic_block(&self) -> &'i BasicBlock<'i> {
        let bb = self.ir_allocator.basic_block();
        self.basic_blocks.borrow_mut().push(bb);
        bb
    }

    fn create_basic_block_deferred(&self) -> &'i BasicBlock<'i> {
        self.ir_allocator.basic_block()
    }

    fn add_basic_block(&self, bb: &'i BasicBlock<'i>) {
        self.basic_blocks.borrow_mut().push(bb);
    }

    fn switch_to_basic_block(&self, bb: &'i BasicBlock<'i>) {
        *self.current_bb.borrow_mut() = bb;
    }

    fn push_to_current_bb(&self, instruction: &'i Instruction) {
        self.current_bb
            .borrow()
            .instructions
            .borrow_mut()
            .push(instruction);
    }

    fn push_variable_to_current_bb(
        &self,
        variable_index: VariableIndex,
        symbol: &Symbol,
        variable_type: Type,
    ) {
        self.current_bb
            .borrow()
            .variables
            .borrow_mut()
            .push(Variable {
                index: variable_index,
                name: symbol.name,
                variable_type,
            });
    }
}

pub fn build_ir_module<'i>(
    ir_allocator: &'i IrAllocator,
    module: &parser::Module<PhaseTypeResolved>,
) -> &'i Module<'i> {
    let mut functions = ir_allocator.functions();
    for function in &module.functions {
        let fn_builder = FunctionIrBuilder::new(ir_allocator);
        functions.push(fn_builder.generate(function));
    }
    ir_allocator.module(module.name, functions)
}

#[cfg(test)]
mod tests {
    use super::*;
    use semantic_analysis::SemanticAnalyzer;

    fn analyze_module<'i>(ir_allocator: &'i IrAllocator, source: &str) -> &'i Module<'i> {
        let ast_allocator = parser::ParsedAstAllocator::default();
        let ast_module = parser::parse(&ast_allocator, "test", source);

        let semantic_analyzer = SemanticAnalyzer::default();
        let typed_module = semantic_analyzer
            .analyze_module(ast_module)
            .expect("should have passed semantic analysis");

        build_ir_module(ir_allocator, typed_module)
    }

    macro_rules! test_module_ir {
        ($name: ident, $source: expr, $expected: expr) => {
            #[test]
            fn $name() {
                let ir_allocator = IrAllocator::new();
                let module = analyze_module(&ir_allocator, $source);
                assert_eq!(module.to_string(), $expected);
            }
        };
    }

    test_module_ir!(
        fn_constant,
        r"fn one() -> int {
    return 1;
}",
        r"module test

fn one(
) -> i {
  entry_block: #0
  { #0
    00000 i const 1i
    00001 i ret @0
  }
}
"
    );
    test_module_ir!(
        fn_unary,
        r"fn neg(x: int) -> int {
    return - x;
}",
        r"module test

fn neg(
  x: int,
) -> i {
  entry_block: #0
  { #0
    00000 i loadarg x
    00001 i neg @0
    00002 i ret @1
  }
}
"
    );

    test_module_ir!(
        fn_binary,
        r"fn add_one(x: double) -> double {
    return 1.0 + x;
}",
        r"module test

fn add_one(
  x: double,
) -> d {
  entry_block: #0
  { #0
    00000 d const 1d
    00001 d loadarg x
    00002 d add @0, @1
    00003 d ret @2
  }
}
"
    );
    test_module_ir!(
        multiple_fn_reset_ir_counter,
        r"fn one() -> int { return 1; }
fn two() -> int { return 2; }",
        r"module test

fn one(
) -> i {
  entry_block: #0
  { #0
    00000 i const 1i
    00001 i ret @0
  }
}
fn two(
) -> i {
  entry_block: #0
  { #0
    00000 i const 2i
    00001 i ret @0
  }
}
"
    );
    test_module_ir!(
        implicit_return_is_generated,
        "fn empty() { }",
        r"module test

fn empty(
) -> void {
  entry_block: #0
  { #0
    00000 v ret
  }
}
"
    );
    test_module_ir!(
        variable_declaration,
        r"fn var() -> bool {
    let y = true;
    return y;
}",
        r"module test

fn var(
) -> b {
  entry_block: #0
  { #0
    var y: bool
    00000 b const true
    00001 b let y = @0
    00002 b loadvar y
    00003 b ret @2
  }
}
"
    );
    test_module_ir!(
        multiple_variable_declaration,
        r"fn var() { 
    let y = 1, z = 2;
}",
        r"module test

fn var(
) -> void {
  entry_block: #0
  { #0
    var y: int
    var z: int
    00000 i const 1i
    00001 i let y = @0
    00002 i const 2i
    00003 i let z = @2
    00004 v ret
  }
}
"
    );
    test_module_ir!(
        variable_assignment,
        r"fn var() -> int {
    let y = 1;
    y = 2;
    return y;
}",
        r"module test

fn var(
) -> i {
  entry_block: #0
  { #0
    var y: int
    00000 i const 1i
    00001 i let y = @0
    00002 i const 2i
    00003 i storevar y = @2
    00004 i loadvar y
    00005 i ret @4
  }
}
"
    );
    test_module_ir!(
        argument_reassignment,
        r"fn arg_assign(x: int) -> int {
    x = x + 1;
    return x;
}",
        r"module test

fn arg_assign(
  x: int,
) -> i {
  entry_block: #0
  { #0
    var x: int
    00000 i loadarg x
    00001 i const 1i
    00002 i add @0, @1
    00003 i let x = @2
    00004 i loadvar x
    00005 i ret @4
  }
}
"
    );

    test_module_ir!(
        function_call_no_args,
        r"fn get_five() -> int { return 5; }
fn main() -> int {
    return get_five();
}",
        r"module test

fn get_five(
) -> i {
  entry_block: #0
  { #0
    00000 i const 5i
    00001 i ret @0
  }
}
fn main(
) -> i {
  entry_block: #0
  { #0
    00000 i call get_five()
    00001 i ret @0
  }
}
"
    );

    test_module_ir!(
        function_call_with_args,
        r"fn add(x: int, y: int) -> int { return x + y; }
fn main() -> int {
    return add(3, 7);
}",
        r"module test

fn add(
  x: int,
  y: int,
) -> i {
  entry_block: #0
  { #0
    00000 i loadarg x
    00001 i loadarg y
    00002 i add @0, @1
    00003 i ret @2
  }
}
fn main(
) -> i {
  entry_block: #0
  { #0
    00000 i const 3i
    00001 i const 7i
    00002 i call add(@0, @1)
    00003 i ret @2
  }
}
"
    );

    test_module_ir!(
        function_call_void,
        r"fn print_hello() { }
fn main() {
    print_hello();
}",
        r"module test

fn print_hello(
) -> void {
  entry_block: #0
  { #0
    00000 v ret
  }
}
fn main(
) -> void {
  entry_block: #0
  { #0
    00000 v call print_hello()
    00001 v ret
  }
}
"
    );

    test_module_ir!(
        if_statement_simple,
        r"fn test(x: bool) -> int {
    if (x) {
        return 1;
    }
    return 2;
}",
        r"module test

fn test(
  x: bool,
) -> i {
  entry_block: #0
  { #0
    00000 b loadarg x
    00001 v br @0, #2, #1
  }
  { #2
    00002 i const 1i
    00003 i ret @2
  }
  { #1
    00004 i const 2i
    00005 i ret @4
  }
}
"
    );

    test_module_ir!(
        if_statement_with_else,
        r"fn test(x: bool) -> int {
    if (x) {
        return 1;
    } else {
        return 2;
    }
}",
        r"module test

fn test(
  x: bool,
) -> i {
  entry_block: #0
  { #0
    00000 b loadarg x
    00001 v br @0, #2, #3
  }
  { #2
    00002 i const 1i
    00003 i ret @2
  }
  { #3
    00004 i const 2i
    00005 i ret @4
  }
  { #1
  }
}
"
    );

    test_module_ir!(
        if_elseif_else,
        r"fn test(x: int) -> int {
    let result = 0;
    if (x > 10) {
        result = 1;
    } else if (x > 5) {
        result = 2;
    } else {
        result = 3;
    }
    return result;
}",
        r"module test

fn test(
  x: int,
) -> i {
  entry_block: #0
  { #0
    var result: int
    00000 i const 0i
    00001 i let result = @0
    00002 i loadarg x
    00003 i const 10i
    00004 b gt @2, @3
    00005 v br @4, #2, #3
  }
  { #2
    00006 i const 1i
    00007 i storevar result = @6
    00008 v jmp #1
  }
  { #3
    00009 i loadarg x
    00010 i const 5i
    00011 b gt @9, @10
    00012 v br @11, #4, #5
  }
  { #4
    00013 i const 2i
    00014 i storevar result = @13
    00015 v jmp #1
  }
  { #5
    00016 i const 3i
    00017 i storevar result = @16
    00018 v jmp #1
  }
  { #1
    00019 i loadvar result
    00020 i ret @19
  }
}
"
    );

    test_module_ir!(
        variable_can_be_declared_in_ifs,
        r"
fn test(condition: bool) -> int {
    let r = 1;
    if condition {
        let x = 2;
        return x + r;
    }
    return r;
}",
        r"module test

fn test(
  condition: bool,
) -> i {
  entry_block: #0
  { #0
    var r: int
    00000 i const 1i
    00001 i let r = @0
    00002 b loadarg condition
    00003 v br @2, #2, #1
  }
  { #2
    var x: int
    00004 i const 2i
    00005 i let x = @4
    00006 i loadvar x
    00007 i loadvar r
    00008 i add @6, @7
    00009 i ret @8
  }
  { #1
    00010 i loadvar r
    00011 i ret @10
  }
}
"
    );

    test_module_ir!(
        while_simple,
        r"fn test() -> int {
    let x = 0;
    while (x < 10) {
        x = x + 1;
    }
    return x;
}",
        r"module test

fn test(
) -> i {
  entry_block: #0
  { #0
    var x: int
    00000 i const 0i
    00001 i let x = @0
    00002 v jmp #1
  }
  { #1
    00003 i loadvar x
    00004 i const 10i
    00005 b lt @3, @4
    00006 v br @5, #2, #3
  }
  { #2
    00007 i loadvar x
    00008 i const 1i
    00009 i add @7, @8
    00010 i storevar x = @9
    00011 v jmp #1
  }
  { #3
    00012 i loadvar x
    00013 i ret @12
  }
}
"
    );

    test_module_ir!(
        while_with_early_return,
        r"fn test() -> int {
    let x = 0;
    while (x < 10) {
        if (x == 5) {
            return x;
        }
        x = x + 1;
    }
    return x;
}",
        r"module test

fn test(
) -> i {
  entry_block: #0
  { #0
    var x: int
    00000 i const 0i
    00001 i let x = @0
    00002 v jmp #1
  }
  { #1
    00003 i loadvar x
    00004 i const 10i
    00005 b lt @3, @4
    00006 v br @5, #2, #3
  }
  { #2
    00007 i loadvar x
    00008 i const 5i
    00009 b eq @7, @8
    00010 v br @9, #5, #4
  }
  { #5
    00011 i loadvar x
    00012 i ret @11
  }
  { #4
    00013 i loadvar x
    00014 i const 1i
    00015 i add @13, @14
    00016 i storevar x = @15
    00017 v jmp #1
  }
  { #3
    00018 i loadvar x
    00019 i ret @18
  }
}
"
    );

    test_module_ir!(
        while_variable_scope,
        r"fn test() -> int {
    let sum = 0;
    let i = 0;
    while (i < 5) {
        let temp = i * 2;
        sum = sum + temp;
        i = i + 1;
    }
    return sum;
}",
        r"module test

fn test(
) -> i {
  entry_block: #0
  { #0
    var sum: int
    var i: int
    00000 i const 0i
    00001 i let sum = @0
    00002 i const 0i
    00003 i let i = @2
    00004 v jmp #1
  }
  { #1
    00005 i loadvar i
    00006 i const 5i
    00007 b lt @5, @6
    00008 v br @7, #2, #3
  }
  { #2
    var temp: int
    00009 i loadvar i
    00010 i const 2i
    00011 i mul @9, @10
    00012 i let temp = @11
    00013 i loadvar sum
    00014 i loadvar temp
    00015 i add @13, @14
    00016 i storevar sum = @15
    00017 i loadvar i
    00018 i const 1i
    00019 i add @17, @18
    00020 i storevar i = @19
    00021 v jmp #1
  }
  { #3
    00022 i loadvar sum
    00023 i ret @22
  }
}
"
    );
}
