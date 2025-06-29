use codegen::{Function, Instruction, InstructionId, InstructionPayload, LiteralValue};
use inkwell::IntPredicate;
use inkwell::builder::{Builder, BuilderError};
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::FunctionType;
use inkwell::values::{FunctionValue, IntValue, PointerValue};
use parser::{BinaryOperator, UnaryOperator, resolve_string_id};
use semantic_analysis::{SymbolKind, Type, VariableIndex};
use std::cell::RefCell;
use thiserror::Error;

#[derive(Debug, PartialEq, Error)]
#[error("Code generation error: {message}")]
struct CodeGenError {
    message: String,
}

impl From<BuilderError> for CodeGenError {
    fn from(value: BuilderError) -> Self {
        Self {
            message: value.to_string(),
        }
    }
}

struct LlvmFunctionGenerator<'c, 'c2, 'ir, 'ir2> {
    context: &'c Context,
    builder: &'c2 Builder<'c>,
    function: &'ir Function<'ir2>,

    // Vectors are indexed by instruction id. There's a bit of space wasted,
    // but it makes everything quite simple and fast.
    int_values: RefCell<Vec<Option<IntValue<'c>>>>,
    bool_values: RefCell<Vec<Option<IntValue<'c>>>>,

    // Variables are indexed by their progressive number
    int_bool_variable: RefCell<Vec<PointerValue<'c>>>,
}

enum IntOrBool {
    Int,
    Bool,
}

impl IntOrBool {
    fn from_type(t: &Type) -> Self {
        match t {
            Type::Int => IntOrBool::Int,
            Type::Boolean => IntOrBool::Bool,
            _ => panic!("unexpected type in IntOrBool"),
        }
    }
}

impl<'c, 'c2, 'ir, 'ir2> LlvmFunctionGenerator<'c, 'c2, 'ir, 'ir2> {
    fn new(context: &'c Context, builder: &'c2 Builder<'c>, function: &'ir Function<'ir2>) -> Self {
        let num_instructions = function.body.instructions.borrow().len();

        let mut int_values = Vec::with_capacity(num_instructions);
        int_values.resize(num_instructions, None);
        let mut bool_values = Vec::with_capacity(num_instructions);
        bool_values.resize(num_instructions, None);

        let int_bool_variable = Vec::with_capacity(function.body.variables.borrow().len());

        Self {
            context,
            builder,
            function,
            int_values: int_values.into(),
            bool_values: bool_values.into(),
            int_bool_variable: int_bool_variable.into(),
        }
    }

    fn alloca_variables(&self) -> Result<(), CodeGenError> {
        for var in self.function.body.variables.borrow().iter() {
            let value = self.builder.build_alloca(
                match var.variable_type {
                    Type::Int => self.context.i64_type(),
                    Type::Boolean => self.context.bool_type(),
                    Type::Double => todo!(),
                },
                resolve_string_id(var.name).expect("variable name"),
            )?;
            self.int_bool_variable.borrow_mut().push(value);
        }
        Ok(())
    }

    fn store_int_bool_value(&self, int_or_bool: IntOrBool, id: InstructionId, value: IntValue<'c>) {
        match int_or_bool {
            IntOrBool::Int => {
                self.store_int_value(id, value);
            }
            IntOrBool::Bool => {
                self.store_bool_value(id, value);
            }
        }
    }

    fn store_int_value(&self, id: InstructionId, value: IntValue<'c>) {
        self.int_values.borrow_mut()[id.as_usize()] = Some(value);
    }

    fn store_bool_value(&self, id: InstructionId, value: IntValue<'c>) {
        self.bool_values.borrow_mut()[id.as_usize()] = Some(value);
    }

    fn get_int_value(&self, id: InstructionId) -> IntValue<'c> {
        self.int_values
            .borrow()
            .get(id.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("int value should be present")
    }

    fn get_bool_value(&self, id: InstructionId) -> IntValue<'c> {
        self.bool_values
            .borrow()
            .get(id.as_usize())
            .expect("vector should be initialized with the correct length")
            .expect("int value should be present")
    }

    fn generate(&self, llvm_module: &Module<'c>) -> Result<FunctionValue<'c>, CodeGenError> {
        let fn_type = self.make_fun_type();
        let fun = llvm_module.add_function(
            resolve_string_id(self.function.signature.name).expect("function name"),
            fn_type,
            None,
        );

        self.setup_fun_arg(fun)?;
        self.generate_body(fun)?;

        if !fun.verify(true) {
            panic!("LLVM says we have built an invalid function; this is a bug :-(");
        }
        Ok(fun)
    }

    fn generate_body(&self, fun: FunctionValue<'c>) -> Result<(), CodeGenError> {
        let bb = self.context.append_basic_block(fun, "entry");
        self.builder.position_at_end(bb);

        self.alloca_variables()?;

        for instruction in self.function.body.instructions.borrow().iter() {
            match &instruction.payload {
                InstructionPayload::Constant { constant, .. } => {
                    self.handle_constant(instruction.id, constant);
                }
                InstructionPayload::Unary {
                    result_type: operand_type,
                    operator,
                    operand,
                } => {
                    self.handle_unary(instruction.id, operand_type, operator, *operand)?;
                }
                InstructionPayload::Binary {
                    result_type,
                    operator,
                    operand_type,
                    left,
                    right,
                } => {
                    self.handle_binary(
                        instruction.id,
                        result_type,
                        operator,
                        operand_type,
                        *left,
                        *right,
                    )?;
                }
                InstructionPayload::Ret => {
                    self.builder.build_return(None)?;
                }
                InstructionPayload::RetExpr {
                    expression,
                    operand_type,
                } => {
                    self.handle_return_expression(*expression, operand_type)?;
                }
                InstructionPayload::Load {
                    operand_type,
                    symbol_kind,
                    ..
                } => {
                    self.handle_load(fun, instruction, operand_type, *symbol_kind)?;
                }
                InstructionPayload::Store {
                    operand_type,
                    symbol_kind,
                    value,
                    ..
                } => {
                    self.handle_store(fun, instruction, operand_type, *symbol_kind, *value)?;
                }
                InstructionPayload::Let {
                    variable_index,
                    operand_type,
                    initializer,
                    ..
                } => self.handle_let(*variable_index, operand_type, *initializer)?,
            }
        }
        Ok(())
    }

    fn handle_load(
        &self,
        fun: FunctionValue<'c>,
        instruction: &Instruction,
        operand_type: &Type,
        symbol_kind: SymbolKind,
    ) -> Result<(), CodeGenError> {
        match symbol_kind {
            SymbolKind::Function => todo!(),
            SymbolKind::Variable { index } => {
                let variable_index: usize = index.into();
                let var_pointer = *self
                    .int_bool_variable
                    .borrow()
                    .get(variable_index)
                    .expect("variable index should be valid");

                match operand_type {
                    Type::Int => {
                        self.int_values.borrow_mut()[instruction.id.as_usize()] = Some(
                            self.builder
                                .build_load(
                                    self.context.i64_type(),
                                    var_pointer,
                                    &Self::name("load", instruction.id),
                                )?
                                .into_int_value(),
                        );
                    }
                    Type::Boolean => {
                        self.bool_values.borrow_mut()[instruction.id.as_usize()] = Some(
                            self.builder
                                .build_load(
                                    self.context.bool_type(),
                                    var_pointer,
                                    &Self::name("load", instruction.id),
                                )?
                                .into_int_value(),
                        );
                    }
                    Type::Double => todo!(),
                }
            }
            SymbolKind::Argument { index } => {
                let value = fun
                    .get_nth_param(index.into())
                    .expect("valid argument number");
                match operand_type {
                    Type::Int => {
                        self.int_values.borrow_mut()[instruction.id.as_usize()] =
                            Some(value.into_int_value());
                    }
                    Type::Boolean => {
                        self.bool_values.borrow_mut()[instruction.id.as_usize()] =
                            Some(value.into_int_value());
                    }
                    Type::Double => {
                        todo!()
                    }
                }
            }
        }
        Ok(())
    }

    fn handle_store(
        &self,
        fun: FunctionValue<'c>,
        instruction: &Instruction,
        operand_type: &Type,
        symbol_kind: SymbolKind,
        value: InstructionId,
    ) -> Result<(), CodeGenError> {
        todo!()
    }

    fn handle_let(
        &self,
        variable_index: VariableIndex,
        operand_type: &Type,
        initializer: InstructionId,
    ) -> Result<(), CodeGenError> {
        let variable_index: usize = variable_index.into();
        let var_pointer = *self
            .int_bool_variable
            .borrow()
            .get(variable_index)
            .expect("variable index should be valid");

        let initializer = match operand_type {
            Type::Int => self
                .int_values
                .borrow()
                .get(initializer.as_usize())
                .expect("vector should be initialized with the correct length")
                .expect("let initializer should be an int"),
            Type::Boolean => self
                .bool_values
                .borrow()
                .get(initializer.as_usize())
                .expect("vector should be initialized with the correct length")
                .expect("let initializer should be a bool"),
            Type::Double => todo!(),
        };

        self.builder.build_store(var_pointer, initializer)?;
        Ok(())
    }

    fn make_fun_type(&self) -> FunctionType<'c> {
        let arguments = self
            .function
            .signature
            .arguments
            .iter()
            .map(|arg| match arg.argument_type {
                Type::Int => self.context.i64_type().into(),
                Type::Boolean => self.context.bool_type().into(),
                Type::Double => self.context.f64_type().into(),
            })
            .collect::<Vec<_>>();

        match &self.function.signature.return_type {
            None => self.context.void_type().fn_type(&arguments, false),
            Some(t) => match t {
                Type::Int => self.context.i64_type().fn_type(&arguments, false),
                Type::Boolean => self.context.bool_type().fn_type(&arguments, false),
                Type::Double => self.context.f64_type().fn_type(&arguments, false),
            },
        }
    }

    fn setup_fun_arg(&self, fun: FunctionValue<'c>) -> Result<(), CodeGenError> {
        for (i, arg) in self.function.signature.arguments.iter().enumerate() {
            let arg_value = fun.get_nth_param(i as u32).expect("should have argument");
            arg_value.set_name(resolve_string_id(arg.name).expect("function argument name"));
        }
        Ok(())
    }

    fn handle_binary(
        &self,
        id: InstructionId,
        result_type: &Type,
        operator: &BinaryOperator,
        operand_type: &Type,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        match operand_type {
            Type::Int => {
                self.handle_binary_int_operands(id, operator, result_type, left, right)?;
            }

            Type::Boolean => {
                self.handle_binary_boolean_operands(id, operator, result_type, left, right)?;
            }
            Type::Double => todo!(),
        }
        Ok(())
    }

    fn handle_binary_boolean_operands(
        &self,
        id: InstructionId,
        operator: &BinaryOperator,
        result_type: &Type,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        let left = self.get_bool_value(left);
        let right = self.get_bool_value(right);
        let result = match operator {
            BinaryOperator::Add
            | BinaryOperator::Sub
            | BinaryOperator::Mul
            | BinaryOperator::Div
            | BinaryOperator::Rem
            | BinaryOperator::Exp
            | BinaryOperator::Lt
            | BinaryOperator::Lte
            | BinaryOperator::Gt
            | BinaryOperator::Gte
            | BinaryOperator::BitwiseAnd
            | BinaryOperator::BitwiseOr
            | BinaryOperator::BitwiseXor
            | BinaryOperator::BitwiseShl
            | BinaryOperator::BitwiseShr => unreachable!(),

            BinaryOperator::Eq => self.builder.build_int_compare(
                IntPredicate::EQ,
                left,
                right,
                &Self::name("eq", id),
            )?,
            BinaryOperator::Neq => self.builder.build_int_compare(
                IntPredicate::NE,
                left,
                right,
                &Self::name("neq", id),
            )?,
            BinaryOperator::And => self
                .builder
                .build_and(left, right, &Self::name("and", id))?,
            BinaryOperator::Or => self.builder.build_or(left, right, &Self::name("or", id))?,
        };

        self.store_int_bool_value(IntOrBool::from_type(result_type), id, result);
        Ok(())
    }

    fn handle_binary_int_operands(
        &self,
        id: InstructionId,
        operator: &BinaryOperator,
        result_type: &Type,
        left: InstructionId,
        right: InstructionId,
    ) -> Result<(), CodeGenError> {
        let left = self.get_int_value(left);
        let right = self.get_int_value(right);
        let result = match operator {
            BinaryOperator::Add => {
                self.builder
                    .build_int_add(left, right, &Self::name("add", id))?
            }
            BinaryOperator::Sub => {
                self.builder
                    .build_int_sub(left, right, &Self::name("sub", id))?
            }
            BinaryOperator::Mul => {
                self.builder
                    .build_int_mul(left, right, &Self::name("mul", id))?
            }
            BinaryOperator::Div => {
                self.builder
                    .build_int_signed_div(left, right, &Self::name("div", id))?
            }
            BinaryOperator::Rem => {
                todo!()
            }
            BinaryOperator::Exp => {
                todo!()
            }
            BinaryOperator::Eq => self.builder.build_int_compare(
                IntPredicate::EQ,
                left,
                right,
                &Self::name("eq", id),
            )?,
            BinaryOperator::Neq => self.builder.build_int_compare(
                IntPredicate::NE,
                left,
                right,
                &Self::name("neq", id),
            )?,
            BinaryOperator::Lt => self.builder.build_int_compare(
                IntPredicate::SLT,
                left,
                right,
                &Self::name("lt", id),
            )?,
            BinaryOperator::Lte => self.builder.build_int_compare(
                IntPredicate::SLE,
                left,
                right,
                &Self::name("lte", id),
            )?,
            BinaryOperator::Gt => self.builder.build_int_compare(
                IntPredicate::SGT,
                left,
                right,
                &Self::name("gt", id),
            )?,
            BinaryOperator::Gte => self.builder.build_int_compare(
                IntPredicate::SGE,
                left,
                right,
                &Self::name("gte", id),
            )?,
            BinaryOperator::BitwiseAnd => {
                self.builder
                    .build_and(left, right, &Self::name("bitwise_and", id))?
            }
            BinaryOperator::BitwiseOr => {
                self.builder
                    .build_or(left, right, &Self::name("bitwise_or", id))?
            }
            BinaryOperator::BitwiseXor => {
                self.builder
                    .build_xor(left, right, &Self::name("bitwise_xor", id))?
            }
            BinaryOperator::BitwiseShl => {
                self.builder
                    .build_left_shift(left, right, &Self::name("bitwise_shl", id))?
            }
            BinaryOperator::BitwiseShr => self.builder.build_right_shift(
                left,
                right,
                false,
                &Self::name("bitwise_shr", id),
            )?,

            BinaryOperator::And | BinaryOperator::Or => {
                // TODO
                unreachable!()
            }
        };

        self.store_int_bool_value(IntOrBool::from_type(result_type), id, result);
        Ok(())
    }

    fn handle_unary(
        &self,
        id: InstructionId,
        operand_type: &Type,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        match operand_type {
            Type::Int => {
                self.handle_unary_int_operand(id, operator, operand)?;
            }
            Type::Boolean => {
                self.handle_unary_boolean_operand(id, operator, operand)?;
            }
            Type::Double => todo!(),
        }
        Ok(())
    }

    fn handle_unary_boolean_operand(
        &self,
        id: InstructionId,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        let operand = self.get_bool_value(operand);
        let result = match operator {
            UnaryOperator::Neg | UnaryOperator::BitwiseNot => {
                unreachable!()
            }
            UnaryOperator::Not => self.builder.build_not(operand, &Self::name("not", id))?,
        };

        self.store_bool_value(id, result);
        Ok(())
    }

    fn handle_unary_int_operand(
        &self,
        id: InstructionId,
        operator: &UnaryOperator,
        operand: InstructionId,
    ) -> Result<(), CodeGenError> {
        let operand = self.get_int_value(operand);
        let result = match operator {
            UnaryOperator::Neg => self
                .builder
                .build_int_neg(operand, &Self::name("neg", id))?,
            UnaryOperator::BitwiseNot => {
                // There's no LLVM instruction for bitwise not, but we can xor with
                // all 1s to get the same result (i.e. complement to 1)
                self.builder.build_xor(
                    self.context.i64_type().const_all_ones(),
                    operand,
                    &Self::name("bitwise_not", id),
                )?
            }
            UnaryOperator::Not => {
                // TODO: error
                unreachable!("unexpected not operator with int type")
            }
        };

        self.store_int_value(id, result);
        Ok(())
    }

    fn handle_constant(&self, id: InstructionId, constant: &LiteralValue) {
        match constant {
            LiteralValue::Integer(value) => {
                self.store_int_value(id, self.context.i64_type().const_int(*value as u64, false));
            }
            LiteralValue::Boolean(value) => {
                self.store_bool_value(
                    id,
                    self.context
                        .bool_type()
                        .const_int(if *value { 1 } else { 0 }, false),
                );
            }
            LiteralValue::Double(..) => todo!(),
        };
    }

    fn handle_return_expression(
        &self,
        expression: InstructionId,
        operand_type: &Type,
    ) -> Result<(), CodeGenError> {
        match operand_type {
            Type::Int => {
                let operand = self.get_int_value(expression);
                self.builder.build_return(Some(&operand))?;
            }
            Type::Boolean => {
                let operand = self.get_bool_value(expression);
                self.builder.build_return(Some(&operand))?;
            }
            Type::Double => todo!(),
        }
        Ok(())
    }

    fn name(prefix: &str, id: InstructionId) -> String {
        format!("{}_{}", prefix, id)
    }
}

struct LlvmGenerator<'c, 'ir, 'ir2>
where
    'c: 'ir,
{
    context: &'c Context,
    llvm_module: Module<'c>,
    builder: Builder<'c>,
    ir_module: &'ir codegen::Module<'ir2>,
}

impl<'c, 'm, 'm2> LlvmGenerator<'c, 'm, 'm2> {
    fn new(context: &'c Context, ir_module: &'m codegen::Module<'m2>) -> Self {
        let llvm_module =
            context.create_module(resolve_string_id(ir_module.name).expect("module name"));
        let builder = context.create_builder();
        Self {
            context,
            llvm_module,
            builder,
            ir_module,
        }
    }

    fn generate(&self) -> Result<String, CodeGenError> {
        for function in self.ir_module.functions.iter() {
            let fun_generator = LlvmFunctionGenerator::new(self.context, &self.builder, function);
            fun_generator.generate(&self.llvm_module)?;
        }
        Ok(self.llvm_module.to_string())
    }
}

#[allow(unused)]
fn ir_to_llvm(context: &Context, module: &codegen::Module) -> Result<String, CodeGenError> {
    let mut builder = LlvmGenerator::new(context, module);
    builder.generate()
}

#[cfg(test)]
mod tests {
    use super::*;
    use codegen::IrAllocator;
    use codegen::build_ir_module;
    use inkwell::context::Context;
    use semantic_analysis::{SemanticAnalyzer, TypedModule};
    use std::io::{Write, stderr};

    // TODO: this needs to not be so duplicated across projects
    fn make_analyzed_ast<'s>(
        semantic_analyzer: &'s SemanticAnalyzer,
        source: &str,
    ) -> &'s TypedModule<'s> {
        let ast_allocator = parser::AstAllocator::default();
        let module = parser::parse(&ast_allocator, "test", source);

        let result = semantic_analyzer.analyze_module(module);
        result.expect("should have passed semantic analysis")
    }

    fn handle_module<'i>(ir_allocator: &'i IrAllocator, source: &str) -> &'i codegen::Module<'i> {
        let semantic_analyzer = SemanticAnalyzer::default();
        let module = make_analyzed_ast(&semantic_analyzer, source);
        let module = build_ir_module(ir_allocator, module);

        eprintln!("Module IR:\n{}", module);
        stderr().flush().unwrap();

        module
    }

    #[test]
    fn test_ir_to_llvm() {
        let ir_allocator = IrAllocator::new();
        let basic_block = handle_module(
            &ir_allocator,
            r"
fn empty() {
}

fn add_one(x: int) -> int {
  return 1 + x;
}

fn add(x: int, y: int) -> int {
  return x + y;
}

fn greater(x: int, y: int) -> boolean {
  return x > y;
}

fn declare_var() {
    let x = 1;
    let y = true;
}

fn use_var() -> boolean {
    let x = false;
    let y = true;
    return y && !x;
}
",
        );

        let context = Context::create();
        let llvm_ir = ir_to_llvm(&context, basic_block).unwrap();

        println!("Generated LLVM IR:\n{}", llvm_ir);

        insta::assert_snapshot!(llvm_ir, @r#"
        ; ModuleID = 'test'
        source_filename = "test"

        define void @empty() {
        entry:
          ret void
        }

        define i64 @add_one(i64 %x) {
        entry:
          %add_2 = add i64 1, %x
          ret i64 %add_2
        }

        define i64 @add(i64 %x, i64 %y) {
        entry:
          %add_2 = add i64 %x, %y
          ret i64 %add_2
        }

        define i1 @greater(i64 %x, i64 %y) {
        entry:
          %gt_2 = icmp sgt i64 %x, %y
          ret i1 %gt_2
        }

        define void @declare_var() {
        entry:
          %x = alloca i64, align 8
          %y = alloca i1, align 1
          store i64 1, ptr %x, align 4
          store i1 true, ptr %y, align 1
          ret void
        }

        define i1 @use_var() {
        entry:
          %x = alloca i1, align 1
          %y = alloca i1, align 1
          store i1 false, ptr %x, align 1
          store i1 true, ptr %y, align 1
          %load_4 = load i1, ptr %y, align 1
          %load_5 = load i1, ptr %x, align 1
          %not_6 = xor i1 %load_5, true
          %and_7 = and i1 %load_4, %not_6
          ret i1 %and_7
        }
        "#);
    }
}
