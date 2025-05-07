use codegen::{InstructionType, LiteralValue};
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::values::IntValue;
use std::collections::HashMap;

fn ir_to_llvm<'c>(context: &'c Context, module: &Module<'c>, ir: &codegen::BasicBlock) {
    let builder = context.create_builder();

    let fn_type = context.void_type().fn_type(&[], false);
    let fun = module.add_function("test", fn_type, None);

    let bb = context.append_basic_block(fun, "entry");

    builder.position_at_end(bb);

    let mut int_values: HashMap<&str, IntValue> = HashMap::new();

    for instruction in ir.instructions.borrow().iter() {
        match instruction.instruction_type {
            InstructionType::Const => {
                let constant = instruction
                    .constant
                    .clone()
                    .expect("a const instruction should have a value");
                match constant {
                    LiteralValue::Integer(value) => {
                        int_values.insert(
                            instruction.name,
                            context.i64_type().const_int(value as u64, false),
                        );
                    }
                    LiteralValue::Double(value) => todo!(),
                    LiteralValue::Boolean(_) => todo!(),
                };
            }

            InstructionType::Add => {
                let lhs = int_values.get(instruction.args[0].name).unwrap();
                let rhs = int_values.get(instruction.args[1].name).unwrap();
                let result = builder.build_int_add(*lhs, *rhs, "add0").unwrap();
                int_values.insert(instruction.name, result);
            }

            _ => todo!(), // InstructionType::Ret => {}
                          // InstructionType::Not => {}
                          // InstructionType::Neg => {}
                          // InstructionType::BitwiseNot => {}
                          // InstructionType::Add => {}
                          // InstructionType::Sub => {}
                          // InstructionType::Mul => {}
                          // InstructionType::Div => {}
                          // InstructionType::Rem => {}
                          // InstructionType::Exp => {}
                          // InstructionType::Eq => {}
                          // InstructionType::Neq => {}
                          // InstructionType::Lt => {}
                          // InstructionType::Lte => {}
                          // InstructionType::Gt => {}
                          // InstructionType::Gte => {}
                          // InstructionType::And => {}
                          // InstructionType::Or => {}
                          // InstructionType::BitwiseAnd => {}
                          // InstructionType::BitwiseOr => {}
                          // InstructionType::BitwiseXor => {}
                          // InstructionType::BitwiseShl => {}
                          // InstructionType::BitwiseShr => {}
        }
    }

    builder.build_return(None);
    if !fun.verify(true) {
        panic!("Invalid function");
    }

    fun.print_to_stderr();
}

#[cfg(test)]
mod tests {
    use super::*;
    use codegen::Ir;
    use codegen::{build_ir, BasicBlock};
    use inkwell::context::Context;
    use std::io::{stderr, Write};
    use type_engine::{TypeEngine, TypedExpression};

    // TODO: this needs to not be so duplicated across projects
    fn make_analyzed_ast<'te>(
        type_engine: &'te TypeEngine,
        source: &str,
    ) -> &'te TypedExpression<'te> {
        let ast = parser::Ast::for_tests();
        let expression = parser::parse(&ast, source);

        let result = type_engine.check_and_infer_types(expression);
        result.expect("should have passed semantic analysis")
    }

    fn basic_block_from_source<'ir>(ir: &'ir Ir, source: &str) -> &'ir BasicBlock<'ir> {
        let type_engine = TypeEngine::default();
        let expression = make_analyzed_ast(&type_engine, source);
        let bb = build_ir(ir, expression);

        let bb_ir = bb
            .instructions
            .borrow()
            .iter()
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join("\n");
        eprintln!("BasicBlock IR:\n{}", bb_ir);
        stderr().flush().unwrap();

        bb
    }

    #[test]
    fn test_ir_to_llvm() {
        let ir = Ir::new();
        let basic_block = basic_block_from_source(&ir, "1 + 2");

        let context = Context::create();
        let module = context.create_module("test");
        ir_to_llvm(&context, &module, basic_block);
    }
}
