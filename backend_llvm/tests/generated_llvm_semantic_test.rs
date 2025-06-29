use codegen::{build_ir_module, IrAllocator};
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use inkwell::OptimizationLevel;
use semantic_analysis::SemanticAnalyzer;

fn jit_test(source: &str, test_callback: unsafe fn(ExecutionEngine) -> ()) {
    let ast_allocator = parser::AstAllocator::default();
    let parsed_module = parser::parse(&ast_allocator, "test", source);

    let semantic_analyzer = SemanticAnalyzer::default();
    let typed_module = semantic_analyzer.analyze_module(parsed_module).unwrap();

    let ir_allocator = IrAllocator::new();
    let module = build_ir_module(&ir_allocator, typed_module);

    let context = Context::create();
    let module = backend_llvm::ir_to_llvm(&context, module).unwrap();

    println!(
        "Generated LLVM IR:\n{}",
        module.print_to_string().to_string()
    );

    let jit_engine = module
        .create_jit_execution_engine(OptimizationLevel::None)
        .unwrap();

    unsafe {
        test_callback(jit_engine);
    }
}

#[test]
fn test_basic_arithmetic() {
    let source = "fn add_one(x: int) -> int { return x + 1; }";
    jit_test(source, |jit_engine| unsafe {
        type AddOne = unsafe extern "C" fn(i64) -> i64;
        let fun: JitFunction<AddOne> = jit_engine.get_function("add_one").unwrap();

        assert_eq!(fun.call(0), 1);
        assert_eq!(fun.call(1), 2);
        assert_eq!(fun.call(i64::MAX), i64::MIN); // Wraps around
    })
}
