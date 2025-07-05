use codegen::{IrAllocator, build_ir_module};
use inkwell::OptimizationLevel;
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use semantic_analysis::SemanticAnalyzer;

fn jit_test(source: &str, test_callback: unsafe fn(ExecutionEngine) -> ()) {
    let ast_allocator = parser::ParsedAstAllocator::default();
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
    let source = "fn f(x: int) -> int { return 1 + x * 2; }";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64) -> i64;
        let fun: JitFunction<F> = jit_engine.get_function("f").unwrap();

        assert_eq!(fun.call(0), 1);
        assert_eq!(fun.call(1), 3);
    })
}

#[test]
fn test_int_comparison() {
    let source = "fn f(x: int, y: int, z: int) -> boolean { return x < y || x < z; }";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64, i64, i64) -> bool;
        let fun: JitFunction<F> = jit_engine.get_function("f").unwrap();

        assert!(fun.call(0, 1, 2));
        assert!(fun.call(0, 0, 1));
        assert!(!fun.call(0, 0, 0));
    })
}

#[test]
fn test_variables() {
    let source = r"
fn f(x: int) -> boolean {
    let y = x * x;
    let z = x + 1;
    return y < z;
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64) -> bool;
        let fun: JitFunction<F> = jit_engine.get_function("f").unwrap();

        assert!(fun.call(0));
        assert!(fun.call(1));
        assert!(!fun.call(2));
    })
}

#[test]
fn test_variable_shadowing() {
    let source = r"
fn f(x: int) -> int {
    let x = x + 1;
    let x = x * 2;
    return x + 1;
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64) -> i64;
        let fun: JitFunction<F> = jit_engine.get_function("f").unwrap();

        assert_eq!(fun.call(0), 3);
        assert_eq!(fun.call(-1), 1);
        assert_eq!(fun.call(1), 5);
    })
}
