use codegen::{IrAllocator, build_ir_module};
use inkwell::OptimizationLevel;
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use semantic_analysis::SemanticAnalyzer;

fn jit_test(source: &str, test_callback: unsafe fn(ExecutionEngine) -> ()) {
    let ast_allocator = parser::ParsedAstAllocator::default();
    let parsed_module =
        parser::parse(&ast_allocator, "test", source).expect("parse should succeed");

    let semantic_analyzer = SemanticAnalyzer::default();
    let typed_module = semantic_analyzer
        .analyze_module(parsed_module)
        .expect("semantic analysis");

    let ir_allocator = IrAllocator::new();
    let module = build_ir_module(&ir_allocator, typed_module).expect("codegen should succeed");

    let context = Context::create();
    let module = backend_llvm::ir_to_llvm(&context, module).expect("llvm ir generation");

    println!(
        "Generated LLVM IR:\n{}",
        module.print_to_string().to_string()
    );

    let jit_engine = module
        .create_jit_execution_engine(OptimizationLevel::None)
        .expect("jit engine creation");

    unsafe {
        test_callback(jit_engine);
    }
}

#[test]
fn test_basic_arithmetic() {
    let source = "fn f(x: int) -> int { return 1 + x * 2; }";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64) -> i64;
        let fun: JitFunction<F> = jit_engine.get_function("f").expect("find function");

        assert_eq!(fun.call(0), 1);
        assert_eq!(fun.call(1), 3);
    })
}

#[test]
fn test_int_comparison() {
    let source = "fn f(x: int, y: int, z: int) -> bool { return x < y || x < z; }";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64, i64, i64) -> bool;
        let fun: JitFunction<F> = jit_engine.get_function("f").expect("find function");

        assert!(fun.call(0, 1, 2));
        assert!(fun.call(0, 0, 1));
        assert!(!fun.call(0, 0, 0));
    })
}

#[test]
fn test_variables() {
    let source = r"
fn f(x: int) -> bool {
    let y = x * x;
    let z = x + 1;
    return y < z;
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64) -> bool;
        let fun: JitFunction<F> = jit_engine.get_function("f").expect("find function");

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
        let fun: JitFunction<F> = jit_engine.get_function("f").expect("find function");

        assert_eq!(fun.call(0), 3);
        assert_eq!(fun.call(-1), 1);
        assert_eq!(fun.call(1), 5);
    })
}

#[test]
fn test_functions_call() {
    let source = r"
fn add_one(x: int) -> int { return x + 1; }

fn f(x: int) -> int {
    return 2 * add_one(x);
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64) -> i64;
        let fun: JitFunction<F> = jit_engine.get_function("f").expect("find function");

        assert_eq!(fun.call(0), 2);
        assert_eq!(fun.call(1), 4);
        assert_eq!(fun.call(2), 6);
    })
}

#[test]
fn test_if_statement_simple() {
    let source = r"
fn test(x: bool) -> int {
    if x {
        return 1;
    }
    return 0;
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(bool) -> i64;
        let fun: JitFunction<F> = jit_engine.get_function("test").expect("find function");

        assert_eq!(fun.call(true), 1);
        assert_eq!(fun.call(false), 0);
    })
}

#[test]
fn test_if_statement_with_else() {
    let source = r"
fn test(x: bool) -> int {
    if x {
        return 1;
    } else {
        return 0;
    }
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(bool) -> i64;
        let fun: JitFunction<F> = jit_engine.get_function("test").expect("find function");

        assert_eq!(fun.call(true), 1);
        assert_eq!(fun.call(false), 0);
    })
}

#[test]
fn test_if_elseif_else() {
    let source = r"
fn test(x: int) -> int {
    if x > 0 {
        return 1;
    } else if x < 0 {
        return -1;
    } else {
        return 0;
    }
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64) -> i64;
        let fun: JitFunction<F> = jit_engine.get_function("test").expect("find function");

        assert_eq!(fun.call(5), 1);
        assert_eq!(fun.call(-3), -1);
        assert_eq!(fun.call(0), 0);
    })
}

#[test]
fn test_if_statement_variable_assignment() {
    let source = r"
fn test(condition: bool) -> int {
    let result = 0;
    if condition {
        result = 42;
    }
    return result;
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(bool) -> i64;
        let fun: JitFunction<F> = jit_engine.get_function("test").expect("find function");

        assert_eq!(fun.call(true), 42);
        assert_eq!(fun.call(false), 0);
    })
}

#[test]
fn test_nested_if_statements() {
    let source = r"
fn test(x: int, y: int) -> int {
    if x > 0 {
        if y > 0 {
            return 1;
        } else {
            return 2;
        }
    } else {
        return 3;
    }
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64, i64) -> i64;
        let fun: JitFunction<F> = jit_engine.get_function("test").expect("find function");

        assert_eq!(fun.call(1, 1), 1);
        assert_eq!(fun.call(1, -1), 2);
        assert_eq!(fun.call(-1, 1), 3);
        assert_eq!(fun.call(-1, -1), 3);
    })
}

#[test]
fn test_if_statement_variable_declaration_in_block() {
    let source = r"
fn test(condition: bool) -> int {
    let r = 1;
    if condition {
        let x = 2;
        return x + r;
    }
    return r;
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(bool) -> i64;
        let fun: JitFunction<F> = jit_engine.get_function("test").expect("find function");

        assert_eq!(fun.call(true), 3);
        assert_eq!(fun.call(false), 1);
    })
}

#[test]
fn test_factorial() {
    let source = r"
fn fact(n: int) -> int {
    if n <= 1 {
        return 1;
    }
    return n * fact(n - 1);
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64) -> i64;
        let fun: JitFunction<F> = jit_engine.get_function("fact").expect("find function");

        assert_eq!(fun.call(0), 1);
        assert_eq!(fun.call(1), 1);
        assert_eq!(fun.call(2), 2);
        assert_eq!(fun.call(3), 6);
        assert_eq!(fun.call(4), 24);
    })
}

#[test]
fn test_while_loop_simple() {
    let source = r"
fn count_down(n: int) -> int {
    let result = 0;
    let counter = n;
    while counter > 0 {
        result = result + counter;
        counter = counter - 1;
    }
    return result;
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64) -> i64;
        let fun: JitFunction<F> = jit_engine
            .get_function("count_down")
            .expect("find function");

        assert_eq!(fun.call(0), 0);
        assert_eq!(fun.call(1), 1);
        assert_eq!(fun.call(3), 6); // 3 + 2 + 1
        assert_eq!(fun.call(5), 15); // 5 + 4 + 3 + 2 + 1
    })
}

#[test]
fn test_while_loop_with_early_return() {
    let source = r"
fn find_first_multiple(start: int, target: int) -> int {
    let current = start;
    while current < 100 {
        if current % target == 0 {
            return current;
        }
        current = current + 1;
    }
    return -1;
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64, i64) -> i64;
        let fun: JitFunction<F> = jit_engine
            .get_function("find_first_multiple")
            .expect("find function");

        assert_eq!(fun.call(10, 5), 10); // 10 is multiple of 5
        assert_eq!(fun.call(11, 5), 15); // first multiple of 5 >= 11
        assert_eq!(fun.call(98, 3), 99); // first multiple of 3 >= 98
    })
}

#[test]
fn test_nested_while_loops() {
    let source = r"
fn multiply_by_addition(a: int, b: int) -> int {
    let result = 0;
    let i = 0;
    while i < a {
        let j = 0;
        while j < b {
            result = result + 1;
            j = j + 1;
        }
        i = i + 1;
    }
    return result;
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64, i64) -> i64;
        let fun: JitFunction<F> = jit_engine
            .get_function("multiply_by_addition")
            .expect("find function");

        assert_eq!(fun.call(0, 5), 0);
        assert_eq!(fun.call(3, 0), 0);
        assert_eq!(fun.call(3, 4), 12);
        assert_eq!(fun.call(2, 7), 14);
    })
}

#[test]
fn test_break_continue() {
    let source = r"
fn count_bits(a: int) -> int {
    let n = 0;
    let t = a;
    while true {
        if t == 0 {
            break;
        }
        if (t & 1) == 1 {
            n = n + 1;
        }
        t = t >> 1;
    }
    return n;
}";
    jit_test(source, |jit_engine| unsafe {
        type F = unsafe extern "C" fn(i64) -> i64;
        let fun: JitFunction<F> = jit_engine
            .get_function("count_bits")
            .expect("find function");

        assert_eq!(fun.call(0), 0);
        assert_eq!(fun.call(1), 1);
        assert_eq!(fun.call(2), 1);
        assert_eq!(fun.call(3), 2);
        assert_eq!(fun.call(4), 1);
        assert_eq!(fun.call(5), 2);
        assert_eq!(fun.call(7), 3);
    })
}
