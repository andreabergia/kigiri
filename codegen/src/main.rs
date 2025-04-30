#![allow(unused)]

mod ir;
mod ir_builder;

use inkwell::context::Context;

fn main() {
    let context = Context::create();
    let builder = context.create_builder();

    let module = context.create_module("test");
    let fn_type = context.i64_type().fn_type(&[], false);
    let fun = module.add_function("foo", fn_type, None);

    let bb = context.append_basic_block(fun, "entry");

    builder.position_at_end(bb);
    let ival = builder
        .build_int_add(
            context.i64_type().const_int(1, false),
            context.i64_type().const_int(2, false),
            "add0",
        )
        .unwrap();
    builder.build_return(Some(&ival)).unwrap();

    if !fun.verify(true) {
        panic!("Invalid function");
    }

    fun.print_to_stderr();
}
