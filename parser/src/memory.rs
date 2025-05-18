use std::sync::{LazyLock, Mutex};

pub type StringInterner = string_interner::DefaultStringInterner;
pub type StringId = string_interner::DefaultSymbol;

pub static STRING_INTERNER: LazyLock<Mutex<StringInterner>> =
    LazyLock::new(|| Mutex::new(StringInterner::new()));
