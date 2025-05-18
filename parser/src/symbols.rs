use std::sync::{LazyLock, Mutex};

pub type StringInterner = string_interner::DefaultStringInterner;
pub type StringId = string_interner::DefaultSymbol;

static STRING_INTERNER: LazyLock<Mutex<StringInterner>> =
    LazyLock::new(|| Mutex::new(StringInterner::new()));

pub fn resolve_symbol(symbol_id: StringId) -> Option<&'static str> {
    let interner = STRING_INTERNER
        .lock()
        .expect("should be able to acquire mutex on the string interner");
    interner.resolve(symbol_id).map(|s|
        // SAFETY: the string interner is never deallocated and guarantees the strings
        // are always alive and valid
        unsafe {
            std::mem::transmute(s)
        })
}

pub fn get_or_create_symbol(symbol: &str) -> StringId {
    let mut interner = STRING_INTERNER
        .lock()
        .expect("should be able to lock the interner");
    interner.get_or_intern(symbol)
}
