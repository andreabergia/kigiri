use std::sync::{LazyLock, Mutex};

pub type StringInterner = string_interner::DefaultStringInterner;
pub type StringId = string_interner::DefaultSymbol;

static STRING_INTERNER: LazyLock<Mutex<StringInterner>> =
    LazyLock::new(|| Mutex::new(StringInterner::new()));

pub fn resolve_string_id(string_id: StringId) -> Option<&'static str> {
    let interner = STRING_INTERNER
        .lock()
        .expect("should be able to acquire mutex on the string interner");
    interner.resolve(string_id).map(|s|
        // SAFETY: the string interner is never deallocated and guarantees the strings
        // are always alive and valid
        unsafe {
            std::mem::transmute(s)
        })
}

pub fn intern_string(string: &str) -> StringId {
    let mut interner = STRING_INTERNER
        .lock()
        .expect("should be able to lock the interner");
    interner.get_or_intern(string)
}
