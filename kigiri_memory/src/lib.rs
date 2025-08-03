mod symbols;

pub use symbols::StringId;
pub use symbols::intern_string;
pub use symbols::resolve_string_id;

// Re-export with a slight rename

pub use bumpalo::Bump as BumpArena;
pub use bumpalo::collections::Vec as BumpVec;
