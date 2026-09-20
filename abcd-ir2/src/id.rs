//! Typed arena indices (T1: stable value identity).
//!
//! Every cross-reference in the IR is one of these newtype `u32` indices
//! into a [`crate::module::Module`] arena. Ids are allocated append-only
//! and never renumbered: passes clone arenas, so an id keeps its meaning
//! across a whole pass pipeline. There are no file offsets anywhere in
//! this crate — an id is never an encoding position.

use std::fmt;

macro_rules! define_id {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);

        impl $name {
            /// Wrap a raw arena index.
            pub const fn new(index: u32) -> Self {
                Self(index)
            }

            /// The raw arena index.
            pub const fn index(self) -> usize {
                self.0 as usize
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!(stringify!($name), "({})"), self.0)
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(self, f)
            }
        }
    };
}

define_id!(
    /// Symbol identity: an interned name in [`crate::symbol::SymbolTable`]
    /// (T9 — every name in the IR is a `Sym`, never a raw string or a file
    /// string-pool index).
    Sym
);
define_id!(
    /// Index into [`crate::consts::ConstPool`].
    ConstId
);
define_id!(
    /// Index into [`crate::module::Module::classes`] — the module's own
    /// class table, never a file pool (N46 by construction).
    ClassId
);
define_id!(
    /// Index into [`crate::module::ClassData::fields`] of the owning class.
    FieldId
);
define_id!(
    /// Index into [`crate::module::Module::functions`].
    FuncId
);
define_id!(
    /// Index into [`crate::module::Module::blocks`].
    BlockId
);
define_id!(
    /// Index into [`crate::module::Module::insts`].
    InstId
);
define_id!(
    /// Index into [`crate::module::Module::values`] — the SSA value
    /// identity; the taint-analysis key (T1).
    ValueId
);
