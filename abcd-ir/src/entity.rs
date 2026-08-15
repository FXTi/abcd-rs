//! Typed index types for arena-based IR storage.
//!
//! All IR nodes are stored in `Vec` arenas and referenced by lightweight
//! copy-able indices.  This avoids lifetimes and raw pointers while keeping
//! the graph easy to traverse.

use std::fmt;

macro_rules! define_entity {
    ($(#[$meta:meta])* $name:ident, $prefix:expr) => {
        $(#[$meta])*
        #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);

        impl $name {
            pub const INVALID: Self = Self(u32::MAX);

            #[inline]
            pub fn index(self) -> usize {
                self.0 as usize
            }

            #[inline]
            pub fn from_index(i: usize) -> Self {
                Self(i as u32)
            }

            #[inline]
            pub fn is_valid(self) -> bool {
                self != Self::INVALID
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                if *self == Self::INVALID {
                    write!(f, "{}(INVALID)", stringify!($name))
                } else {
                    write!(f, "{}({})", stringify!($name), self.0)
                }
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "%{}_{}", $prefix, self.0)
            }
        }
    };
}

define_entity!(
    /// SSA value reference.
    Value, "v"
);
define_entity!(
    /// Basic block reference.
    Block, "bb"
);
define_entity!(
    /// Instruction reference.  Instructions that produce a result
    /// are also usable as [`Value`]s.
    Inst, "i"
);
define_entity!(
    /// Function reference within a [`Module`](crate::Module).
    FuncId, "fn"
);
define_entity!(
    /// Interned string reference into [`StringPool`](crate::StringPool).
    StringId, "s"
);
define_entity!(
    /// Class reference within a [`Module`](crate::Module).
    ClassId, "cls"
);
