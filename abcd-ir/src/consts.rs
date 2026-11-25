//! Typed constant pool (`design/ir.md`): literal-array table indices and
//! container offsets stay in the file layer; the IR stores semantic
//! [`Const`] values and [`ConstId`]-linked literal shapes.
//!
//! The pool is append-only (T1): pushing or interning a constant never changes
//! an existing [`ConstId`]. Array/object literal shapes reference child
//! constants via [`ConstId`], keeping [`Const`] flat and non-recursive.

use std::collections::HashMap;

use crate::id::{ConstId, FuncId, Sym};

/// A typed constant value.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Const {
    /// `undefined`.
    Undefined,
    /// The TDZ hole (sentinel for uninitialized lexical bindings).
    Hole,
    /// `null`.
    Null,
    /// A boolean literal.
    Bool(bool),
    /// A number literal, stored as raw `f64` bits so `NaN` payloads and
    /// `-0.0` round-trip exactly.
    Number(u64),
    /// A signed 64-bit integer literal (`StaticTy::I64`, `#36`).
    Int64(i64),
    /// An unsigned 64-bit integer literal (`StaticTy::U64`, `#36`).
    UInt64(u64),
    /// A string literal (its identity is a symbol).
    String(Sym),
    /// A BigInt literal (decimal repr as a symbol). Never collapsible
    /// into [`Const::String`] — the runtime builds a BigInt, not a
    /// string.
    BigInt(Sym),
    /// An array literal shape (`createarraywithbuffer`): element [`ConstId`]s
    /// in [`ConstPool`].
    ArrayLiteral(Vec<ConstId>),
    /// An object literal shape (`createobjectwithbuffer`): parallel key
    /// and value [`ConstId`] lists; `keys[i]` names `values[i]`.
    ObjectLiteral {
        /// Property keys (typically [`Const::String`]).
        keys: Vec<ConstId>,
        /// Property values.
        values: Vec<ConstId>,
    },
    /// A reference to a function in the module's function table — used by
    /// class member buffers (`defineclasswithbuffer`) whose literal arrays
    /// carry methods.
    MethodRef(FuncId),
}

impl Const {
    /// Build a [`Const::Number`] from an `f64` (bits preserved).
    #[must_use]
    pub fn number(v: f64) -> Self {
        Self::Number(v.to_bits())
    }

    /// Interpret a [`Const::Number`] payload as `f64`; `None` for other
    /// variants.
    #[must_use]
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Const::Number(bits) => Some(f64::from_bits(*bits)),
            _ => None,
        }
    }

    /// Interpret a [`Const::Int64`] payload as `i64`; `None` for other
    /// variants.
    #[must_use]
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Const::Int64(v) => Some(*v),
            _ => None,
        }
    }

    /// Interpret a [`Const::UInt64`] payload as `u64`; `None` for other
    /// variants.
    #[must_use]
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Const::UInt64(v) => Some(*v),
            _ => None,
        }
    }
}

/// Append-only pool of typed constants (T1) supporting both unguarded [`Self::push`]
/// and deduplicating [`Self::intern`].
#[derive(Clone, Debug, Default)]
pub struct ConstPool {
    consts: Vec<Const>,
    index: HashMap<Const, ConstId>,
}

impl PartialEq for ConstPool {
    fn eq(&self, other: &Self) -> bool {
        self.consts == other.consts
    }
}

impl Eq for ConstPool {}

impl ConstPool {
    /// An empty pool.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Append a constant unconditionally, returning its [`ConstId`]. Ids are
    /// stable: a push never renumbers earlier entries.
    pub fn push(&mut self, c: Const) -> ConstId {
        let raw = u32::try_from(self.consts.len()).expect("ConstPool exceeded u32::MAX entries");
        let id = ConstId(raw);
        self.index.entry(c.clone()).or_insert(id);
        self.consts.push(c);
        id
    }

    /// Deduplicating append: returns the existing [`ConstId`] if an identical
    /// [`Const`] was already interned or pushed, otherwise appends it.
    pub fn intern(&mut self, c: Const) -> ConstId {
        if let Some(&id) = self.index.get(&c) {
            return id;
        }
        let raw = u32::try_from(self.consts.len()).expect("ConstPool exceeded u32::MAX entries");
        let id = ConstId(raw);
        self.index.insert(c.clone(), id);
        self.consts.push(c);
        id
    }

    /// Convenience helper appending a [`Const::ArrayLiteral`].
    pub fn push_array(&mut self, items: Vec<ConstId>) -> ConstId {
        self.push(Const::ArrayLiteral(items))
    }

    /// Convenience helper appending a [`Const::ObjectLiteral`].
    pub fn push_object(&mut self, keys: Vec<ConstId>, values: Vec<ConstId>) -> ConstId {
        self.push(Const::ObjectLiteral { keys, values })
    }

    /// Look up a constant by id; `None` for an id the pool never issued
    /// (library rule: no panics on data).
    #[must_use]
    pub fn get(&self, id: ConstId) -> Option<&Const> {
        self.consts.get(id.index())
    }

    /// Number of constants in the pool.
    #[must_use]
    pub fn len(&self) -> usize {
        self.consts.len()
    }

    /// Whether the pool is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.consts.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn const_pool_round_trip_and_intern() {
        let mut pool = ConstPool::new();
        let sym = Sym::new(0);
        let c_one = pool.intern(Const::number(1.0));
        let c_null = pool.intern(Const::Null);
        let c_nested_arr = pool.push_array(vec![c_null]);
        let c_str = pool.intern(Const::String(sym));
        let c_two = pool.intern(Const::number(2.0));
        let c_false = pool.intern(Const::Bool(false));
        let c_mref = pool.intern(Const::MethodRef(FuncId::new(3)));

        let values = [
            Const::Undefined,
            Const::Hole,
            Const::Null,
            Const::Bool(true),
            Const::number(-0.0),
            Const::number(f64::NAN),
            Const::Int64(-42),
            Const::UInt64(u64::MAX),
            Const::String(sym),
            Const::BigInt(sym),
            Const::ArrayLiteral(vec![c_one, c_nested_arr]),
            Const::ObjectLiteral {
                keys: vec![c_str, c_two],
                values: vec![c_false, c_mref],
            },
            Const::MethodRef(FuncId::new(7)),
        ];
        let ids: Vec<ConstId> = values.iter().cloned().map(|c| pool.push(c)).collect();
        for (id, want) in ids.iter().zip(values.iter()) {
            assert_eq!(pool.get(*id), Some(want));
        }
        assert_eq!(pool.intern(Const::Null), c_null);
        assert_eq!(pool.get(ids[4]).and_then(Const::as_f64), Some(-0.0));
        assert!(pool.get(ids[5]).and_then(Const::as_f64).unwrap().is_nan());
        assert_eq!(pool.get(ids[6]).and_then(Const::as_i64), Some(-42));
        assert_eq!(pool.get(ids[7]).and_then(Const::as_u64), Some(u64::MAX));
        assert_eq!(pool.get(ConstId::new(999)), None);
    }
}
