//! Typed constant pool (replaces v0.1 `LiteralArrayIdx` /
//! `literal_array_offsets` — a literal-array *index* is a container shape;
//! a [`Const`] is the semantic value).
//!
//! The pool is append-only (T1): pushing a constant never changes an
//! existing [`ConstId`]. Array/object literal shapes are semantic
//! [`Const`] trees, not file literal-array blobs.

use crate::id::{ConstId, FuncId, Sym};

/// A typed constant value.
#[derive(Clone, Debug, PartialEq)]
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
    /// A string literal (its identity is a symbol).
    String(Sym),
    /// A BigInt literal (decimal repr as a symbol). Never collapsible
    /// into [`Const::String`] — the runtime builds a BigInt, not a
    /// string.
    BigInt(Sym),
    /// An array literal shape (`createarraywithbuffer`): the elements.
    ArrayLiteral(Vec<Const>),
    /// An object literal shape (`createobjectwithbuffer`): parallel key
    /// and value lists; `keys[i]` names `values[i]`.
    ObjectLiteral {
        /// Property keys (typically [`Const::String`]).
        keys: Vec<Const>,
        /// Property values.
        values: Vec<Const>,
    },
    /// A reference to a function in the module's function table — used by
    /// class member buffers (`defineclasswithbuffer`) whose literal arrays
    /// carry methods.
    MethodRef(FuncId),
}

impl Const {
    /// Build a [`Const::Number`] from an `f64` (bits preserved).
    pub fn number(v: f64) -> Self {
        Self::Number(v.to_bits())
    }

    /// Interpret a [`Const::Number`] payload as `f64`; `None` for other
    /// variants.
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Const::Number(bits) => Some(f64::from_bits(*bits)),
            _ => None,
        }
    }
}

/// Append-only pool of typed constants (T1).
#[derive(Clone, Debug, Default)]
pub struct ConstPool {
    consts: Vec<Const>,
}

impl ConstPool {
    /// An empty pool.
    pub fn new() -> Self {
        Self::default()
    }

    /// Append a constant, returning its [`ConstId`]. Ids are stable: a
    /// push never renumbers earlier entries. (Dedup is a lift-layer
    /// policy, not a pool invariant.)
    pub fn push(&mut self, c: Const) -> ConstId {
        let id = ConstId(self.consts.len() as u32);
        self.consts.push(c);
        id
    }

    /// Look up a constant by id; `None` for an id the pool never issued
    /// (library rule: no panics on data).
    pub fn get(&self, id: ConstId) -> Option<&Const> {
        self.consts.get(id.index())
    }

    /// Number of constants in the pool.
    pub fn len(&self) -> usize {
        self.consts.len()
    }

    /// Whether the pool is empty.
    pub fn is_empty(&self) -> bool {
        self.consts.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn const_pool_round_trip() {
        let mut pool = ConstPool::new();
        let sym = Sym::new(0);
        let values = [
            Const::Undefined,
            Const::Hole,
            Const::Null,
            Const::Bool(true),
            Const::number(-0.0),
            Const::number(f64::NAN),
            Const::String(sym),
            Const::BigInt(sym),
            Const::ArrayLiteral(vec![
                Const::number(1.0),
                Const::ArrayLiteral(vec![Const::Null]),
            ]),
            Const::ObjectLiteral {
                keys: vec![Const::String(sym), Const::number(2.0)],
                values: vec![Const::Bool(false), Const::MethodRef(FuncId::new(3))],
            },
            Const::MethodRef(FuncId::new(7)),
        ];
        let ids: Vec<ConstId> = values.iter().cloned().map(|c| pool.push(c)).collect();
        // Round-trip: every id reads back exactly what was pushed.
        for (id, want) in ids.iter().zip(values.iter()) {
            assert_eq!(pool.get(*id), Some(want));
        }
        // Append-only: pushing more does not disturb earlier entries.
        pool.push(Const::Null);
        assert_eq!(pool.get(ids[0]), Some(&Const::Undefined));
        // Bit-exactness of the number payloads.
        assert_eq!(pool.get(ids[4]).and_then(Const::as_f64), Some(-0.0));
        assert!(pool.get(ids[5]).and_then(Const::as_f64).unwrap().is_nan());
        // Out-of-range ids are data, not panics.
        assert_eq!(pool.get(ConstId::new(999)), None);
    }
}
