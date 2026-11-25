//! Typed constant pool (`design/ir.md`, `#57` `R3-H9`): literal-array table
//! indices and container offsets stay in the file layer; the IR stores semantic
//! [`Const`] values and [`ConstId`]-linked literal shapes with lossless tag
//! fidelity.
//!
//! The pool is append-only (T1): pushing or interning a constant never changes
//! an existing [`ConstId`]. Array/object/typed-array literal shapes reference
//! child constants via [`ConstId`], keeping [`Const`] flat and non-recursive.

use std::collections::HashMap;

use crate::id::{ConstId, FuncId, Sym};

/// Method-literal tag kind carried by [`Const::MethodRef`] (`#57` `R3-H9`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum LitMethodKind {
    /// `LiteralTag::METHOD`.
    #[default]
    Method,
    /// `LiteralTag::GENERATORMETHOD`.
    GeneratorMethod,
    /// `LiteralTag::ASYNCGENERATORMETHOD`.
    AsyncGeneratorMethod,
    /// `LiteralTag::GETTER`.
    Getter,
    /// `LiteralTag::SETTER`.
    Setter,
}

/// Element tag of a homogeneous [`Const::TypedArrayLiteral`] (`LiteralTag::ARRAY_*`, `#57` `R3-H9`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TypedArrayTag {
    /// `LiteralTag::ARRAY_U1`.
    U1,
    /// `LiteralTag::ARRAY_U8`.
    U8,
    /// `LiteralTag::ARRAY_I8`.
    I8,
    /// `LiteralTag::ARRAY_U16`.
    U16,
    /// `LiteralTag::ARRAY_I16`.
    I16,
    /// `LiteralTag::ARRAY_U32`.
    U32,
    /// `LiteralTag::ARRAY_I32`.
    I32,
    /// `LiteralTag::ARRAY_U64`.
    U64,
    /// `LiteralTag::ARRAY_I64`.
    I64,
    /// `LiteralTag::ARRAY_F32`.
    F32,
    /// `LiteralTag::ARRAY_F64`.
    F64,
    /// `LiteralTag::ARRAY_STRING`.
    String,
}

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
    /// A 1-byte literal tag value (`LiteralTag::TAGVALUE` / `Integer8`).
    Int8(u8),
    /// A 32-bit integer literal (`LiteralTag::INTEGER`).
    Int32(u32),
    /// A 32-bit float literal (`LiteralTag::FLOAT`), stored as raw `f32` bits.
    Float32(u32),
    /// A number literal, stored as raw `f64` bits so `NaN` payloads and
    /// `-0.0` round-trip exactly (`LiteralTag::DOUBLE` / `fldai`).
    Number(u64),
    /// A signed 64-bit integer literal (`StaticTy::I64`, `#36`).
    Int64(i64),
    /// An unsigned 64-bit integer literal (`StaticTy::U64`, `#36`).
    UInt64(u64),
    /// `LiteralTag::ACCESSOR` byte payload.
    Accessor(u8),
    /// `LiteralTag::METHODAFFILIATE` `u16` payload.
    MethodAffiliate(u16),
    /// `LiteralTag::BUILTINTYPEINDEX` `u8` payload.
    BuiltinTypeIndex(u8),
    /// `LiteralTag::ETS_IMPLEMENTS` symbol payload.
    EtsImplements(Sym),
    /// `LiteralTag::NULLVALUE` `u8` payload (distinct from JS `Const::Null` tag).
    LitNull(u8),
    /// A string literal (its identity is a symbol).
    String(Sym),
    /// A BigInt literal (decimal repr as a symbol). Never collapsible
    /// into [`Const::String`] — the runtime builds a BigInt, not a
    /// string.
    BigInt(Sym),
    /// An array literal shape (`createarraywithbuffer`): element [`ConstId`]s
    /// in [`ConstPool`].
    ArrayLiteral(Vec<ConstId>),
    /// A homogeneous typed-array literal (`LiteralTag::ARRAY_*`).
    TypedArrayLiteral {
        /// Homogeneous element tag.
        tag: TypedArrayTag,
        /// Element [`ConstId`]s in [`ConstPool`].
        items: Vec<ConstId>,
    },
    /// An object literal shape (`createobjectwithbuffer`): parallel key
    /// and value [`ConstId`] lists; `keys[i]` names `values[i]`.
    ObjectLiteral {
        /// Property keys (typically [`Const::String`]).
        keys: Vec<ConstId>,
        /// Property values.
        values: Vec<ConstId>,
    },
    /// Nested literal-buffer reference (`LiteralTag::LITERALBUFFERINDEX`)
    /// pointing to a pooled array [`ConstId`].
    LiteralBufferRef(ConstId),
    /// A reference to a function in the module's function table with its
    /// literal method-tag kind (`#57` `R3-H9`).
    MethodRef {
        /// Target function in `Module::functions`.
        func: FuncId,
        /// Literal method tag kind (`Method`, `Getter`, `Setter`, ...).
        kind: LitMethodKind,
    },
}

impl Const {
    /// Build a [`Const::Number`] from an `f64` (bits preserved).
    #[must_use]
    pub fn number(v: f64) -> Self {
        Self::Number(v.to_bits())
    }

    /// Build a [`Const::Float32`] from an `f32` (bits preserved).
    #[must_use]
    pub fn float32(v: f32) -> Self {
        Self::Float32(v.to_bits())
    }

    /// Build a [`Const::MethodRef`] with [`LitMethodKind::Method`].
    #[must_use]
    pub const fn method_ref(func: FuncId) -> Self {
        Self::MethodRef {
            func,
            kind: LitMethodKind::Method,
        }
    }

    /// Build a [`Const::MethodRef`] with an explicit [`LitMethodKind`].
    #[must_use]
    pub const fn method_ref_with_kind(func: FuncId, kind: LitMethodKind) -> Self {
        Self::MethodRef { func, kind }
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

    /// Interpret a [`Const::Float32`] payload as `f32`; `None` for other
    /// variants.
    #[must_use]
    pub fn as_f32(&self) -> Option<f32> {
        match self {
            Const::Float32(bits) => Some(f32::from_bits(*bits)),
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
        assert!(
            std::mem::size_of::<Const>() <= 48,
            "Const size {} exceeded 48B",
            std::mem::size_of::<Const>()
        );
        let mut pool = ConstPool::new();
        let sym = Sym::new(0);
        let c_one = pool.intern(Const::number(1.0));
        let c_null = pool.intern(Const::Null);
        let c_nested_arr = pool.push_array(vec![c_null]);
        let c_str = pool.intern(Const::String(sym));
        let c_two = pool.intern(Const::number(2.0));
        let c_false = pool.intern(Const::Bool(false));
        let c_mref = pool.intern(Const::method_ref(FuncId::new(3)));

        let values = [
            Const::Undefined,
            Const::Hole,
            Const::Null,
            Const::Bool(true),
            Const::Int8(7),
            Const::Int32(0x1234_5678),
            Const::float32(-1.5),
            Const::number(-0.0),
            Const::number(f64::NAN),
            Const::Int64(-42),
            Const::UInt64(u64::MAX),
            Const::Accessor(1),
            Const::MethodAffiliate(2),
            Const::BuiltinTypeIndex(5),
            Const::EtsImplements(sym),
            Const::LitNull(0),
            Const::String(sym),
            Const::BigInt(sym),
            Const::ArrayLiteral(vec![c_one, c_nested_arr]),
            Const::TypedArrayLiteral {
                tag: TypedArrayTag::I32,
                items: vec![c_one],
            },
            Const::ObjectLiteral {
                keys: vec![c_str, c_two],
                values: vec![c_false, c_mref],
            },
            Const::LiteralBufferRef(c_nested_arr),
            Const::method_ref_with_kind(FuncId::new(7), LitMethodKind::Getter),
        ];
        let ids: Vec<ConstId> = values.iter().cloned().map(|c| pool.push(c)).collect();
        for (id, want) in ids.iter().zip(values.iter()) {
            assert_eq!(pool.get(*id), Some(want));
        }
        assert_eq!(pool.intern(Const::Null), c_null);
        assert_eq!(pool.get(ids[6]).and_then(Const::as_f32), Some(-1.5));
        assert_eq!(pool.get(ids[7]).and_then(Const::as_f64), Some(-0.0));
        assert!(pool.get(ids[8]).and_then(Const::as_f64).unwrap().is_nan());
        assert_eq!(pool.get(ids[9]).and_then(Const::as_i64), Some(-42));
        assert_eq!(pool.get(ids[10]).and_then(Const::as_u64), Some(u64::MAX));
        assert_eq!(pool.get(ConstId::new(999)), None);
    }
}
