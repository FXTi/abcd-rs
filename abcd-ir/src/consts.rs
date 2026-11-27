//! Typed constant pool (`design/ir.md`, `#57` `R3-H9`, `#72`, `#77`):
//! literal-array table indices and container offsets stay in the file layer;
//! the IR stores semantic [`Const`] values and [`ConstId`]-linked literal
//! shapes with lossless tag fidelity.
//!
//! The pool is append-only (`T1`): pushing or interning a constant never
//! changes an existing [`ConstId`]. Array/object/typed-array literal shapes
//! reference child constants via [`ConstId`], keeping [`Const`] flat and
//! non-recursive. Deduplication uses `hashbrown::HashTable<u32>` indexing
//! `consts: Vec<Const>` directly with zero duplicate [`Const`] clones (`#72`).

use std::fmt;
use std::hash::{BuildHasher, RandomState};

use hashbrown::HashTable;

use crate::id::{ConstId, FuncId, Sym};

/// Capacity overflow error returned by [`ConstPool::try_push`] and
/// [`ConstPool::try_intern`] when the pool count reaches `u32::MAX`
/// (`ConstId(u32::MAX)` is reserved as an unmapped sentinel; `#77`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
#[error("ConstPool entry count reached u32::MAX sentinel limit")]
pub struct ConstPoolOverflow;

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

#[derive(Clone)]
struct ConstIndex {
    hasher: RandomState,
    table: HashTable<u32>,
}

impl ConstIndex {
    fn new() -> Self {
        Self {
            hasher: RandomState::new(),
            table: HashTable::new(),
        }
    }

    fn rebuild(consts: &[Const]) -> Self {
        let hasher = RandomState::new();
        let mut table = HashTable::with_capacity(consts.len());
        for (i, c) in consts.iter().enumerate() {
            let hash = hasher.hash_one(c);
            if table
                .find(hash, |&existing_id| &consts[existing_id as usize] == c)
                .is_none()
            {
                let raw_id = i as u32;
                table.insert_unique(hash, raw_id, |&existing_id| {
                    hasher.hash_one(&consts[existing_id as usize])
                });
            }
        }
        Self { hasher, table }
    }
}

#[inline]
const fn check_const_capacity(cur_len: usize) -> Result<u32, ConstPoolOverflow> {
    if cur_len >= (u32::MAX as usize) {
        return Err(ConstPoolOverflow);
    }
    Ok(cur_len as u32)
}

/// Append-only pool of typed constants (`T1`) supporting both unguarded
/// [`Self::push`] and deduplicating [`Self::intern`] without cloning map keys
/// (`#72`, `#77`).
#[derive(Clone)]
pub struct ConstPool {
    consts: Vec<Const>,
    index: Option<ConstIndex>,
}

impl Default for ConstPool {
    fn default() -> Self {
        Self {
            consts: Vec::new(),
            index: Some(ConstIndex::new()),
        }
    }
}

impl fmt::Debug for ConstPool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ConstPool")
            .field("consts", &self.consts)
            .field("has_index", &self.has_index())
            .finish()
    }
}

impl PartialEq for ConstPool {
    fn eq(&self, other: &Self) -> bool {
        self.consts == other.consts
    }
}

impl Eq for ConstPool {}

impl ConstPool {
    /// An empty pool with an active deduplication index.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Release the hash-table deduplication index while retaining all pooled
    /// [`Const`] entries (`#72`).
    ///
    /// [`Self::get`] and [`Self::lookup`] remain total after `drop_index()`,
    /// and subsequent [`Self::push`] / [`Self::intern`] calls rebuild the index
    /// automatically.
    pub fn drop_index(&mut self) {
        self.index = None;
    }

    /// Whether the hash-table deduplication index is currently resident.
    #[must_use]
    #[inline]
    pub fn has_index(&self) -> bool {
        self.index.is_some()
    }

    fn ensure_index(&mut self) {
        if self.index.is_none() {
            self.index = Some(ConstIndex::rebuild(&self.consts));
        }
    }

    /// Look up the canonical (first-inserted) [`ConstId`] equal to `c` without
    /// mutating the pool.
    ///
    /// Uses `O(1)` hash lookup when [`Self::has_index`] is `true`, or a total
    /// `O(len)` scan over `consts` after [`Self::drop_index`].
    #[must_use]
    pub fn lookup(&self, c: &Const) -> Option<ConstId> {
        if let Some(index) = &self.index {
            let hash = index.hasher.hash_one(c);
            return index
                .table
                .find(hash, |&id| &self.consts[id as usize] == c)
                .copied()
                .map(ConstId::new);
        }
        self.consts
            .iter()
            .position(|existing| existing == c)
            .map(|idx| ConstId::new(idx as u32))
    }

    /// Fallibly append a constant unconditionally, returning [`ConstPoolOverflow`]
    /// if the pool has reached `u32::MAX` entries (`#77`).
    ///
    /// Preserves `or_insert` index semantics: if an equal [`Const`] was already
    /// present, its earlier [`ConstId`] remains the canonical target for
    /// [`Self::lookup`] and [`Self::intern`].
    pub fn try_push(&mut self, c: Const) -> Result<ConstId, ConstPoolOverflow> {
        let raw = check_const_capacity(self.consts.len())?;
        self.ensure_index();
        self.consts.push(c);
        let Some(index) = &mut self.index else {
            unreachable!("ensure_index populated self.index");
        };
        let inserted = &self.consts[raw as usize];
        let hash = index.hasher.hash_one(inserted);
        if index
            .table
            .find(hash, |&id| &self.consts[id as usize] == inserted)
            .is_none()
        {
            let consts = &self.consts;
            index.table.insert_unique(hash, raw, |&existing_id| {
                index.hasher.hash_one(&consts[existing_id as usize])
            });
        }
        Ok(ConstId::new(raw))
    }

    /// Append a constant unconditionally, returning its [`ConstId`]. Ids are
    /// stable: a push never renumbers earlier entries.
    pub fn push(&mut self, c: Const) -> ConstId {
        self.try_push(c).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Fallible deduplicating append: returns the existing canonical [`ConstId`]
    /// if an equal [`Const`] was already interned or pushed, otherwise appends
    /// `c` (or returns [`ConstPoolOverflow`] if the pool is at `u32::MAX`).
    pub fn try_intern(&mut self, c: Const) -> Result<ConstId, ConstPoolOverflow> {
        self.ensure_index();
        let Some(index) = &mut self.index else {
            unreachable!("ensure_index populated self.index");
        };
        let hash = index.hasher.hash_one(&c);
        if let Some(&id) = index.table.find(hash, |&id| self.consts[id as usize] == c) {
            return Ok(ConstId::new(id));
        }
        let raw = check_const_capacity(self.consts.len())?;
        self.consts.push(c);
        let consts = &self.consts;
        index.table.insert_unique(hash, raw, |&existing_id| {
            index.hasher.hash_one(&consts[existing_id as usize])
        });
        Ok(ConstId::new(raw))
    }

    /// Deduplicating append: returns the existing [`ConstId`] if an identical
    /// [`Const`] was already interned or pushed, otherwise appends it.
    pub fn intern(&mut self, c: Const) -> ConstId {
        self.try_intern(c).unwrap_or_else(|e| panic!("{e}"))
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

    #[test]
    fn const_pool_push_preserves_first_id_drop_index_lookup_and_no_key_cloning() {
        let mut pool = ConstPool::new();
        assert!(pool.has_index());

        // `push` with a heap-backed `ArrayLiteral` must keep its original `Vec` buffer
        // in `pool.consts` without cloning a second `Vec` into the hash index.
        let items = vec![ConstId::new(0), ConstId::new(1), ConstId::new(2)];
        let items_ptr = items.as_ptr();
        let arr_first = pool.push(Const::ArrayLiteral(items));
        let Some(Const::ArrayLiteral(stored)) = pool.get(arr_first) else {
            panic!("expected ArrayLiteral");
        };
        assert_eq!(
            stored.as_ptr(),
            items_ptr,
            "push must move Const into Vec without reallocating or cloning"
        );

        // Duplicate `push` appends a distinct ID while keeping `arr_first` canonical!
        let arr_dup = pool.push(Const::ArrayLiteral(vec![
            ConstId::new(0),
            ConstId::new(1),
            ConstId::new(2),
        ]));
        assert_ne!(arr_first, arr_dup);
        let probe = Const::ArrayLiteral(vec![ConstId::new(0), ConstId::new(1), ConstId::new(2)]);
        assert_eq!(pool.lookup(&probe), Some(arr_first));
        assert_eq!(pool.intern(probe.clone()), arr_first);

        // `drop_index` preserves `PartialEq`, `lookup`, and `or_insert` first-ID parity on rebuild.
        let before_drop = pool.clone();
        pool.drop_index();
        assert!(!pool.has_index());
        assert_eq!(pool, before_drop);
        assert_eq!(pool.lookup(&probe), Some(arr_first));
        assert_eq!(pool.lookup(&Const::Undefined), None);
        assert!(!pool.has_index(), "lookup(&self) must not rebuild index");

        let c_undef = pool.try_intern(Const::Undefined).unwrap();
        assert!(pool.has_index());
        assert_eq!(pool.intern(probe), arr_first);
        assert_eq!(pool.lookup(&Const::Undefined), Some(c_undef));

        assert_eq!(
            check_const_capacity((u32::MAX as usize) - 1),
            Ok(u32::MAX - 1)
        );
        assert_eq!(
            check_const_capacity(u32::MAX as usize),
            Err(ConstPoolOverflow)
        );
    }
}
