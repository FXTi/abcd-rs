//! Data structures for a fully-decoded ABC file.
//!
//! Every field is owned — no lifetimes, no raw pointers.

#![forbid(unsafe_code)]

use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap};
use std::ops::Index;
use std::sync::Arc;

use abcd_isa::Version;

use crate::FileType;
use crate::types::{AccessFlags, FunctionKind, HasAccessFlags, SourceLang, Type};
use crate::{StringId, StringPool};

// Re-export leaf types that are already owned.
pub use crate::annotation::{
    AnnotationElem, AnnotationValue, MethodHandleType, ResolvedMethodHandle,
};
pub use crate::code::{CatchBlock, TryBlock};
pub use crate::debug::{ColumnEntry, LineEntry, LocalVarInfo, ParamInfo};
pub use crate::literal::{LiteralArrayIdx, LiteralValue};
pub use crate::module::{ModuleData, ModuleRecord, ModuleRequestPhase};
pub use abcd_isa::{Bytecode, DecodeError};

// ---------------------------------------------------------------------------
// Dense entity indices & typed bytecode entity references (`#50` `R3-D2`)
// ---------------------------------------------------------------------------

/// Dense 0-based index into [`File::all_methods`] (iterating `File::classes`
/// in `BTreeMap` order, then `Class::methods` in `Vec` order).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MethodIdx(pub u32);

impl MethodIdx {
    /// Underlying `usize` index into [`File::all_methods`].
    #[inline]
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Dense 0-based index into [`File::all_fields`] (iterating `File::classes`
/// in `BTreeMap` order, then `Class::fields` in `Vec` order).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FieldIdx(pub u32);

impl FieldIdx {
    /// Underlying `usize` index into [`File::all_fields`].
    #[inline]
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Typed target of a bytecode entity operand in [`MethodBody::entities`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EntityRef {
    /// String entity (`EntityKind::StringId`): interned string + optional
    /// wire offset provenance (`Some(off)` from decode / `.pa` parse for
    /// `ark_disasm` `# STRING` `[offset:0x…]` byte-identity; `None` on
    /// hand-built / lowered models).
    String {
        id: StringId,
        source_offset: Option<u32>,
    },
    /// Method entity (`EntityKind::MethodId`) → [`MethodIdx`] in [`File::all_methods`].
    Method(MethodIdx),
    /// Foreign/unowned method item not present in `Class::methods` (retains
    /// interned name + source offset for `ark_disasm` fallback signature
    /// rendering; rejected with `Error::CodeRelocation` on `encode`).
    ExternalMethod { name: StringId, source_offset: u32 },
    /// Literal-array entity (`EntityKind::LiteralarrayId`) → [`LiteralArrayIdx`]
    /// in [`File::literal_arrays`].
    LiteralArray(LiteralArrayIdx),
}

impl EntityRef {
    /// Construct an offsetless string entity reference.
    #[inline]
    #[must_use]
    pub const fn string(id: StringId) -> Self {
        Self::String {
            id,
            source_offset: None,
        }
    }

    /// Construct a string entity reference carrying wire offset provenance.
    #[inline]
    #[must_use]
    pub const fn string_with_offset(id: StringId, off: u32) -> Self {
        Self::String {
            id,
            source_offset: Some(off),
        }
    }

    /// Construct a method entity reference.
    #[inline]
    #[must_use]
    pub const fn method(idx: MethodIdx) -> Self {
        Self::Method(idx)
    }

    /// Construct a literal-array entity reference.
    #[inline]
    #[must_use]
    pub const fn literal_array(idx: LiteralArrayIdx) -> Self {
        Self::LiteralArray(idx)
    }
}

// ---------------------------------------------------------------------------
// Compact sorted MethodEntities & Dual-mode MethodCode (`#49`)
// ---------------------------------------------------------------------------

#[inline]
const fn entity_key_rank(key: &(abcd_isa::EntityKind, u32)) -> (u8, u32) {
    (key.0 as u8, key.1)
}

#[inline]
fn entity_key_cmp(
    lhs: &(abcd_isa::EntityKind, u32),
    rhs: &(abcd_isa::EntityKind, u32),
) -> Ordering {
    entity_key_rank(lhs).cmp(&entity_key_rank(rhs))
}

/// Compact sorted `(EntityKind, raw_operand_id) -> EntityRef` table on
/// [`MethodBody`] (`#49`).
///
/// Replaces per-method `HashMap` bucket overhead with a dense `Vec` sorted
/// strictly by `(kind as u8, raw_id)` and queried via binary search.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MethodEntities {
    entries: Vec<((abcd_isa::EntityKind, u32), EntityRef)>,
}

impl MethodEntities {
    /// Construct an empty entity table.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Construct an empty entity table with pre-reserved capacity.
    #[inline]
    #[must_use]
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            entries: Vec::with_capacity(cap),
        }
    }

    /// Number of stored `(EntityKind, raw_id)` mappings.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the entity table is empty.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Remove all entries from the table.
    #[inline]
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Whether `key` is present in the table.
    #[inline]
    #[must_use]
    pub fn contains_key(&self, key: &(abcd_isa::EntityKind, u32)) -> bool {
        self.get(key).is_some()
    }

    /// Binary-search lookup by `&(EntityKind, raw_id)`.
    #[inline]
    #[must_use]
    pub fn get(&self, key: &(abcd_isa::EntityKind, u32)) -> Option<&EntityRef> {
        let pos = self
            .entries
            .binary_search_by(|(k, _)| entity_key_cmp(k, key))
            .ok()?;
        Some(&self.entries[pos].1)
    }

    /// Mutable binary-search lookup by `&(EntityKind, raw_id)`.
    #[inline]
    pub fn get_mut(&mut self, key: &(abcd_isa::EntityKind, u32)) -> Option<&mut EntityRef> {
        let pos = self
            .entries
            .binary_search_by(|(k, _)| entity_key_cmp(k, key))
            .ok()?;
        Some(&mut self.entries[pos].1)
    }

    /// Insert or replace `(key, value)`, returning any displaced [`EntityRef`].
    pub fn insert(
        &mut self,
        key: (abcd_isa::EntityKind, u32),
        value: EntityRef,
    ) -> Option<EntityRef> {
        if let Some((last_k, _)) = self.entries.last()
            && entity_key_cmp(last_k, &key).is_lt()
        {
            self.entries.push((key, value));
            return None;
        }
        match self
            .entries
            .binary_search_by(|(k, _)| entity_key_cmp(k, &key))
        {
            Ok(pos) => Some(std::mem::replace(&mut self.entries[pos].1, value)),
            Err(pos) => {
                self.entries.insert(pos, (key, value));
                None
            }
        }
    }

    /// Remove `key` from the table, returning its [`EntityRef`] if present.
    pub fn remove(&mut self, key: &(abcd_isa::EntityKind, u32)) -> Option<EntityRef> {
        let pos = self
            .entries
            .binary_search_by(|(k, _)| entity_key_cmp(k, key))
            .ok()?;
        Some(self.entries.remove(pos).1)
    }

    /// Iterate `(&(EntityKind, raw_id), &EntityRef)` in canonical `(kind, raw_id)` order.
    pub fn iter(
        &self,
    ) -> impl ExactSizeIterator<Item = (&(abcd_isa::EntityKind, u32), &EntityRef)>
    + DoubleEndedIterator
    + '_ {
        self.entries.iter().map(|(k, v)| (k, v))
    }

    /// Iterate `&(EntityKind, raw_id)` keys in canonical `(kind, raw_id)` order.
    pub fn keys(
        &self,
    ) -> impl ExactSizeIterator<Item = &(abcd_isa::EntityKind, u32)> + DoubleEndedIterator + '_
    {
        self.entries.iter().map(|(k, _)| k)
    }

    /// Iterate `&EntityRef` values in canonical `(kind, raw_id)` order.
    pub fn values(&self) -> impl ExactSizeIterator<Item = &EntityRef> + DoubleEndedIterator + '_ {
        self.entries.iter().map(|(_, v)| v)
    }

    /// Mutably iterate `&mut EntityRef` values in canonical `(kind, raw_id)` order.
    pub fn values_mut(
        &mut self,
    ) -> impl ExactSizeIterator<Item = &mut EntityRef> + DoubleEndedIterator + '_ {
        self.entries.iter_mut().map(|(_, v)| v)
    }
}

impl Index<&(abcd_isa::EntityKind, u32)> for MethodEntities {
    type Output = EntityRef;

    fn index(&self, key: &(abcd_isa::EntityKind, u32)) -> &Self::Output {
        match self.get(key) {
            Some(v) => v,
            None => panic!("no entry found for key {key:?} in MethodEntities"),
        }
    }
}

impl FromIterator<((abcd_isa::EntityKind, u32), EntityRef)> for MethodEntities {
    fn from_iter<T: IntoIterator<Item = ((abcd_isa::EntityKind, u32), EntityRef)>>(
        iter: T,
    ) -> Self {
        let raw: Vec<_> = iter.into_iter().collect();
        if raw.is_empty() {
            return Self::new();
        }
        // Tag original position so last-write-wins on duplicate keys after stable sort.
        let mut indexed: Vec<_> = raw.into_iter().enumerate().collect();
        indexed.sort_by(|(ia, (ka, _)), (ib, (kb, _))| {
            entity_key_cmp(ka, kb).then_with(|| ia.cmp(ib))
        });
        let mut entries: Vec<((abcd_isa::EntityKind, u32), EntityRef)> =
            Vec::with_capacity(indexed.len());
        for (_, (k, v)) in indexed {
            if let Some((last_k, last_v)) = entries.last_mut()
                && *last_k == k
            {
                *last_v = v;
            } else {
                entries.push((k, v));
            }
        }
        Self { entries }
    }
}

impl From<HashMap<(abcd_isa::EntityKind, u32), EntityRef>> for MethodEntities {
    fn from(map: HashMap<(abcd_isa::EntityKind, u32), EntityRef>) -> Self {
        // Keys in `HashMap` are unique; sorting by `(kind as u8, raw_id)`
        // establishes a canonical `N20`-deterministic layout independent of
        // `HashMap` bucket iteration order.
        let mut entries: Vec<_> = map.into_iter().collect();
        entries.sort_by(|(ka, _), (kb, _)| entity_key_cmp(ka, kb));
        Self { entries }
    }
}

impl<'a> IntoIterator for &'a MethodEntities {
    type Item = (&'a (abcd_isa::EntityKind, u32), &'a EntityRef);
    type IntoIter = std::iter::Map<
        std::slice::Iter<'a, ((abcd_isa::EntityKind, u32), EntityRef)>,
        fn(
            &'a ((abcd_isa::EntityKind, u32), EntityRef),
        ) -> (&'a (abcd_isa::EntityKind, u32), &'a EntityRef),
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter().map(|(k, v)| (k, v))
    }
}

impl IntoIterator for MethodEntities {
    type Item = ((abcd_isa::EntityKind, u32), EntityRef);
    type IntoIter = std::vec::IntoIter<((abcd_isa::EntityKind, u32), EntityRef)>;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}

/// Validated zero-copy byte range inside a shared `Arc<[u8]>` `.abc` backing
/// buffer for lazy method-body decoding (`#49`).
#[derive(Clone, Debug)]
pub struct MethodSpan {
    pub backing: Arc<[u8]>,
    pub offset: u32,
    pub len: u32,
    pub insn_count: u32,
    pub legacy: bool,
}

impl MethodSpan {
    /// Borrow the raw instruction slice inside [`Self::backing`].
    #[inline]
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        let start = self.offset as usize;
        let end = start.saturating_add(self.len as usize);
        self.backing.get(start..end).unwrap_or(&[])
    }

    fn decode_bytecodes(&self) -> Vec<Bytecode> {
        let raw = self.bytes();
        if raw.is_empty() {
            return Vec::new();
        }
        let res = if self.legacy {
            abcd_isa::decode_legacy(raw)
        } else {
            abcd_isa::decode(raw)
        };
        match res {
            Ok(pairs) => pairs.into_iter().map(|(bc, _)| bc).collect(),
            Err(_) => Vec::new(),
        }
    }
}

impl PartialEq for MethodSpan {
    fn eq(&self, other: &Self) -> bool {
        self.insn_count == other.insn_count
            && self.legacy == other.legacy
            && self.bytes() == other.bytes()
    }
}

impl Eq for MethodSpan {}

/// Dual-mode method instruction storage (`#49`): either eagerly materialized
/// [`Bytecode`]s or a validated zero-copy [`MethodSpan`] into the source `.abc`
/// backing buffer.
#[derive(Clone, Debug, PartialEq)]
pub enum MethodCode {
    Decoded(Vec<Bytecode>),
    Span(MethodSpan),
}

impl Default for MethodCode {
    #[inline]
    fn default() -> Self {
        Self::Decoded(Vec::new())
    }
}

impl From<Vec<Bytecode>> for MethodCode {
    #[inline]
    fn from(v: Vec<Bytecode>) -> Self {
        Self::Decoded(v)
    }
}

impl MethodCode {
    /// Number of instructions in the method without materializing lazy spans.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        match self {
            Self::Decoded(v) => v.len(),
            Self::Span(s) => s.insn_count as usize,
        }
    }

    /// Whether the method contains zero instructions.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Borrow decoded instructions directly when eager, or decode transiently
    /// on the fly when backed by a [`MethodSpan`].
    #[must_use]
    pub fn decode_cow(&self) -> Cow<'_, [Bytecode]> {
        match self {
            Self::Decoded(v) => Cow::Borrowed(v.as_slice()),
            Self::Span(s) => Cow::Owned(s.decode_bytecodes()),
        }
    }

    /// Consume `self` and return an owned `Vec<Bytecode>`.
    #[must_use]
    pub fn into_vec(self) -> Vec<Bytecode> {
        match self {
            Self::Decoded(v) => v,
            Self::Span(s) => s.decode_bytecodes(),
        }
    }
}

// ---------------------------------------------------------------------------
// Data structures
// ---------------------------------------------------------------------------

/// Fully-decoded ABC file.
#[derive(Clone, Debug)]
pub struct File {
    pub version: Version,
    pub checksum: u32,
    pub size: u32,
    pub file_type: FileType,
    /// String interner — all string data lives here.
    pub strings: StringPool,
    /// Classes keyed by interned descriptor (e.g. `"L_GLOBAL;"`).
    pub classes: BTreeMap<StringId, Class>,
    /// Literal arrays (indexed by [`LiteralArrayIdx`]). Beyond header-table
    /// entries this includes arrays reached through method index regions,
    /// scope-names / type-summary fields, and nested literal-array payloads
    /// recovered transitively at decode.
    pub literal_arrays: Vec<LiteralArray>,
    /// The raw header literal-array index table, in header order and
    /// INCLUDING the module-record / module-request-phase blob slots that
    /// [`File::literal_arrays`] excludes (they are untagged blobs, not
    /// literal arrays). Only populated for files whose header carries the
    /// table (version ≤ 12.0.6.0 — vendored
    /// `LAST_CONTAINS_LITERAL_IN_HEADER_VERSION`); empty for 13.x+/24.x
    /// (no header table) and for hand-built models. The pandasm emitter's
    /// byte-identity with upstream `ark_disasm` depends on the original
    /// header positions, which are otherwise unrecoverable once the
    /// excluded slots are dropped.
    pub literal_array_header_offsets: Vec<u32>,
}

/// A decoded class with nested methods, fields, and annotations.
#[derive(Clone, Debug)]
pub struct Class {
    pub descriptor: StringId,
    pub name: StringId,
    pub access_flags: AccessFlags,
    pub source_lang: SourceLang,
    pub source_file: Option<StringId>,
    pub is_external: bool,
    pub super_class: Option<StringId>,
    pub interfaces: Vec<StringId>,
    pub methods: Vec<Method>,
    pub fields: Vec<Field>,
    pub annotations: Annotations,
}

/// A decoded method.
#[derive(Clone, Debug)]
pub struct Method {
    pub name: StringId,
    /// Offset of the method item in the source file; 0 for hand-built
    /// models. This is the file's unique method identity — names are not
    /// unique across classes.
    pub offset: u32,
    pub access_flags: AccessFlags,
    pub function_kind: FunctionKind,
    pub source_lang: SourceLang,
    pub is_external: bool,
    pub return_type: Option<Type>,
    pub arg_types: Vec<Type>,
    pub body: Option<MethodBody>,
    pub annotations: Annotations,
    /// Per-parameter annotations, indexed by parameter position.
    pub param_annotations: ParamAnnotations,
    pub debug: Option<MethodDebugInfo>,
}

/// Per-parameter annotations, indexed by parameter position.
///
/// Both `compile_time` (`MethodTag::PARAM_ANNOTATION`) and `runtime`
/// (`MethodTag::RUNTIME_PARAM_ANNOTATION`) buckets are decoded and sealed
/// independently on [`crate::encode`] without cross-bucket folding.
#[derive(Clone, Debug, Default)]
pub struct ParamAnnotations {
    pub compile_time: Vec<Vec<Annotation>>,
    pub runtime: Vec<Vec<Annotation>>,
}

/// A decoded field.
#[derive(Clone, Debug)]
pub struct Field {
    pub name: StringId,
    /// Offset of the field item in the source file; 0 for hand-built
    /// models. This is the file's unique field identity — names are not
    /// unique across classes.
    pub offset: u32,
    pub field_type: Type,
    pub access_flags: AccessFlags,
    pub is_external: bool,
    pub initial_value: Option<FieldValue>,
    pub annotations: Annotations,
}

/// Initial value of a field.
#[derive(Clone, Debug, PartialEq)]
pub enum FieldValue {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    /// String item reference (`FieldTag::VALUE` + `u32` `StringItem` offset),
    /// used for static/constant string fields (`Type::Reference` or `Type::U32`).
    String(StringId),
    /// Module-record field (standalone `_ESModuleRecord`, or `moduleRecordIdx`
    /// on the module's own record class in `--merge-abc` output): the u32 wire
    /// value is the source-file offset of an untagged ModuleDataAccessor-format
    /// blob (vendored `module_data_accessor-inl.h`). Decode reads the blob
    /// structurally into this model; encode re-emits it as a fresh
    /// literal-array item and writes the field value as the item's NEW layout
    /// offset (never the stale source offset).
    ModuleData(ModuleData),
    /// Tagged literal-array reference field (standalone `_ESScopeNamesRecord`,
    /// `scopeNames` on `--merge-abc` module records, or non-zero
    /// `typeSummaryOffset` fields): `index` names the decoded entry in
    /// [`File::literal_arrays`] used by [`crate::encode`], while
    /// `source_offset` optionally retains the wire offset for `pandasm`
    /// byte-identity with `ark_disasm`.
    LiteralArrayRef {
        index: LiteralArrayIdx,
        source_offset: Option<u32>,
    },
    /// `moduleRequestPhaseIdx` field (on `_ModuleRequestPhaseRecord`, or on
    /// the module's own record in merge-abc output): the u32 wire value is
    /// the source-file offset of an untagged module-request-phase blob
    /// (vendored `ModuleLazyImportFlagAccessor` layout). Decode reads the
    /// blob structurally; encode re-emits it and relocates the field value,
    /// exactly like [`FieldValue::ModuleData`].
    ModuleRequestPhase(ModuleRequestPhase),
    /// `jsonFileContent` field (`--merge-abc` JSON module record emitted by
    /// `es2panda` `Emitter::GenJsonContentRecord`, read at runtime by
    /// `JSPandaFile` via `GetStringData(EntityId(offset))`): the u32 wire value
    /// is the source-file offset of a `StringItem` holding the raw JSON text.
    /// Decode resolves the string (keeping `source_offset` for `pandasm`
    /// byte-identity with `ark_disasm`); encode re-emits a `ScalarValueItem`
    /// `Type::ID` over the `StringItem` so the offset relocates automatically.
    JsonFileContent {
        source_offset: u32,
        content: StringId,
    },
}

impl FieldValue {
    /// Construct an offsetless [`FieldValue::LiteralArrayRef`] pointing at `index`.
    #[inline]
    #[must_use]
    pub const fn literal_array_ref(index: LiteralArrayIdx) -> Self {
        Self::LiteralArrayRef {
            index,
            source_offset: None,
        }
    }
}

/// Decoded method body (dual-mode instructions + exception handlers).
#[derive(Clone, Debug)]
pub struct MethodBody {
    /// Number of virtual registers used by this method.
    pub num_vregs: u32,
    /// Number of arguments (including `this` for instance methods).
    pub num_args: u32,
    /// Dual-mode instruction payload (`Decoded(Vec<Bytecode>)` or lazy
    /// zero-copy `Span(MethodSpan)`).
    pub code: MethodCode,
    /// `(EntityKind, raw_operand_id)` → resolved [`EntityRef`]. Bytecodes
    /// retain their raw immediate/index operands while semantic consumers and
    /// [`crate::encode`] consult this compact sorted table directly.
    pub entities: MethodEntities,
    pub try_blocks: Vec<TryBlock>,
    /// Total IC-slot consumption of this bytecode, as computed by the
    /// lower that produced it (N73).
    ///
    /// `None` for decoded bodies: a plain decode → encode round-trip
    /// keeps the source annotation verbatim. `Some(n)` tells [`crate::encode`]
    /// to sync the method's `SlotNumber` element to `n`.
    pub ic_size: Option<u32>,
}

impl MethodBody {
    /// Borrow decoded instructions directly when eager, or decode transiently
    /// on the fly when backed by a lazy [`MethodSpan`].
    #[must_use]
    pub fn bytecodes(&self) -> Cow<'_, [Bytecode]> {
        self.code.decode_cow()
    }

    /// Number of instructions in this method body without materializing lazy spans.
    #[inline]
    #[must_use]
    pub fn insn_count(&self) -> usize {
        self.code.len()
    }
}

/// Four kinds of annotations grouped by retention policy.
#[derive(Clone, Debug, Default)]
pub struct Annotations {
    pub compile_time: Vec<Annotation>,
    pub runtime: Vec<Annotation>,
    pub compile_time_type: Vec<Annotation>,
    pub runtime_type: Vec<Annotation>,
}

/// A single decoded annotation.
pub struct Annotation {
    pub class_descriptor: StringId,
    pub elements: Vec<AnnotationElem>,
}

/// Per-method debug information.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MethodDebugInfo {
    pub source_file: Option<StringId>,
    pub source_code: Option<StringId>,
    pub line_table: Vec<LineEntry>,
    pub column_table: Vec<ColumnEntry>,
    pub local_vars: Vec<LocalVarInfo>,
    pub params: Vec<ParamInfo>,
}

/// Decoded literal array.
#[derive(Clone, Debug, PartialEq)]
pub struct LiteralArray {
    /// Optional wire offset in the source `.abc` / `.pa` file (`None` on
    /// hand-built or lowered models).
    pub source_offset: Option<u32>,
    pub values: Vec<LiteralValue>,
}

impl LiteralArray {
    /// Create a literal array without wire offset provenance (`source_offset: None`).
    #[inline]
    #[must_use]
    pub const fn new(values: Vec<LiteralValue>) -> Self {
        Self {
            source_offset: None,
            values,
        }
    }

    /// Create a literal array recording its wire `source_offset`.
    #[inline]
    #[must_use]
    pub const fn with_source_offset(source_offset: u32, values: Vec<LiteralValue>) -> Self {
        Self {
            source_offset: Some(source_offset),
            values,
        }
    }
}

// ---------------------------------------------------------------------------
// Convenience methods
// ---------------------------------------------------------------------------

impl File {
    /// Bytecode dialect implied by [`Self::file_type`] and [`Self::version`].
    #[inline]
    pub const fn dialect(&self) -> Option<crate::Dialect> {
        crate::Dialect::from_header(self.file_type, self.version)
    }

    /// Look up a class by descriptor string (convenience).
    pub fn class_by_str(&self, descriptor: &str) -> Option<&Class> {
        let sid = self.strings.get(descriptor)?;
        self.classes.get(&sid)
    }

    /// Flat iterator over `(class_descriptor, method)` across all classes
    /// (indexed by [`MethodIdx`]).
    pub fn all_methods(&self) -> impl Iterator<Item = (StringId, &Method)> {
        self.classes
            .iter()
            .flat_map(|(&desc, c)| c.methods.iter().map(move |m| (desc, m)))
    }

    /// Flat iterator over `(class_descriptor, field)` across all classes
    /// (indexed by [`FieldIdx`]).
    pub fn all_fields(&self) -> impl Iterator<Item = (StringId, &Field)> {
        self.classes
            .iter()
            .flat_map(|(&desc, c)| c.fields.iter().map(move |f| (desc, f)))
    }

    /// Dense `(class_descriptor, class, method)` table indexed by [`MethodIdx`].
    #[must_use]
    pub fn method_table(&self) -> Vec<(StringId, &Class, &Method)> {
        self.classes
            .iter()
            .flat_map(|(&desc, c)| c.methods.iter().map(move |m| (desc, c, m)))
            .collect()
    }

    /// Look up `(class_descriptor, class, method)` by [`MethodIdx`].
    #[must_use]
    pub fn method_by_idx(&self, idx: MethodIdx) -> Option<(StringId, &Class, &Method)> {
        let mut rem = idx.index();
        for (&desc, cls) in &self.classes {
            if rem < cls.methods.len() {
                return Some((desc, cls, &cls.methods[rem]));
            }
            rem -= cls.methods.len();
        }
        None
    }

    /// Look up `(class_descriptor, class, field)` by [`FieldIdx`].
    #[must_use]
    pub fn field_by_idx(&self, idx: FieldIdx) -> Option<(StringId, &Class, &Field)> {
        let mut rem = idx.index();
        for (&desc, cls) in &self.classes {
            if rem < cls.fields.len() {
                return Some((desc, cls, &cls.fields[rem]));
            }
            rem -= cls.fields.len();
        }
        None
    }

    /// Find the first [`LiteralArray`] carrying `source_offset == Some(off)`.
    #[must_use]
    pub fn literal_array_by_offset(&self, off: u32) -> Option<(LiteralArrayIdx, &LiteralArray)> {
        self.literal_arrays.iter().enumerate().find_map(|(i, la)| {
            (la.source_offset == Some(off)).then_some((LiteralArrayIdx(i as u32), la))
        })
    }

    /// Decode module data from the literal array at the given index.
    ///
    /// Module data is stored as a special literal array in ABC files.
    /// Returns `Err` if the index is out of bounds or the data cannot be
    /// parsed as valid module data.
    pub fn decode_module(&self, index: usize) -> Result<ModuleData, crate::Error> {
        let la = self
            .literal_arrays
            .get(index)
            .ok_or_else(|| crate::Error::Malformed {
                field: "literal_array_index",
                context: format!("index {index} out of bounds"),
            })?;
        ModuleData::from_literal_values(&la.values)
    }
}

impl HasAccessFlags for Method {
    fn access_flags(&self) -> AccessFlags {
        self.access_flags
    }
}
