//! Data structures for a fully-decoded ABC file.
//!
//! Every field is owned — no lifetimes, no raw pointers.

use std::collections::{BTreeMap, HashMap};

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
    /// through the vendored accessor into this structural model; encode
    /// re-emits it as a fresh literal-array item and writes the field value as
    /// the item's NEW layout offset (never the stale source offset).
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

/// Decoded method body (bytecodes + exception handlers).
#[derive(Clone, Debug)]
pub struct MethodBody {
    /// Number of virtual registers used by this method.
    pub num_vregs: u32,
    /// Number of arguments (including `this` for instance methods).
    pub num_args: u32,
    pub bytecodes: Vec<Bytecode>,
    /// `(EntityKind, raw_operand_id)` → resolved [`EntityRef`]. Bytecodes
    /// retain their raw immediate/index operands while semantic consumers and
    /// [`crate::encode`] consult this table directly without raw file offsets.
    pub entities: HashMap<(abcd_isa::EntityKind, u32), EntityRef>,
    pub try_blocks: Vec<TryBlock>,
    /// Total IC-slot consumption of this bytecode, as computed by the
    /// lower that produced it (N73).
    ///
    /// `None` for decoded bodies: a plain decode → encode round-trip
    /// keeps the source annotation verbatim. `Some(n)` tells [`crate::encode`]
    /// to sync the method's `SlotNumber` element to `n`.
    pub ic_size: Option<u32>,
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
