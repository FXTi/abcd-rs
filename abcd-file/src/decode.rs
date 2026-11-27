//! Eagerly-decoded, fully-owned representation of an ABC file.
//!
//! Call [`decode`] to parse raw bytes into a [`File`] struct.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::ffi::{CStr, c_void};

use abcd_file_sys as sys;

use crate::code::{CatchBlock, TryBlock};
use crate::debug::{ModelDebugSink, decode_method_debug_item};
use crate::error::Error;
use crate::file::{ABSENT, StringItemCache, is_external, read_string};
use crate::model::*;
use crate::types::{AccessFlags, Dialect, FunctionKind, SourceLang, Type, TypeId};
use crate::{StringId, StringPool};

#[inline]
fn decode_source_lang(raw: u8) -> Result<SourceLang, Error> {
    if raw == u8::MAX {
        Ok(SourceLang::PandaAssembly)
    } else {
        SourceLang::try_from(raw)
    }
}

/// Decode the 8-bit `panda_file::FunctionKind` stored in `access_flags_` bits
/// `8..15` (`file_items.h:74-85`). Upstream defines `SENDABLE_FUNCTION = 1 << 3`
/// (`0x08`) as a bit flag combined with non-concurrent base kinds (`FUNCTION`,
/// `NC_FUNCTION`, `GENERATOR_FUNCTION`, `ASYNC_FUNCTION`,
/// `ASYNC_GENERATOR_FUNCTION`, `ASYNC_NC_FUNCTION`).
#[inline]
fn decode_function_kind_from_flags(raw_flags: u32) -> Result<FunctionKind, Error> {
    let raw = ((raw_flags >> 8) & 0xFF) as u8;
    if let Ok(kind) = FunctionKind::try_from(raw) {
        return Ok(kind);
    }
    let sendable = sys::FunctionKind_SENDABLE_FUNCTION;
    if (raw & !0x07) == sendable {
        let base = raw & 0x07;
        if base == sys::FunctionKind_FUNCTION {
            return Ok(FunctionKind::SendableFunction);
        }
        if base != sys::FunctionKind_CONCURRENT_FUNCTION
            && let Ok(kind) = FunctionKind::try_from(base)
        {
            return Ok(kind);
        }
    }
    Err(Error::UnknownFunctionKind(raw))
}

#[inline]
fn check_supported_dialect(
    file_type: sys::FileType,
    version: abcd_isa::Version,
) -> Result<Dialect, Error> {
    if version == abcd_isa::Version::new(0, 1, 0, 7) || file_type == sys::FileType::Static {
        return Err(Error::Malformed {
            field: "file_type",
            context: format!("static .abc container (version {version}) is not supported"),
        });
    }
    if version == Dialect::LEGACY_VERSION {
        Ok(Dialect::DynamicLegacy)
    } else {
        Ok(Dialect::DynamicModern)
    }
}

// ---------------------------------------------------------------------------
// RAII guard for C handles
// ---------------------------------------------------------------------------

/// Calls a closure on drop. Used to ensure C handles are closed.
struct HandleGuard<F: FnOnce()>(Option<F>);

impl<F: FnOnce()> Drop for HandleGuard<F> {
    fn drop(&mut self) {
        if let Some(f) = self.0.take() {
            f();
        }
    }
}

// ---------------------------------------------------------------------------
// decode()
// ---------------------------------------------------------------------------

/// Decode an ABC file from raw bytes into a fully-owned [`File`].
pub fn decode(data: &[u8]) -> Result<File, Error> {
    use crate::file::AbcFile;

    let abc = AbcFile::open(data)?;
    let f = abc.raw;
    let version = abc.version();
    // Legacy ISA gate: files written by the pre-2022-08-18 toolchain
    // (OpenHarmony 3.0/3.1-era, header version 0.0.0.2 — seen in the wild on
    // 3.2/4.0 devices) use the old opcode numbering (0xff-prefixed ecma
    // instructions) and old operand encoding (32-bit string file offsets,
    // 16-bit global literal-array indices). Their bytecode is decoded via
    // abcd_isa::decode_legacy and their entity operands resolved with legacy
    // rules below.
    let dialect = check_supported_dialect(crate::file::file_type(data), version)?;
    let legacy = dialect == Dialect::DynamicLegacy;
    let legacy_lit_table = if legacy {
        legacy_literalarray_table(data)
    } else {
        None
    };
    let checksum = abc.checksum();
    let size = abc.size();
    let file_type = crate::file::file_type(data);
    let file_bytes = data
        .get(..size as usize)
        .ok_or_else(|| Error::Open("declared file_size exceeds buffer".into()))?;

    let mut strings = StringPool::new();
    let mut str_cache = StringItemCache::new(f, file_bytes);

    struct StagedClass {
        class_off: u32,
        class_id: u32,
        descriptor: StringId,
        descriptor_str: String,
        is_external: bool,
        method_offs: Vec<u32>,
        field_offs: Vec<u32>,
    }

    // Pass 1: single-pass class/method/field header scan building `entity_map`
    // and caching member offset lists so Pass 2 avoids re-enumerating headers.
    let mut entity_map = HashMap::new();
    // SAFETY: `f` is a live `AbcFileHandle`.
    let num_classes = unsafe { sys::abc_file_num_classes(f) };
    let mut staged_classes = Vec::with_capacity(num_classes.min(size / 4) as usize);
    for i in 0..num_classes {
        // SAFETY: `f` is a live `AbcFileHandle`.
        let class_off = unsafe { sys::abc_file_class_offset(f, i) };
        if class_off == ABSENT {
            return Err(Error::InvalidOffset(class_off));
        }
        if is_external(f, class_off) {
            if let Some(sid) = str_cache.intern_lossy(class_off, &mut strings) {
                entity_map.insert(class_off, sid);
                staged_classes.push(StagedClass {
                    class_off,
                    class_id: class_off,
                    descriptor: sid,
                    descriptor_str: String::new(),
                    is_external: true,
                    method_offs: Vec::new(),
                    field_offs: Vec::new(),
                });
            }
            continue;
        }
        // SAFETY: `f` is live and `class_off` is non-external.
        let cr = unsafe { sys::abc_class_open(f, class_off) };
        if cr.is_null() {
            return Err(Error::InvalidOffset(class_off));
        }
        let _cg = HandleGuard(Some(|| {
            // SAFETY: `cr` is non-null and owned by this scope.
            unsafe { sys::abc_class_close(cr) };
        }));

        // SAFETY: `cr` is a valid `AbcClassAccessor`.
        let class_id = unsafe { sys::abc_class_get_class_id(cr) };
        let Some((desc_sid, descriptor_str)) =
            read_class_descriptor_cached(cr, class_id, &mut str_cache, &mut strings)
        else {
            continue;
        };
        entity_map.insert(class_id, desc_sid);

        let method_offs = collect_offsets_void(
            cr,
            sys::abc_class_enumerate_methods,
            "class_methods",
            class_off,
        )?;
        for &off in &method_offs {
            // SAFETY: `f` is live.
            let mr = unsafe { sys::abc_method_open(f, off) };
            if mr.is_null() {
                continue;
            }
            let _mg = HandleGuard(Some(|| {
                // SAFETY: `mr` is non-null and owned by this scope.
                unsafe { sys::abc_method_close(mr) };
            }));
            if let Some(sid) = str_cache.intern_method_name(off, mr, &mut strings) {
                // SAFETY: `mr` is valid.
                entity_map.insert(unsafe { sys::abc_method_get_method_id(mr) }, sid);
            }
        }

        let field_offs = collect_offsets_void(
            cr,
            sys::abc_class_enumerate_fields,
            "class_fields",
            class_off,
        )?;
        for &off in &field_offs {
            // SAFETY: `f` is live.
            let fr = unsafe { sys::abc_field_open(f, off) };
            if fr.is_null() {
                continue;
            }
            let _fg = HandleGuard(Some(|| {
                // SAFETY: `fr` is non-null and owned by this scope.
                unsafe { sys::abc_field_close(fr) };
            }));
            // SAFETY: `fr` is valid.
            let name_off = unsafe { sys::abc_field_name_off(fr) };
            if name_off != ABSENT
                && let Some(sid) = str_cache.intern_lossy(name_off, &mut strings)
            {
                // SAFETY: `fr` is valid.
                entity_map.insert(unsafe { sys::abc_field_get_field_id(fr) }, sid);
            }
        }

        staged_classes.push(StagedClass {
            class_off,
            class_id,
            descriptor: desc_sid,
            descriptor_str,
            is_external: is_external(f, class_id),
            method_offs,
            field_offs,
        });
    }

    // --- classes ---
    let mut classes = BTreeMap::new();
    let mut module_data_offsets: HashSet<u32> = HashSet::new();
    let mut scope_names_offsets: HashSet<u32> = HashSet::new();
    let mut phase_blob_offsets: HashSet<u32> = HashSet::new();
    let mut ann_visiting: HashSet<u32> = HashSet::new();

    for staged in staged_classes {
        if classes.contains_key(&staged.descriptor) {
            let dup = strings.resolve(staged.descriptor).unwrap_or("?").to_owned();
            return Err(Error::Malformed {
                field: "class",
                context: format!("duplicate class descriptor {dup:?}"),
            });
        }
        if staged.is_external
            && staged.class_off == staged.class_id
            && staged.descriptor_str.is_empty()
        {
            classes.insert(
                staged.descriptor,
                Class {
                    descriptor: staged.descriptor,
                    name: staged.descriptor,
                    access_flags: AccessFlags::empty(),
                    source_lang: SourceLang::PandaAssembly,
                    source_file: None,
                    is_external: true,
                    super_class: None,
                    interfaces: Vec::new(),
                    methods: Vec::new(),
                    fields: Vec::new(),
                    annotations: Annotations::default(),
                },
            );
            continue;
        }

        // SAFETY: `f` is live and `staged.class_off` was already validated in Pass 1.
        let cr = unsafe { sys::abc_class_open(f, staged.class_off) };
        if cr.is_null() {
            return Err(Error::InvalidOffset(staged.class_off));
        }
        let _cg = HandleGuard(Some(|| {
            // SAFETY: `cr` is non-null and owned by this scope.
            unsafe { sys::abc_class_close(cr) };
        }));

        let name = str_cache
            .intern_utf8(staged.class_id, &mut strings)
            .ok_or_else(|| Error::Malformed {
                field: "name",
                context: format!("class {}", staged.descriptor_str),
            })?;

        // SAFETY: `cr` is valid.
        let sf_off = unsafe { sys::abc_class_source_file_off(cr) };
        // SAFETY: `cr` is valid.
        let source_lang = decode_source_lang(unsafe { sys::abc_class_get_source_lang(cr) })?;

        let mut methods = Vec::with_capacity(staged.method_offs.len());
        for off in staged.method_offs {
            methods.push(decode_method_at(
                f,
                file_bytes,
                off,
                staged.class_id,
                sf_off,
                dialect,
                &entity_map,
                &mut strings,
                &mut str_cache,
                &mut ann_visiting,
            )?);
        }

        let mut fields = Vec::with_capacity(staged.field_offs.len());
        for off in staged.field_offs {
            fields.push(decode_field_at(
                f,
                file_bytes,
                off,
                &entity_map,
                &mut strings,
                &mut str_cache,
                &mut ann_visiting,
                &staged.descriptor_str,
                &mut module_data_offsets,
                &mut scope_names_offsets,
                &mut phase_blob_offsets,
            )?);
        }

        let annotations = decode_class_annotations(
            f,
            cr,
            staged.class_off,
            &entity_map,
            &mut strings,
            &mut str_cache,
            &mut ann_visiting,
        )?;

        let source_file = if sf_off == ABSENT {
            None
        } else {
            str_cache.intern_utf8(sf_off, &mut strings)
        };

        // SAFETY: `cr` is valid.
        let access_flags =
            AccessFlags::from_bits_truncate(unsafe { sys::abc_class_access_flags(cr) });
        // SAFETY: `cr` is valid.
        let super_off = unsafe { sys::abc_class_super_class_off(cr) };
        let super_class = if super_off == 0 || super_off == ABSENT {
            None
        } else {
            entity_map.get(&super_off).copied()
        };
        // SAFETY: `cr` is valid.
        let n_ifaces = unsafe { sys::abc_class_get_ifaces_number(cr) };
        let interfaces = (0..n_ifaces)
            .filter_map(|i| {
                // SAFETY: `cr` is valid and `i < n_ifaces`.
                let off = unsafe { sys::abc_class_get_interface_id(cr, i) };
                entity_map.get(&off).copied()
            })
            .collect();

        classes.insert(
            staged.descriptor,
            Class {
                descriptor: staged.descriptor,
                name,
                access_flags,
                source_lang,
                source_file,
                is_external: staged.is_external,
                super_class,
                interfaces,
                methods,
                fields,
                annotations,
            },
        );
    }

    // Assign dense 0-based `MethodIdx` / `FieldIdx` tables in `classes` BTreeMap order.
    let mut method_offset_to_idx: HashMap<u32, MethodIdx> = HashMap::new();
    for (idx, (_, m)) in classes
        .iter()
        .flat_map(|(&d, c)| c.methods.iter().map(move |m| (d, m)))
        .enumerate()
    {
        if m.offset != 0 {
            method_offset_to_idx
                .entry(m.offset)
                .or_insert(MethodIdx(idx as u32));
        }
    }
    let mut field_offset_to_idx: HashMap<u32, FieldIdx> = HashMap::new();
    for (idx, (_, fl)) in classes
        .iter()
        .flat_map(|(&d, c)| c.fields.iter().map(move |fl| (d, fl)))
        .enumerate()
    {
        if fl.offset != 0 {
            field_offset_to_idx
                .entry(fl.offset)
                .or_insert(FieldIdx(idx as u32));
        }
    }

    // Resolve encoded string/method/literal-array indices while the source file
    // is open. Literal-array operands record `(flat_method_idx, raw_id, offset)`
    // and finalize to `EntityRef::LiteralArray(LiteralArrayIdx)` once
    // `decode_literal_arrays` builds the complete table.
    let mut pending_code_lit_refs: Vec<(usize, u32, u32)> = Vec::new();
    for (flat_idx, method) in classes
        .values_mut()
        .flat_map(|class| &mut class.methods)
        .enumerate()
    {
        let Some(body) = &mut method.body else {
            continue;
        };
        for bytecode in &body.bytecodes {
            let (ops, ops_len) = bytecode.entity_operands_inline();
            for &(kind, id) in &ops[..ops_len] {
                use abcd_isa::EntityKind;
                if !matches!(
                    kind,
                    EntityKind::StringId | EntityKind::MethodId | EntityKind::LiteralarrayId
                ) {
                    continue;
                }
                let invalid = || Error::Malformed {
                    field: "bytecode entity reference",
                    context: format!(
                        "{} in method {:#x}: {:?} index {}",
                        bytecode.mnemonic(),
                        method.offset,
                        kind,
                        id.0
                    ),
                };
                let offset = if legacy {
                    match kind {
                        EntityKind::StringId => {
                            let off = id.0;
                            if off == 0 || off as usize >= data.len() {
                                return Err(invalid());
                            }
                            off
                        }
                        EntityKind::MethodId => {
                            let index = u16::try_from(id.0).map_err(|_| invalid())?;
                            // SAFETY: `f` is a live `AbcFileHandle`.
                            let off = unsafe {
                                sys::abc_resolve_offset_by_index(f, method.offset, index)
                            };
                            if off == ABSENT {
                                return Err(invalid());
                            }
                            off
                        }
                        EntityKind::LiteralarrayId => {
                            let Some((count, table_off)) = legacy_lit_table else {
                                return Err(invalid());
                            };
                            if id.0 >= count {
                                return Err(invalid());
                            }
                            let bytes: [u8; 4] =
                                id.0.checked_mul(4)
                                    .and_then(|n| table_off.checked_add(n))
                                    .and_then(|entry| usize::try_from(entry).ok())
                                    .and_then(|entry| {
                                        entry.checked_add(4).and_then(|end| data.get(entry..end))
                                    })
                                    .and_then(|s| s.try_into().ok())
                                    .ok_or_else(invalid)?;
                            let off = u32::from_le_bytes(bytes);
                            if off == 0 || off as usize >= data.len() {
                                return Err(invalid());
                            }
                            off
                        }
                    }
                } else {
                    let index = u16::try_from(id.0).map_err(|_| invalid())?;
                    // SAFETY: `f` is a live `AbcFileHandle`.
                    let off = unsafe { sys::abc_resolve_offset_by_index(f, method.offset, index) };
                    if off == ABSENT {
                        return Err(invalid());
                    }
                    off
                };

                match kind {
                    EntityKind::LiteralarrayId => {
                        pending_code_lit_refs.push((flat_idx, id.0, offset));
                    }
                    EntityKind::StringId => {
                        let sid = match entity_map.get(&offset).copied() {
                            Some(sid) => sid,
                            None => {
                                let sid = str_cache
                                    .intern_lossy(offset, &mut strings)
                                    .ok_or_else(invalid)?;
                                entity_map.insert(offset, sid);
                                sid
                            }
                        };
                        body.entities
                            .insert((kind, id.0), EntityRef::string_with_offset(sid, offset));
                    }
                    EntityKind::MethodId => {
                        let eref = if let Some(&midx) = method_offset_to_idx.get(&offset) {
                            EntityRef::Method(midx)
                        } else {
                            let name = match entity_map.get(&offset).copied() {
                                Some(sid) => sid,
                                None => {
                                    let sid = {
                                        // SAFETY: `f` is live.
                                        let accessor = unsafe { sys::abc_method_open(f, offset) };
                                        if accessor.is_null() {
                                            return Err(invalid());
                                        }
                                        let _guard = HandleGuard(Some(|| {
                                            // SAFETY: `accessor` is non-null and owned by this scope.
                                            unsafe { sys::abc_method_close(accessor) };
                                        }));
                                        str_cache.intern_method_name(offset, accessor, &mut strings)
                                    }
                                    .ok_or_else(invalid)?;
                                    entity_map.insert(offset, sid);
                                    sid
                                }
                            };
                            EntityRef::ExternalMethod {
                                name,
                                source_offset: offset,
                            }
                        };
                        body.entities.insert((kind, id.0), eref);
                    }
                }
            }
        }
    }

    // Legacy (0.0.0.2): the create*withbuffer family carries the literal
    // array as a plain 16-bit immediate (a global index into the header
    // table), not as a typed id operand, so the entity_operands pass above
    // never sees it. Collect those references here so the literal arrays
    // enter the model exactly like modern ones.
    if legacy {
        for (flat_idx, method) in classes
            .values()
            .flat_map(|class| &class.methods)
            .enumerate()
        {
            let Some(body) = &method.body else {
                continue;
            };
            for bytecode in &body.bytecodes {
                use abcd_isa::Bytecode as B;
                let global_idx = match bytecode {
                    B::DeprecatedCreateobjectwithbuffer(abcd_isa::Imm(i))
                    | B::DeprecatedCreatearraywithbuffer(abcd_isa::Imm(i))
                    | B::DeprecatedCreateobjecthavingmethod(abcd_isa::Imm(i))
                    | B::DeprecatedDefineclasswithbuffer(_, abcd_isa::Imm(i), _, _, _) => *i,
                    _ => continue,
                };
                let invalid = || Error::Malformed {
                    field: "legacy literal-array reference",
                    context: format!(
                        "{} in method {:#x}: global index {global_idx}",
                        bytecode.mnemonic(),
                        method.offset,
                    ),
                };
                let Ok(idx) = u32::try_from(global_idx) else {
                    return Err(invalid());
                };
                let Some((count, table_off)) = legacy_lit_table else {
                    return Err(invalid());
                };
                if idx >= count {
                    return Err(invalid());
                }
                let bytes: [u8; 4] = idx
                    .checked_mul(4)
                    .and_then(|n| table_off.checked_add(n))
                    .and_then(|entry| usize::try_from(entry).ok())
                    .and_then(|entry| entry.checked_add(4).and_then(|end| data.get(entry..end)))
                    .and_then(|s| s.try_into().ok())
                    .ok_or_else(invalid)?;
                let off = u32::from_le_bytes(bytes);
                if off == 0 || off as usize >= data.len() {
                    return Err(invalid());
                }
                pending_code_lit_refs.push((flat_idx, idx, off));
            }
        }
    }

    // --- literal arrays ---
    let mut referenced_literal_offsets: HashSet<u32> = pending_code_lit_refs
        .iter()
        .map(|&(_, _, off)| off)
        .chain(scope_names_offsets.iter().copied())
        .collect();
    collect_annotation_nested_literal_offsets(
        f,
        &classes,
        size,
        &module_data_offsets,
        &phase_blob_offsets,
        &mut referenced_literal_offsets,
    );
    let (literal_arrays, literal_array_offsets, literal_array_header_offsets) =
        decode_literal_arrays(
            f,
            size,
            &mut strings,
            &mut str_cache,
            &referenced_literal_offsets,
            &module_data_offsets,
            &phase_blob_offsets,
            &method_offset_to_idx,
        )?;

    // Finalize bytecode literal-array operands, field `LiteralArrayRef`s, and
    // annotation method/field/literal-array indices.
    {
        let mut methods_mut: Vec<&mut Method> = classes
            .values_mut()
            .flat_map(|c| c.methods.iter_mut())
            .collect();
        for (flat_idx, raw_id, off) in pending_code_lit_refs {
            let table_idx = literal_array_offsets.get(&off).copied().unwrap_or(ABSENT);
            if let Some(body) = methods_mut[flat_idx].body.as_mut() {
                body.entities.insert(
                    (abcd_isa::EntityKind::LiteralarrayId, raw_id),
                    EntityRef::LiteralArray(LiteralArrayIdx(table_idx)),
                );
            }
        }
    }
    for class in classes.values_mut() {
        for field in &mut class.fields {
            if let Some(FieldValue::LiteralArrayRef {
                index,
                source_offset: Some(off),
            }) = &mut field.initial_value
            {
                let table_idx = literal_array_offsets.get(off).copied().unwrap_or(ABSENT);
                *index = LiteralArrayIdx(table_idx);
            }
        }
    }
    rewrite_annotation_refs(
        &mut classes,
        &literal_array_offsets,
        literal_arrays.len(),
        &literal_array_header_offsets,
        &method_offset_to_idx,
        &field_offset_to_idx,
    );

    Ok(File {
        version,
        checksum,
        size,
        file_type,
        strings,
        classes,
        literal_arrays,
        literal_array_header_offsets,
    })
}

// ---------------------------------------------------------------------------
// Lightweight streaming summary & verifier (`inspect_summary`)
// ---------------------------------------------------------------------------

/// Bytecode verification counts produced by [`inspect_summary`] when `verify`
/// is `true`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifySummary {
    pub methods_checked: usize,
    pub instructions_decoded: usize,
}

/// Lightweight header and entity summary of an `.abc` file produced by
/// [`inspect_summary`] without materializing an owned [`File`] in memory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileSummary {
    pub version: crate::Version,
    pub checksum: u32,
    pub size: u32,
    pub file_type: crate::FileType,
    pub strings: usize,
    pub lossy_strings: usize,
    pub classes: usize,
    pub external_classes: usize,
    pub methods: usize,
    pub methods_with_body: usize,
    pub fields: usize,
    pub literal_arrays: usize,
    pub entity_index_entries: usize,
    pub debug_infos: usize,
    pub verify: Option<VerifySummary>,
}

impl FileSummary {
    /// Classify this `.abc` summary into its container [`Dialect`].
    #[inline]
    pub const fn dialect(&self) -> Option<crate::Dialect> {
        crate::Dialect::from_header(self.file_type, self.version)
    }
}

/// Compact open-addressed `u32` hash set using `u32::MAX` as the empty slot
/// sentinel (with an explicit side flag for `u32::MAX` itself). Avoids std
/// `HashSet` per-bucket metadata overhead when tracking ~100k file offsets.
#[derive(Default)]
struct CompactU32Set {
    slots: Vec<u32>,
    len: usize,
    has_max: bool,
}

impl CompactU32Set {
    #[inline]
    fn mix(mut x: u32) -> usize {
        x ^= x >> 16;
        x = x.wrapping_mul(0x7feb_352d);
        x ^= x >> 15;
        x = x.wrapping_mul(0x846c_a68b);
        x ^= x >> 16;
        x as usize
    }

    #[inline]
    fn len(&self) -> usize {
        self.len + usize::from(self.has_max)
    }

    fn iter(&self) -> impl Iterator<Item = u32> {
        self.slots
            .iter()
            .copied()
            .filter(|&v| v != u32::MAX)
            .chain(self.has_max.then_some(u32::MAX))
    }

    #[inline]
    fn contains(&self, v: u32) -> bool {
        if v == u32::MAX {
            return self.has_max;
        }
        if self.slots.is_empty() {
            return false;
        }
        let mask = self.slots.len() - 1;
        let mut idx = Self::mix(v) & mask;
        loop {
            let cur = self.slots[idx];
            if cur == v {
                return true;
            }
            if cur == u32::MAX {
                return false;
            }
            idx = (idx + 1) & mask;
        }
    }

    fn insert(&mut self, v: u32) -> bool {
        if v == u32::MAX {
            let added = !self.has_max;
            self.has_max = true;
            return added;
        }
        if (self.len + 1) * 10 >= self.slots.len() * 7 {
            let new_cap = if self.slots.is_empty() {
                64
            } else {
                self.slots.len() * 2
            };
            self.rehash(new_cap);
        }
        let mask = self.slots.len() - 1;
        let mut idx = Self::mix(v) & mask;
        loop {
            let cur = self.slots[idx];
            if cur == v {
                return false;
            }
            if cur == u32::MAX {
                self.slots[idx] = v;
                self.len += 1;
                return true;
            }
            idx = (idx + 1) & mask;
        }
    }

    fn rehash(&mut self, new_cap: usize) {
        let old = std::mem::replace(&mut self.slots, vec![u32::MAX; new_cap]);
        let mask = new_cap - 1;
        for v in old {
            if v == u32::MAX {
                continue;
            }
            let mut idx = Self::mix(v) & mask;
            while self.slots[idx] != u32::MAX {
                idx = (idx + 1) & mask;
            }
            self.slots[idx] = v;
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum SymId {
    Utf8(u32),
    Lossy(u32),
}

/// Zero-copy / flat-arena string deduplicator matching [`StringPool`] set
/// cardinalities (`len` and `lossy_count`) without allocating per-string heap
/// boxes for in-file ASCII strings.
struct SummaryStrings<'a> {
    data: &'a [u8],
    arena: Vec<u8>,
    /// `(tagged_start, byte_len)`: high bit `0x8000_0000` selects `arena`,
    /// otherwise `data`.
    utf8_spans: Vec<(u32, u32)>,
    utf8_buckets: Vec<u32>,
    raw_lossy: HashMap<Box<[u8]>, u32>,
    seen_lossy_offsets: CompactU32Set,
    seen_utf8_offsets: CompactU32Set,
    utf16_scratch: Vec<u16>,
    ascii_scratch: Vec<u8>,
}

impl<'a> SummaryStrings<'a> {
    const ARENA_TAG: u32 = 0x8000_0000;

    fn new(data: &'a [u8]) -> Self {
        Self {
            data,
            arena: Vec::new(),
            utf8_spans: Vec::new(),
            utf8_buckets: Vec::new(),
            raw_lossy: HashMap::new(),
            seen_lossy_offsets: CompactU32Set::default(),
            seen_utf8_offsets: CompactU32Set::default(),
            utf16_scratch: Vec::new(),
            ascii_scratch: Vec::new(),
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.utf8_spans.len() + self.raw_lossy.len()
    }

    #[inline]
    fn lossy_count(&self) -> usize {
        self.raw_lossy.len()
    }

    #[inline]
    fn hash_bytes(bytes: &[u8]) -> usize {
        // Deterministic 64-bit FNV-1a + finalizer mix.
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        for &b in bytes {
            h ^= u64::from(b);
            h = h.wrapping_mul(0x0100_0000_01b3);
        }
        h ^= h >> 33;
        h = h.wrapping_mul(0xff51_afd7_ed55_8ccd);
        h ^= h >> 33;
        h as usize
    }

    #[inline]
    fn span_bytes<'s>(data: &'s [u8], arena: &'s [u8], (tagged, len): (u32, u32)) -> &'s [u8] {
        let len = len as usize;
        if tagged & Self::ARENA_TAG != 0 {
            let start = (tagged & !Self::ARENA_TAG) as usize;
            &arena[start..start + len]
        } else {
            let start = tagged as usize;
            &data[start..start + len]
        }
    }

    fn resolve_utf8(&self, sym: SymId) -> Option<&str> {
        match sym {
            SymId::Utf8(idx) => {
                let span = *self.utf8_spans.get(idx as usize)?;
                std::str::from_utf8(Self::span_bytes(self.data, &self.arena, span)).ok()
            }
            SymId::Lossy(_) => None,
        }
    }

    fn ensure_utf8_capacity(&mut self) {
        if (self.utf8_spans.len() + 1) * 10 < self.utf8_buckets.len() * 7 {
            return;
        }
        let new_cap = if self.utf8_buckets.is_empty() {
            128
        } else {
            self.utf8_buckets.len() * 2
        };
        self.utf8_buckets.clear();
        self.utf8_buckets.resize(new_cap, u32::MAX);
        let mask = new_cap - 1;
        for (id, &span) in self.utf8_spans.iter().enumerate() {
            let bytes = Self::span_bytes(self.data, &self.arena, span);
            let mut bkt = Self::hash_bytes(bytes) & mask;
            while self.utf8_buckets[bkt] != u32::MAX {
                bkt = (bkt + 1) & mask;
            }
            self.utf8_buckets[bkt] = id as u32;
        }
    }

    fn intern_in_place_utf8(&mut self, start: usize, len: usize) -> SymId {
        if start >= Self::ARENA_TAG as usize {
            let s = &self.data[start..start + len];
            return self.intern_utf8_bytes_copy(s);
        }
        self.ensure_utf8_capacity();
        let candidate = &self.data[start..start + len];
        let mask = self.utf8_buckets.len() - 1;
        let mut bkt = Self::hash_bytes(candidate) & mask;
        loop {
            let cur = self.utf8_buckets[bkt];
            if cur == u32::MAX {
                let id = self.utf8_spans.len() as u32;
                self.utf8_spans.push((start as u32, len as u32));
                self.utf8_buckets[bkt] = id;
                return SymId::Utf8(id);
            }
            let existing = Self::span_bytes(self.data, &self.arena, self.utf8_spans[cur as usize]);
            if existing == candidate {
                return SymId::Utf8(cur);
            }
            bkt = (bkt + 1) & mask;
        }
    }

    fn intern_utf8_bytes_copy(&mut self, candidate: &[u8]) -> SymId {
        self.ensure_utf8_capacity();
        let mask = self.utf8_buckets.len() - 1;
        let mut bkt = Self::hash_bytes(candidate) & mask;
        loop {
            let cur = self.utf8_buckets[bkt];
            if cur == u32::MAX {
                let arena_off = self.arena.len() as u32;
                self.arena.extend_from_slice(candidate);
                let id = self.utf8_spans.len() as u32;
                self.utf8_spans
                    .push((Self::ARENA_TAG | arena_off, candidate.len() as u32));
                self.utf8_buckets[bkt] = id;
                return SymId::Utf8(id);
            }
            let existing = Self::span_bytes(self.data, &self.arena, self.utf8_spans[cur as usize]);
            if existing == candidate {
                return SymId::Utf8(cur);
            }
            bkt = (bkt + 1) & mask;
        }
    }

    #[inline]
    fn intern_utf8_str(&mut self, s: &str) -> SymId {
        self.intern_utf8_bytes_copy(s.as_bytes())
    }

    fn intern_lossy_raw(&mut self, raw: &[u8]) -> SymId {
        if let Some(&idx) = self.raw_lossy.get(raw) {
            return SymId::Lossy(idx);
        }
        let idx = self.raw_lossy.len() as u32;
        self.raw_lossy.insert(raw.into(), idx);
        SymId::Lossy(idx)
    }

    /// Fast validated in-place ASCII item check matching `GetStringData` +
    /// `convert_string_utf16_bounded`: `offset > sizeof(Header)` (`60`), valid
    /// ULEB128 tag, `utf16_len` bytes in `0x01..=0x7F` (or empty), followed
    /// immediately by a `0x00` NUL byte inside `self.data`.
    #[inline]
    fn try_ascii_span(&self, offset: u32) -> Option<(usize, usize)> {
        if offset <= 60 {
            return None;
        }
        let mut sp = self.data.get(offset as usize..)?;
        let header_before = sp.len();
        let tag_len = read_uleb128_slice(&mut sp)?;
        let prefix_len = header_before - sp.len();
        let utf16_len = (tag_len >> 1) as usize;
        if sp.len() <= utf16_len || sp[utf16_len] != 0 {
            return None;
        }
        let payload = &sp[..utf16_len];
        if !payload.iter().all(|&b| (1..=0x7F).contains(&b)) {
            return None;
        }
        Some((offset as usize + prefix_len, utf16_len))
    }

    /// Equivalent to [`crate::file::intern_string`] (lossless UTF-8 or raw
    /// MUTF-8 bucket), returning the interned [`SymId`].
    fn intern_offset_lossy_sym(
        &mut self,
        f: *const sys::AbcFileHandle,
        offset: u32,
    ) -> Option<SymId> {
        if let Some((start, len)) = self.try_ascii_span(offset) {
            self.seen_lossy_offsets.insert(offset);
            return Some(self.intern_in_place_utf8(start, len));
        }
        let (text, lossy) = crate::file::read_string_reporting_lossy(f, offset)?;
        self.seen_lossy_offsets.insert(offset);
        if !lossy {
            return Some(self.intern_utf8_str(&text));
        }
        match crate::file::read_string_raw_bytes(f, offset) {
            Some(raw) => Some(self.intern_lossy_raw(&raw)),
            None => Some(self.intern_utf8_str(&text)),
        }
    }

    /// Equivalent to [`crate::file::intern_string`] when the caller only needs
    /// validity (`bool`), skipping repeat offsets in O(1).
    fn intern_offset_lossy(&mut self, f: *const sys::AbcFileHandle, offset: u32) -> bool {
        if self.seen_lossy_offsets.contains(offset) {
            return true;
        }
        self.intern_offset_lossy_sym(f, offset).is_some()
    }

    /// Equivalent to `read_string(f, offset).map(|s| strings.get_or_intern(&s))`,
    /// returning the interned [`SymId`].
    fn intern_offset_utf8_sym(
        &mut self,
        f: *const sys::AbcFileHandle,
        offset: u32,
    ) -> Option<SymId> {
        if let Some((start, len)) = self.try_ascii_span(offset) {
            self.seen_utf8_offsets.insert(offset);
            return Some(self.intern_in_place_utf8(start, len));
        }
        let text = read_string(f, offset)?;
        self.seen_utf8_offsets.insert(offset);
        Some(self.intern_utf8_str(&text))
    }

    /// Equivalent to `read_string(f, offset).map(|s| strings.get_or_intern(&s)).is_some()`,
    /// skipping repeat offsets in O(1).
    fn intern_offset_utf8(&mut self, f: *const sys::AbcFileHandle, offset: u32) -> bool {
        if self.seen_utf8_offsets.contains(offset) {
            return true;
        }
        self.intern_offset_utf8_sym(f, offset).is_some()
    }

    /// Equivalent to `read_method_name(mr)` + `strings.get_or_intern`, reusing
    /// one scratch UTF-16 buffer across methods.
    fn intern_method_name(&mut self, mr: *const sys::AbcMethodAccessor) -> bool {
        // SAFETY: `mr` is a valid `AbcMethodAccessor`; null buffer queries unit count.
        let units = unsafe { sys::abc_method_get_name_utf16(mr, std::ptr::null_mut(), 0) };
        if units == 0 {
            return false;
        }
        self.utf16_scratch.clear();
        self.utf16_scratch.resize(units, 0);
        // SAFETY: `mr` is valid and `utf16_scratch` holds `units` writable `u16`s.
        let written =
            unsafe { sys::abc_method_get_name_utf16(mr, self.utf16_scratch.as_mut_ptr(), units) };
        if written != units {
            return false;
        }
        if self.utf16_scratch.iter().all(|&u| u < 0x80) {
            let mut ascii = std::mem::take(&mut self.ascii_scratch);
            ascii.clear();
            ascii.extend(self.utf16_scratch.iter().map(|&u| u as u8));
            self.intern_utf8_bytes_copy(&ascii);
            self.ascii_scratch = ascii;
            return true;
        }
        let Ok(s) = String::from_utf16(&self.utf16_scratch) else {
            return false;
        };
        self.intern_utf8_str(&s);
        true
    }
}

use crate::file::read_uleb128_slice;

#[derive(Default)]
struct ClassSummary {
    is_external: bool,
    methods: usize,
    methods_with_body: usize,
    fields: usize,
    debug_infos: usize,
    instructions_decoded: usize,
}

/// Inspect an `.abc` file and return header metadata and entity counts matching
/// [`decode`] with minimal peak memory:
///
/// - When `verify == false`, opens the header and walks classes, methods,
///   fields, annotations, debug items, and transitive literal arrays **without**
///   invoking `abc_debug_info_open` (which eagerly materializes every method's
///   line/column/local-var tables in C++) and **without** retaining
///   `Vec<MethodBody>` in RAM.
/// - When `verify == true`, additionally runs `abc_debug_info_open` and full
///   try-block / jump-target verification per method while streaming one method
///   at a time, returning [`VerifySummary`].
pub fn inspect_summary(data: &[u8], verify: bool) -> Result<FileSummary, Error> {
    use crate::file::AbcFile;

    let abc = AbcFile::open(data)?;
    inspect_summary_with_handle(abc, data, verify)
}

/// Zero-copy counterpart to [`inspect_summary`] over a caller-owned slice
/// carrying `16` trailing zero padding bytes (`logical_data =
/// &padded_data[..padded_data.len() - 16]`).
///
/// Rejects buffers shorter than `16` bytes, buffers whose `16` trailing bytes
/// are not all zero, and malformed `.abc` headers.
pub fn inspect_summary_zeropadded(padded_data: &[u8], verify: bool) -> Result<FileSummary, Error> {
    use crate::file::AbcFile;

    const ZERO_PADDING: usize = 16;
    let Some(logical_len) = padded_data.len().checked_sub(ZERO_PADDING) else {
        return Err(Error::Open(
            "buffer too small for file header and zero padding".into(),
        ));
    };
    if padded_data[logical_len..].iter().any(|&b| b != 0) {
        return Err(Error::Open(
            "missing required 16-byte trailing zero padding".into(),
        ));
    }
    let logical_data = &padded_data[..logical_len];
    let abc = AbcFile::open_zeropadded(padded_data)?;
    inspect_summary_with_handle(abc, logical_data, verify)
}

fn inspect_summary_with_handle(
    abc: crate::file::AbcFile<'_>,
    data: &[u8],
    verify: bool,
) -> Result<FileSummary, Error> {
    let f = abc.raw;
    let version = abc.version();
    let file_type = crate::file::file_type(data);
    let dialect = if verify {
        check_supported_dialect(file_type, version)?
    } else if version == abcd_isa::Version::new(0, 1, 0, 7) || file_type == sys::FileType::Static {
        Dialect::Static
    } else if version == Dialect::LEGACY_VERSION {
        Dialect::DynamicLegacy
    } else {
        Dialect::DynamicModern
    };
    let legacy = dialect == Dialect::DynamicLegacy;
    let legacy_lit_table = if legacy {
        legacy_literalarray_table(data)
    } else {
        None
    };
    let checksum = abc.checksum();
    let size = abc.size();
    let file_bytes = data
        .get(..size as usize)
        .ok_or_else(|| Error::Open("declared file_size exceeds buffer".into()))?;

    let mut strings = SummaryStrings::new(file_bytes);

    // Pass 1: initial entity_map offsets (classes, methods, fields).
    let mut initial_entities = CompactU32Set::default();
    let mut valid_method_names = CompactU32Set::default();
    // SAFETY: `f` is a live `AbcFileHandle`.
    let num_classes = unsafe { sys::abc_file_num_classes(f) };
    for i in 0..num_classes {
        // SAFETY: `f` is a live `AbcFileHandle`.
        let class_off = unsafe { sys::abc_file_class_offset(f, i) };
        if class_off == ABSENT {
            return Err(Error::InvalidOffset(class_off));
        }
        if is_external(f, class_off) {
            if strings.intern_offset_lossy(f, class_off) {
                initial_entities.insert(class_off);
            }
            continue;
        }
        // SAFETY: `f` is live and `class_off` is non-external.
        let cr = unsafe { sys::abc_class_open(f, class_off) };
        if cr.is_null() {
            return Err(Error::InvalidOffset(class_off));
        }
        let _cg = HandleGuard(Some(|| {
            // SAFETY: `cr` is non-null and owned by this scope.
            unsafe { sys::abc_class_close(cr) };
        }));

        if read_class_descriptor_summary(f, cr, &mut strings).is_some() {
            // SAFETY: `cr` is valid.
            initial_entities.insert(unsafe { sys::abc_class_get_class_id(cr) });
        }
        for off in collect_offsets_void(
            cr,
            sys::abc_class_enumerate_methods,
            "class_methods",
            class_off,
        )? {
            // SAFETY: `f` is live.
            let mr = unsafe { sys::abc_method_open(f, off) };
            if mr.is_null() {
                continue;
            }
            let _mg = HandleGuard(Some(|| {
                // SAFETY: `mr` is non-null and owned by this scope.
                unsafe { sys::abc_method_close(mr) };
            }));
            if strings.intern_method_name(mr) {
                valid_method_names.insert(off);
                // SAFETY: `mr` is valid.
                initial_entities.insert(unsafe { sys::abc_method_get_method_id(mr) });
            }
        }
        for off in collect_offsets_void(
            cr,
            sys::abc_class_enumerate_fields,
            "class_fields",
            class_off,
        )? {
            // SAFETY: `f` is live.
            let fr = unsafe { sys::abc_field_open(f, off) };
            if fr.is_null() {
                continue;
            }
            let _fg = HandleGuard(Some(|| {
                // SAFETY: `fr` is non-null and owned by this scope.
                unsafe { sys::abc_field_close(fr) };
            }));
            // SAFETY: `fr` is valid.
            let name_off = unsafe { sys::abc_field_name_off(fr) };
            if name_off != ABSENT && strings.intern_offset_lossy(f, name_off) {
                // SAFETY: `fr` is valid.
                initial_entities.insert(unsafe { sys::abc_field_get_field_id(fr) });
            }
        }
    }

    // Pass 2: stream classes, methods, fields, and annotations without
    // retaining MethodBody / Field / Annotation vectors.
    let mut classes: BTreeMap<SymId, ClassSummary> = BTreeMap::new();
    let mut extra_entities = CompactU32Set::default();
    let mut module_data_offsets = CompactU32Set::default();
    let mut scope_names_offsets = CompactU32Set::default();
    let mut phase_blob_offsets = CompactU32Set::default();
    let mut referenced_literal_offsets = CompactU32Set::default();
    let mut ann_nested_raw_targets: Vec<u32> = Vec::new();
    let mut ann_visiting: HashSet<u32> = HashSet::new();

    for i in 0..num_classes {
        // SAFETY: `f` is live.
        let class_off = unsafe { sys::abc_file_class_offset(f, i) };
        if class_off == ABSENT {
            return Err(Error::InvalidOffset(class_off));
        }
        if is_external(f, class_off) {
            if let Some(desc_sym) = strings.intern_offset_lossy_sym(f, class_off) {
                if classes.contains_key(&desc_sym) {
                    let dup = strings.resolve_utf8(desc_sym).unwrap_or("?").to_owned();
                    return Err(Error::Malformed {
                        field: "class",
                        context: format!("duplicate class descriptor {dup:?}"),
                    });
                }
                classes.insert(
                    desc_sym,
                    ClassSummary {
                        is_external: true,
                        ..ClassSummary::default()
                    },
                );
            }
            continue;
        }
        // SAFETY: `f` is live and `class_off` is non-external.
        let cr = unsafe { sys::abc_class_open(f, class_off) };
        if cr.is_null() {
            return Err(Error::InvalidOffset(class_off));
        }
        let _cg = HandleGuard(Some(|| {
            // SAFETY: `cr` is non-null and owned by this scope.
            unsafe { sys::abc_class_close(cr) };
        }));

        let Some(desc_sym) = read_class_descriptor_summary(f, cr, &mut strings) else {
            continue;
        };
        if classes.contains_key(&desc_sym) {
            let dup = strings.resolve_utf8(desc_sym).unwrap_or("?").to_owned();
            return Err(Error::Malformed {
                field: "class",
                context: format!("duplicate class descriptor {dup:?}"),
            });
        }
        // SAFETY: `cr` is valid.
        let class_id = unsafe { sys::abc_class_get_class_id(cr) };
        if !strings.intern_offset_utf8(f, class_id) {
            let desc_text = strings.resolve_utf8(desc_sym).unwrap_or("?").to_owned();
            return Err(Error::Malformed {
                field: "name",
                context: format!("class {desc_text}"),
            });
        }
        // SAFETY: `cr` is valid.
        decode_source_lang(unsafe { sys::abc_class_get_source_lang(cr) })?;
        let is_mod_rec_cls = strings.resolve_utf8(desc_sym) == Some(ES_MODULE_RECORD_DESCRIPTOR);
        let is_scope_rec_cls =
            strings.resolve_utf8(desc_sym) == Some(ES_SCOPE_NAMES_RECORD_DESCRIPTOR);

        // SAFETY: `cr` is valid.
        let sf_off = unsafe { sys::abc_class_source_file_off(cr) };

        let mut cls_summary = ClassSummary {
            is_external: is_external(f, class_id),
            ..ClassSummary::default()
        };

        for method_off in collect_offsets_void(
            cr,
            sys::abc_class_enumerate_methods,
            "class_methods",
            class_off,
        )? {
            inspect_method_at(
                f,
                data,
                file_bytes,
                method_off,
                class_id,
                sf_off,
                dialect,
                legacy_lit_table,
                &valid_method_names,
                &initial_entities,
                &mut extra_entities,
                &mut strings,
                &mut referenced_literal_offsets,
                &mut ann_nested_raw_targets,
                &mut ann_visiting,
                &mut cls_summary,
            )?;
        }

        for field_off in collect_offsets_void(
            cr,
            sys::abc_class_enumerate_fields,
            "class_fields",
            class_off,
        )? {
            inspect_field_at(
                f,
                file_bytes,
                field_off,
                desc_sym,
                is_mod_rec_cls,
                is_scope_rec_cls,
                &initial_entities,
                &mut strings,
                &mut module_data_offsets,
                &mut scope_names_offsets,
                &mut phase_blob_offsets,
                &mut ann_nested_raw_targets,
                &mut ann_visiting,
            )?;
            cls_summary.fields += 1;
        }

        for enumerate in [
            sys::abc_class_enumerate_annotations,
            sys::abc_class_enumerate_runtime_annotations,
            sys::abc_class_enumerate_type_annotations,
            sys::abc_class_enumerate_runtime_type_annotations,
        ] {
            for ann_off in collect_offsets_int(cr, enumerate, "class_annotations", class_off)? {
                inspect_annotation_at(
                    f,
                    ann_off,
                    &initial_entities,
                    &mut strings,
                    &mut ann_nested_raw_targets,
                    &mut ann_visiting,
                )?;
            }
        }

        if sf_off != ABSENT {
            let _ = strings.intern_offset_utf8(f, sf_off);
        }

        classes.insert(desc_sym, cls_summary);
    }

    // Seed scope-names and plausible annotation-embedded nested literal arrays.
    for off in scope_names_offsets.iter() {
        referenced_literal_offsets.insert(off);
    }
    for target in ann_nested_raw_targets {
        if is_plausible_literal_array_offset(
            target,
            size,
            &module_data_offsets,
            &phase_blob_offsets,
        ) {
            referenced_literal_offsets.insert(target);
        }
    }

    let literal_arrays = count_literal_arrays_summary(
        f,
        size,
        &mut strings,
        &referenced_literal_offsets,
        &module_data_offsets,
        &phase_blob_offsets,
    )?;

    drop(abc);

    let total_classes = classes.len();
    let mut external_classes = 0usize;
    let mut methods = 0usize;
    let mut methods_with_body = 0usize;
    let mut fields = 0usize;
    let mut debug_infos = 0usize;
    let mut instructions_decoded = 0usize;
    for c in classes.values() {
        if c.is_external {
            external_classes += 1;
        }
        methods += c.methods;
        methods_with_body += c.methods_with_body;
        fields += c.fields;
        debug_infos += c.debug_infos;
        instructions_decoded += c.instructions_decoded;
    }

    Ok(FileSummary {
        version,
        checksum,
        size,
        file_type,
        strings: strings.len(),
        lossy_strings: strings.lossy_count(),
        classes: total_classes,
        external_classes,
        methods,
        methods_with_body,
        fields,
        literal_arrays,
        entity_index_entries: initial_entities.len() + extra_entities.len(),
        debug_infos,
        verify: verify.then_some(VerifySummary {
            methods_checked: methods_with_body,
            instructions_decoded,
        }),
    })
}

fn read_class_descriptor_summary(
    f: *const sys::AbcFileHandle,
    cr: *const sys::AbcClassAccessor,
    strings: &mut SummaryStrings<'_>,
) -> Option<SymId> {
    // SAFETY: `cr` is a valid `AbcClassAccessor`.
    let class_id = unsafe { sys::abc_class_get_class_id(cr) };
    if let Some(sym) = strings.intern_offset_utf8_sym(f, class_id) {
        return Some(sym);
    }
    // SAFETY: `cr` is valid; returns null or a NUL-terminated descriptor inside `f`'s buffer.
    let ptr = unsafe { sys::abc_class_get_descriptor(cr) };
    if ptr.is_null() {
        return None;
    }
    // SAFETY: `ptr` is non-null and NUL-terminated inside `f`'s zero-padded buffer.
    let cstr = unsafe { CStr::from_ptr(ptr.cast::<std::os::raw::c_char>()) };
    Some(strings.intern_utf8_str(&cstr.to_string_lossy()))
}

#[expect(
    clippy::too_many_arguments,
    reason = "streaming method inspector threads distinct summary accumulators without intermediate allocations"
)]
fn inspect_method_at(
    f: *const sys::AbcFileHandle,
    raw_data: &[u8],
    file_bytes: &[u8],
    method_off: u32,
    class_id: u32,
    class_source_file_off: u32,
    dialect: Dialect,
    legacy_lit_table: Option<(u32, u32)>,
    valid_method_names: &CompactU32Set,
    initial_entities: &CompactU32Set,
    extra_entities: &mut CompactU32Set,
    strings: &mut SummaryStrings<'_>,
    referenced_literal_offsets: &mut CompactU32Set,
    ann_nested_raw_targets: &mut Vec<u32>,
    ann_visiting: &mut HashSet<u32>,
    cls_summary: &mut ClassSummary,
) -> Result<(), Error> {
    // SAFETY: `f` is a live `AbcFileHandle`.
    let mr = unsafe { sys::abc_method_open(f, method_off) };
    if mr.is_null() {
        return Err(Error::InvalidOffset(method_off));
    }
    let _mg = HandleGuard(Some(|| {
        // SAFETY: `mr` is non-null and owned by this scope.
        unsafe { sys::abc_method_close(mr) };
    }));

    // SAFETY: `mr` is valid.
    let method_id = unsafe { sys::abc_method_get_method_id(mr) };
    if !valid_method_names.contains(method_off) && !strings.intern_method_name(mr) {
        return Err(Error::Malformed {
            field: "name",
            context: format!("method at offset {method_id:#x}"),
        });
    }

    // SAFETY: `mr` is valid.
    let raw_flags = unsafe { sys::abc_method_access_flags(mr) };
    if dialect != Dialect::Static {
        decode_function_kind_from_flags(raw_flags)?;
    }
    // SAFETY: `mr` is valid.
    decode_source_lang(unsafe { sys::abc_method_get_source_lang(mr) })?;

    // SAFETY: `mr` is valid.
    let code_off = unsafe { sys::abc_method_code_off(mr) };
    let mut code_size = 0u32;
    if code_off != ABSENT {
        cls_summary.methods_with_body += 1;
        if dialect != Dialect::Static {
            let (insns, csize) = inspect_code_at(
                f,
                raw_data,
                method_off,
                code_off,
                dialect,
                legacy_lit_table,
                initial_entities,
                extra_entities,
                strings,
                referenced_literal_offsets,
            )?;
            cls_summary.instructions_decoded += insns;
            code_size = csize;
        }
    }

    let num_params = {
        // SAFETY: `mr` is valid.
        let has_valid = unsafe { sys::abc_method_has_valid_proto(mr) } != 0;
        if !has_valid {
            0usize
        } else {
            // SAFETY: `mr` is valid.
            let proto_id = unsafe { sys::abc_method_get_proto_id(mr) };
            if proto_id == ABSENT {
                0usize
            } else {
                inspect_proto_types(f, proto_id, initial_entities)?
            }
        }
    };

    for enumerate in [
        sys::abc_method_enumerate_annotations,
        sys::abc_method_enumerate_runtime_annotations,
        sys::abc_method_enumerate_type_annotations,
        sys::abc_method_enumerate_runtime_type_annotations,
    ] {
        for ann_off in collect_offsets_int(mr, enumerate, "method_annotations", method_off)? {
            inspect_annotation_at(
                f,
                ann_off,
                initial_entities,
                strings,
                ann_nested_raw_targets,
                ann_visiting,
            )?;
        }
    }

    // SAFETY: `mr` is valid.
    let debug_off = unsafe { sys::abc_method_debug_info_off(mr) };
    if debug_off != ABSENT {
        cls_summary.debug_infos += 1;
        let mut sink = SummaryDebugSink::new(strings);
        decode_method_debug_item(
            f,
            file_bytes,
            class_id,
            class_source_file_off,
            mr,
            code_size,
            debug_off,
            &mut sink,
        )?;
    }

    inspect_param_annotations(
        f,
        mr,
        num_params,
        initial_entities,
        strings,
        ann_nested_raw_targets,
        ann_visiting,
    )?;

    cls_summary.methods += 1;
    Ok(())
}

#[expect(
    clippy::too_many_arguments,
    reason = "streaming code inspector resolves operands directly into summary sets without allocating MethodBody"
)]
fn inspect_code_at(
    f: *const sys::AbcFileHandle,
    data: &[u8],
    method_off: u32,
    code_off: u32,
    dialect: Dialect,
    legacy_lit_table: Option<(u32, u32)>,
    initial_entities: &CompactU32Set,
    extra_entities: &mut CompactU32Set,
    strings: &mut SummaryStrings<'_>,
    referenced_literal_offsets: &mut CompactU32Set,
) -> Result<(usize, u32), Error> {
    let legacy = dialect == Dialect::DynamicLegacy;
    // SAFETY: `f` is a live `AbcFileHandle`.
    let cr = unsafe { sys::abc_code_open(f, code_off) };
    if cr.is_null() {
        return Err(Error::InvalidOffset(code_off));
    }
    let _cg = HandleGuard(Some(|| {
        // SAFETY: `cr` is non-null and owned by this scope.
        unsafe { sys::abc_code_close(cr) };
    }));

    let raw_insns = {
        // SAFETY: `cr` is valid.
        let ptr = unsafe { sys::abc_code_instructions(cr) };
        // SAFETY: `cr` is valid.
        let len = unsafe { sys::abc_code_code_size(cr) } as usize;
        if ptr.is_null() || len == 0 {
            &[]
        } else {
            // SAFETY: `ptr` points to `len` validated bytes inside `f`'s buffer.
            unsafe { std::slice::from_raw_parts(ptr, len) }
        }
    };
    let decoded = match dialect {
        Dialect::DynamicLegacy => abcd_isa::decode_legacy(raw_insns),
        Dialect::DynamicModern => abcd_isa::decode(raw_insns),
        Dialect::Static => {
            return Err(Error::Malformed {
                field: "file_type",
                context: "static .abc bytecode cannot be decoded with dynamic ISA".into(),
            });
        }
    }
    .map_err(|source| Error::BytecodeDecode {
        method_offset: method_off,
        source,
    })?;

    // Validate try-block and catch-block spans and catch class indices.
    validate_try_block_spans(f, method_off, cr, raw_insns.len() as u32, &decoded)?;

    let insn_count = decoded.len();
    for (bytecode, _) in &decoded {
        let (ops, ops_len) = bytecode.entity_operands_inline();
        for &(kind, id) in &ops[..ops_len] {
            use abcd_isa::EntityKind;
            if !matches!(
                kind,
                EntityKind::StringId | EntityKind::MethodId | EntityKind::LiteralarrayId
            ) {
                continue;
            }
            let invalid = || Error::Malformed {
                field: "bytecode entity reference",
                context: format!(
                    "{} in method {:#x}: {:?} index {}",
                    bytecode.mnemonic(),
                    method_off,
                    kind,
                    id.0
                ),
            };
            if legacy {
                let offset = match kind {
                    EntityKind::StringId => {
                        let off = id.0;
                        if off == 0 || off as usize >= data.len() {
                            return Err(invalid());
                        }
                        off
                    }
                    EntityKind::MethodId => {
                        let index = u16::try_from(id.0).map_err(|_| invalid())?;
                        // SAFETY: `f` is live.
                        let offset =
                            unsafe { sys::abc_resolve_offset_by_index(f, method_off, index) };
                        if offset == ABSENT {
                            return Err(invalid());
                        }
                        offset
                    }
                    EntityKind::LiteralarrayId => {
                        let Some((count, table_off)) = legacy_lit_table else {
                            return Err(invalid());
                        };
                        if id.0 >= count {
                            return Err(invalid());
                        }
                        let bytes: [u8; 4] =
                            id.0.checked_mul(4)
                                .and_then(|n| table_off.checked_add(n))
                                .and_then(|entry| usize::try_from(entry).ok())
                                .and_then(|entry| {
                                    entry.checked_add(4).and_then(|end| data.get(entry..end))
                                })
                                .and_then(|s| s.try_into().ok())
                                .ok_or_else(invalid)?;
                        let off = u32::from_le_bytes(bytes);
                        if off == 0 || off as usize >= data.len() {
                            return Err(invalid());
                        }
                        off
                    }
                };
                if kind == EntityKind::LiteralarrayId {
                    referenced_literal_offsets.insert(offset);
                    continue;
                }
                if initial_entities.contains(offset) || extra_entities.contains(offset) {
                    continue;
                }
                if kind == EntityKind::StringId {
                    if !strings.intern_offset_lossy(f, offset) {
                        return Err(invalid());
                    }
                    extra_entities.insert(offset);
                    continue;
                }
                // SAFETY: `f` is live.
                let accessor = unsafe { sys::abc_method_open(f, offset) };
                if accessor.is_null() {
                    return Err(invalid());
                }
                let _guard = HandleGuard(Some(|| {
                    // SAFETY: `accessor` is non-null and owned by this scope.
                    unsafe { sys::abc_method_close(accessor) };
                }));
                if !strings.intern_method_name(accessor) {
                    return Err(invalid());
                }
                extra_entities.insert(offset);
                continue;
            }

            let index = u16::try_from(id.0).map_err(|_| invalid())?;
            // SAFETY: `f` is live.
            let offset = unsafe { sys::abc_resolve_offset_by_index(f, method_off, index) };
            if offset == ABSENT {
                return Err(invalid());
            }
            if kind == EntityKind::LiteralarrayId {
                referenced_literal_offsets.insert(offset);
                continue;
            }
            if initial_entities.contains(offset) || extra_entities.contains(offset) {
                continue;
            }
            if kind == EntityKind::StringId {
                if !strings.intern_offset_lossy(f, offset) {
                    return Err(invalid());
                }
                extra_entities.insert(offset);
                continue;
            }
            // SAFETY: `f` is live.
            let accessor = unsafe { sys::abc_method_open(f, offset) };
            if accessor.is_null() {
                return Err(invalid());
            }
            let _guard = HandleGuard(Some(|| {
                // SAFETY: `accessor` is non-null and owned by this scope.
                unsafe { sys::abc_method_close(accessor) };
            }));
            if !strings.intern_method_name(accessor) {
                return Err(invalid());
            }
            extra_entities.insert(offset);
        }

        if legacy {
            use abcd_isa::Bytecode as B;
            let global_idx = match bytecode {
                B::DeprecatedCreateobjectwithbuffer(abcd_isa::Imm(i))
                | B::DeprecatedCreatearraywithbuffer(abcd_isa::Imm(i))
                | B::DeprecatedCreateobjecthavingmethod(abcd_isa::Imm(i))
                | B::DeprecatedDefineclasswithbuffer(_, abcd_isa::Imm(i), _, _, _) => *i,
                _ => continue,
            };
            let invalid = || Error::Malformed {
                field: "legacy literal-array reference",
                context: format!(
                    "{} in method {:#x}: global index {global_idx}",
                    bytecode.mnemonic(),
                    method_off,
                ),
            };
            let Ok(idx) = u32::try_from(global_idx) else {
                return Err(invalid());
            };
            let Some((count, table_off)) = legacy_lit_table else {
                return Err(invalid());
            };
            if idx >= count {
                return Err(invalid());
            }
            let bytes: [u8; 4] = idx
                .checked_mul(4)
                .and_then(|n| table_off.checked_add(n))
                .and_then(|entry| usize::try_from(entry).ok())
                .and_then(|entry| entry.checked_add(4).and_then(|end| data.get(entry..end)))
                .and_then(|s| s.try_into().ok())
                .ok_or_else(invalid)?;
            let off = u32::from_le_bytes(bytes);
            if off == 0 || off as usize >= data.len() {
                return Err(invalid());
            }
            referenced_literal_offsets.insert(off);
        }
    }

    Ok((insn_count, raw_insns.len() as u32))
}

fn validate_try_block_spans(
    f: *const sys::AbcFileHandle,
    method_off: u32,
    cr: *mut sys::AbcCodeAccessor,
    code_byte_len: u32,
    decoded: &[(abcd_isa::Bytecode, u32)],
) -> Result<(), Error> {
    struct SpanCheckCtx<'a> {
        f: *const sys::AbcFileHandle,
        method_off: u32,
        code_byte_len: u32,
        decoded: &'a [(abcd_isa::Bytecode, u32)],
        seen_tries: u32,
        err: Option<Error>,
    }
    #[inline]
    fn check_pc(
        pc: u32,
        code_byte_len: u32,
        decoded: &[(abcd_isa::Bytecode, u32)],
        method_off: u32,
        field: &'static str,
        label: &str,
    ) -> Result<(), Error> {
        if pc == code_byte_len {
            return Ok(());
        }
        decoded
            .binary_search_by_key(&pc, |&(_, off)| off)
            .map(|_| ())
            .map_err(|_| Error::Malformed {
                field,
                context: format!(
                    "method at offset {method_off:#x}: {label} PC {pc:#x} is not on an instruction boundary"
                ),
            })
    }
    unsafe extern "C" fn cb(
        try_info: *const sys::AbcTryBlockInfo,
        catches: *const sys::AbcCatchBlockInfo,
        ctx_raw: *mut c_void,
    ) -> i32 {
        // SAFETY: `ctx_raw` points to the caller's live `SpanCheckCtx`.
        let ctx = unsafe { &mut *ctx_raw.cast::<SpanCheckCtx<'_>>() };
        if ctx.err.is_some() {
            return 0;
        }
        // SAFETY: `try_info` is a valid non-null pointer supplied by C++.
        let info = unsafe { &*try_info };
        let Some(end_pc) = info.start_pc.checked_add(info.length) else {
            ctx.err = Some(Error::Malformed {
                field: "try_block",
                context: format!("method at offset {:#x}: try span overflow", ctx.method_off),
            });
            return 0;
        };
        if let Err(e) = check_pc(
            info.start_pc,
            ctx.code_byte_len,
            ctx.decoded,
            ctx.method_off,
            "try_block",
            "try start",
        )
        .and_then(|()| {
            check_pc(
                end_pc,
                ctx.code_byte_len,
                ctx.decoded,
                ctx.method_off,
                "try_block",
                "try end",
            )
        }) {
            ctx.err = Some(e);
            return 0;
        }
        let catch_slice = if info.num_catches > 0 {
            // SAFETY: `catches` holds `info.num_catches` contiguous entries during callback.
            unsafe { std::slice::from_raw_parts(catches, info.num_catches as usize) }
        } else {
            &[]
        };
        for c in catch_slice {
            if c.type_idx != u32::MAX {
                let Ok(idx) = u16::try_from(c.type_idx) else {
                    ctx.err = Some(Error::InvalidOffset(c.type_idx));
                    return 0;
                };
                // SAFETY: `ctx.f` is a live `AbcFileHandle`.
                let resolved = unsafe { sys::abc_resolve_class_index(ctx.f, ctx.method_off, idx) };
                if resolved == ABSENT {
                    ctx.err = Some(Error::InvalidOffset(c.type_idx));
                    return 0;
                }
            }
            let Some(handler_end) = c.handler_pc.checked_add(c.code_size) else {
                ctx.err = Some(Error::Malformed {
                    field: "catch_block",
                    context: format!(
                        "method at offset {:#x}: catch span overflow",
                        ctx.method_off
                    ),
                });
                return 0;
            };
            if let Err(e) = check_pc(
                c.handler_pc,
                ctx.code_byte_len,
                ctx.decoded,
                ctx.method_off,
                "catch_block",
                "catch handler",
            )
            .and_then(|()| {
                check_pc(
                    handler_end,
                    ctx.code_byte_len,
                    ctx.decoded,
                    ctx.method_off,
                    "catch_block",
                    "catch end",
                )
            }) {
                ctx.err = Some(e);
                return 0;
            }
        }
        ctx.seen_tries = ctx.seen_tries.saturating_add(1);
        0
    }
    // SAFETY: `cr` is valid.
    let expected_tries = unsafe { sys::abc_code_tries_size(cr) };
    let mut ctx = SpanCheckCtx {
        f,
        method_off,
        code_byte_len,
        decoded,
        seen_tries: 0,
        err: None,
    };
    // SAFETY: `cr` and `ctx` are live for the synchronous enumeration call.
    let rc = unsafe {
        sys::abc_code_enumerate_try_blocks_full(cr, Some(cb), (&raw mut ctx).cast::<c_void>())
    };
    if let Some(err) = ctx.err {
        return Err(err);
    }
    if rc < 0 || ctx.seen_tries != expected_tries {
        return Err(Error::Malformed {
            field: "try_block",
            context: format!(
                "method at offset {method_off:#x}: truncated or malformed try/catch table"
            ),
        });
    }
    Ok(())
}

fn inspect_proto_types(
    f: *const sys::AbcFileHandle,
    proto_off: u32,
    initial_entities: &CompactU32Set,
) -> Result<usize, Error> {
    // SAFETY: `f` is a live `AbcFileHandle`.
    let pr = unsafe { sys::abc_proto_open(f, proto_off) };
    if pr.is_null() {
        return Err(Error::InvalidOffset(proto_off));
    }
    let _pg = HandleGuard(Some(|| {
        // SAFETY: `pr` is non-null and owned by this scope.
        unsafe { sys::abc_proto_close(pr) };
    }));

    // SAFETY: `pr` is valid.
    let ref_num = unsafe { sys::abc_proto_get_ref_num(pr) };
    let mut next_ref = 0u32;
    let mut check_type = |raw: TypeId, ctx: &str| -> Result<(), Error> {
        if raw == TypeId::Reference {
            if next_ref >= ref_num {
                return Err(Error::Malformed {
                    field: "reference_type",
                    context: ctx.to_string(),
                });
            }
            // SAFETY: `pr` is valid and `next_ref < ref_num`.
            let off = unsafe { sys::abc_proto_get_reference_type(pr, next_ref) };
            next_ref += 1;
            if off == u32::MAX || !initial_entities.contains(off) {
                return Err(Error::Malformed {
                    field: "reference_type",
                    context: ctx.to_string(),
                });
            }
            Ok(())
        } else {
            Type::from_raw(raw, None).map(|_| ())
        }
    };

    // SAFETY: `pr` is valid.
    let raw_ret = TypeId::try_from(unsafe { sys::abc_proto_get_return_type(pr) })?;
    check_type(raw_ret, "return type")?;

    unsafe extern "C" fn push_proto_type(raw: u8, ctx: *mut c_void) {
        // SAFETY: `ctx` points to the caller's live `Vec<u8>`.
        unsafe { &mut *ctx.cast::<Vec<u8>>() }.push(raw);
    }
    let mut enum_raw: Vec<u8> = Vec::new();
    // SAFETY: `pr` and `enum_raw` are live for the synchronous enumeration call.
    let rc = unsafe {
        sys::abc_proto_enumerate_types(
            pr,
            Some(push_proto_type),
            (&raw mut enum_raw).cast::<c_void>(),
        )
    };
    if rc < 0 || enum_raw.is_empty() {
        return Err(Error::Malformed {
            field: "proto",
            context: format!("proto at offset {proto_off:#x}: truncated or malformed shorty"),
        });
    }
    for (idx, &raw_byte) in enum_raw[1..].iter().enumerate() {
        let raw = TypeId::try_from(raw_byte)?;
        check_type(raw, &format!("arg {idx}"))?;
    }
    Ok(enum_raw.len() - 1)
}

fn inspect_param_annotations(
    f: *const sys::AbcFileHandle,
    mr: *mut sys::AbcMethodAccessor,
    num_params: usize,
    initial_entities: &CompactU32Set,
    strings: &mut SummaryStrings<'_>,
    ann_nested_raw_targets: &mut Vec<u32>,
    ann_visiting: &mut HashSet<u32>,
) -> Result<(), Error> {
    let _ = num_params;
    for item_off in [
        // SAFETY: `mr` is valid.
        unsafe { sys::abc_method_get_param_annotation_id(mr) },
        // SAFETY: `mr` is valid.
        unsafe { sys::abc_method_get_runtime_param_annotation_id(mr) },
    ] {
        if item_off == ABSENT {
            continue;
        }
        let mut pairs: Vec<(u32, u32)> = Vec::new();
        unsafe extern "C" fn cb(param_idx: u32, annotation_off: u32, ctx: *mut c_void) -> i32 {
            // SAFETY: `ctx` points to the caller's live `Vec<(u32, u32)>`.
            let pairs = unsafe { &mut *ctx.cast::<Vec<(u32, u32)>>() };
            pairs.push((param_idx, annotation_off));
            0
        }
        // SAFETY: `f` and `pairs` are live for the synchronous enumeration call.
        let rc = unsafe {
            sys::abc_param_annotations_enumerate(
                f,
                item_off,
                Some(cb),
                (&raw mut pairs).cast::<c_void>(),
            )
        };
        if rc != 0 {
            return Err(Error::Malformed {
                field: "param_annotations",
                context: format!("param annotations item at offset {item_off:#x}"),
            });
        }
        if pairs.is_empty() {
            continue;
        }
        for &(i, _) in &pairs {
            if i.checked_add(1)
                .and_then(|n| usize::try_from(n).ok())
                .is_none()
            {
                return Err(Error::Malformed {
                    field: "param_annotations",
                    context: format!("param annotations item at offset {item_off:#x}"),
                });
            }
        }
        for (_, off) in pairs {
            inspect_annotation_at(
                f,
                off,
                initial_entities,
                strings,
                ann_nested_raw_targets,
                ann_visiting,
            )?;
        }
    }
    Ok(())
}

#[expect(
    clippy::too_many_arguments,
    reason = "streaming field inspector populates independent offset sets directly without allocating Field structs"
)]
fn inspect_field_at(
    f: *const sys::AbcFileHandle,
    file_bytes: &[u8],
    field_off: u32,
    class_desc_sym: SymId,
    is_mod_rec_cls: bool,
    is_scope_rec_cls: bool,
    initial_entities: &CompactU32Set,
    strings: &mut SummaryStrings<'_>,
    module_data_offsets: &mut CompactU32Set,
    scope_names_offsets: &mut CompactU32Set,
    phase_blob_offsets: &mut CompactU32Set,
    ann_nested_raw_targets: &mut Vec<u32>,
    ann_visiting: &mut HashSet<u32>,
) -> Result<(), Error> {
    // SAFETY: `f` is a live `AbcFileHandle`.
    let fr = unsafe { sys::abc_field_open(f, field_off) };
    if fr.is_null() {
        return Err(Error::InvalidOffset(field_off));
    }
    let _fg = HandleGuard(Some(|| {
        // SAFETY: `fr` is non-null and owned by this scope.
        unsafe { sys::abc_field_close(fr) };
    }));

    // SAFETY: `fr` is valid.
    let field_id = unsafe { sys::abc_field_get_field_id(fr) };
    // SAFETY: `fr` is valid.
    let name_off = unsafe { sys::abc_field_name_off(fr) };
    let name_sym = if name_off == ABSENT {
        return Err(Error::Malformed {
            field: "name",
            context: format!("field at offset {field_id:#x}"),
        });
    } else {
        strings
            .intern_offset_lossy_sym(f, name_off)
            .ok_or_else(|| Error::Malformed {
                field: "name",
                context: format!("field at offset {field_id:#x}"),
            })?
    };

    // SAFETY: `fr` is valid.
    let type_raw = unsafe { sys::abc_field_type(fr) };
    // SAFETY: `fr` is valid.
    let type_id = TypeId::try_from(unsafe { sys::abc_field_type_id(fr) })?;
    if type_id == TypeId::Reference {
        if !initial_entities.contains(type_raw) {
            let fname = strings.resolve_utf8(name_sym).unwrap_or("?").to_owned();
            return Err(Error::Malformed {
                field: "field_type",
                context: format!("field {fname:?}"),
            });
        }
    } else {
        Type::from_raw(type_id, None)?;
    }

    let u32_val = if type_id == TypeId::U32 {
        let mut v = 0i32;
        // SAFETY: `fr` is valid and `&mut v` is writable.
        (unsafe { sys::abc_field_get_value_i32(fr, &mut v) } != 0).then_some(v)
    } else {
        match type_id {
            TypeId::U1
            | TypeId::I8
            | TypeId::U8
            | TypeId::I16
            | TypeId::U16
            | TypeId::I32
            | TypeId::Tagged => {
                let mut v = 0i32;
                // SAFETY: `fr` is valid and `&mut v` is writable.
                unsafe { sys::abc_field_get_value_i32(fr, &mut v) };
            }
            TypeId::I64 | TypeId::U64 => {
                let mut v = 0i64;
                // SAFETY: `fr` is valid and `&mut v` is writable.
                unsafe { sys::abc_field_get_value_i64(fr, &mut v) };
            }
            TypeId::F32 => {
                let mut v = 0.0f32;
                // SAFETY: `fr` is valid and `&mut v` is writable.
                unsafe { sys::abc_field_get_value_f32(fr, &mut v) };
            }
            TypeId::F64 => {
                let mut v = 0.0f64;
                // SAFETY: `fr` is valid and `&mut v` is writable.
                unsafe { sys::abc_field_get_value_f64(fr, &mut v) };
            }
            TypeId::Reference => {
                let mut v = 0i32;
                // SAFETY: `fr` is valid and `&mut v` is writable.
                if unsafe { sys::abc_field_get_value_i32(fr, &mut v) } != 0 {
                    let offset = v as u32;
                    if offset == 0 || !strings.intern_offset_lossy(f, offset) {
                        return Err(Error::InvalidString(offset));
                    }
                }
            }
            TypeId::Void | TypeId::U32 => {}
        }
        None
    };

    if let Some(off) = u32_val {
        let is_ext = is_external(f, field_id);
        let field_name = strings.resolve_utf8(name_sym);
        if field_name == Some(TYPE_SUMMARY_OFFSET_FIELD) {
            let offset = off as u32;
            if offset != 0 {
                if initial_entities.contains(offset)
                    // SAFETY: `f` is live; null callback performs structural validation only.
                    || unsafe {
                        sys::abc_literal_enumerate_vals_checked(
                            f,
                            offset,
                            None,
                            std::ptr::null_mut(),
                        )
                    } != 0
                {
                    return Err(Error::InvalidOffset(offset));
                }
                scope_names_offsets.insert(offset);
            }
        } else if field_name == Some(MODULE_REQUEST_PHASE_FIELD) {
            let class_desc = strings
                .resolve_utf8(class_desc_sym)
                .unwrap_or("?")
                .to_owned();
            let offset = u32::try_from(off).map_err(|_| {
                Error::ModuleData(format!(
                    "{class_desc} field at {field_off:#x}: negative blob offset {off}"
                ))
            })?;
            inspect_module_request_phase_at(f, offset).map_err(|e| {
                Error::ModuleData(format!(
                    "{class_desc} moduleRequestPhaseIdx field at {field_off:#x}: {e}"
                ))
            })?;
            phase_blob_offsets.insert(offset);
        } else if is_mod_rec_cls || field_name == Some(MODULE_RECORD_IDX_FIELD) {
            let class_desc = strings
                .resolve_utf8(class_desc_sym)
                .unwrap_or("?")
                .to_owned();
            let offset = u32::try_from(off).map_err(|_| {
                Error::ModuleData(format!(
                    "{class_desc} field at {field_off:#x}: negative blob offset {off}"
                ))
            })?;
            match inspect_module_data_at(f, offset, strings) {
                Ok(()) => {}
                Err(e @ Error::Malformed { .. }) => return Err(e),
                Err(e) => {
                    return Err(Error::ModuleData(format!(
                        "{class_desc} field at {field_off:#x}: {e}"
                    )));
                }
            }
            module_data_offsets.insert(offset);
        } else if is_scope_rec_cls || field_name == Some(SCOPE_NAMES_FIELD) {
            let class_desc = strings
                .resolve_utf8(class_desc_sym)
                .unwrap_or("?")
                .to_owned();
            let offset = u32::try_from(off).map_err(|_| {
                Error::ModuleData(format!(
                    "{class_desc} field at {field_off:#x}: negative blob offset {off}"
                ))
            })?;
            scope_names_offsets.insert(offset);
        } else if field_name == Some(JSON_FILE_CONTENT_FIELD)
            || field_first_tag(file_bytes, field_off, is_ext) == Some(0x02)
        {
            let offset = off as u32;
            if offset == 0 || !strings.intern_offset_lossy(f, offset) {
                return Err(Error::InvalidString(offset));
            }
        }
    }

    for enumerate in [
        sys::abc_field_enumerate_annotations,
        sys::abc_field_enumerate_runtime_annotations,
        sys::abc_field_enumerate_type_annotations,
        sys::abc_field_enumerate_runtime_type_annotations,
    ] {
        for ann_off in collect_offsets_int(fr, enumerate, "field_annotations", field_off)? {
            inspect_annotation_at(
                f,
                ann_off,
                initial_entities,
                strings,
                ann_nested_raw_targets,
                ann_visiting,
            )?;
        }
    }
    Ok(())
}

fn inspect_module_request_phase_at(f: *const sys::AbcFileHandle, offset: u32) -> Result<(), Error> {
    unsafe extern "C" fn noop(_flag: u8, _ctx: *mut c_void) {}
    // SAFETY: `f` is live and `noop` does not dereference `ctx`.
    let n =
        unsafe { sys::abc_module_request_phase_read(f, offset, Some(noop), std::ptr::null_mut()) };
    if n < 0 {
        return Err(Error::ModuleData(format!(
            "module-request-phase blob at {offset:#x} is unreadable"
        )));
    }
    Ok(())
}

fn inspect_module_data_at(
    f: *const sys::AbcFileHandle,
    offset: u32,
    strings: &mut SummaryStrings<'_>,
) -> Result<(), Error> {
    // SAFETY: `f` is a live `AbcFileHandle`.
    let mr = unsafe { sys::abc_module_open(f, offset) };
    if mr.is_null() {
        return Err(Error::InvalidOffset(offset));
    }
    let _mg = HandleGuard(Some(|| {
        // SAFETY: `mr` is non-null and owned by this scope.
        unsafe { sys::abc_module_close(mr) };
    }));

    // SAFETY: `mr` is valid.
    let num_requests = unsafe { sys::abc_module_num_requests(mr) };
    for i in 0..num_requests {
        // SAFETY: `mr` is valid and `i < num_requests`.
        let off = unsafe { sys::abc_module_request_off(mr, i) };
        if off == ABSENT || !strings.intern_offset_utf8(f, off) {
            return Err(Error::InvalidString(off));
        }
    }

    struct RawRec {
        tag: u8,
        export_off: u32,
        import_off: u32,
        local_off: u32,
    }
    unsafe extern "C" fn collect_rec(
        tag: u8,
        export_off: u32,
        _request_idx: u32,
        import_off: u32,
        local_off: u32,
        ctx: *mut c_void,
    ) {
        // SAFETY: `ctx` points to the caller's live `Vec<RawRec>`.
        unsafe { &mut *ctx.cast::<Vec<RawRec>>() }.push(RawRec {
            tag,
            export_off,
            import_off,
            local_off,
        });
    }
    let mut raw: Vec<RawRec> = Vec::new();
    // SAFETY: `mr` and `raw` are live for the synchronous enumeration call.
    let rc = unsafe {
        sys::abc_module_enumerate_records(mr, Some(collect_rec), (&raw mut raw).cast::<c_void>())
    };
    if rc < 0 {
        return Err(Error::Malformed {
            field: "module_data",
            context: format!("truncated or malformed module record blob at {offset:#x}"),
        });
    }
    for rec in raw {
        match rec.tag {
            t if t == sys::ModuleTag_REGULAR_IMPORT => {
                if !strings.intern_offset_utf8(f, rec.local_off) {
                    return Err(Error::InvalidString(rec.local_off));
                }
                if !strings.intern_offset_utf8(f, rec.import_off) {
                    return Err(Error::InvalidString(rec.import_off));
                }
            }
            t if t == sys::ModuleTag_NAMESPACE_IMPORT => {
                if !strings.intern_offset_utf8(f, rec.local_off) {
                    return Err(Error::InvalidString(rec.local_off));
                }
            }
            t if t == sys::ModuleTag_LOCAL_EXPORT => {
                if !strings.intern_offset_utf8(f, rec.local_off) {
                    return Err(Error::InvalidString(rec.local_off));
                }
                if !strings.intern_offset_utf8(f, rec.export_off) {
                    return Err(Error::InvalidString(rec.export_off));
                }
            }
            t if t == sys::ModuleTag_INDIRECT_EXPORT => {
                if !strings.intern_offset_utf8(f, rec.export_off) {
                    return Err(Error::InvalidString(rec.export_off));
                }
                if !strings.intern_offset_utf8(f, rec.import_off) {
                    return Err(Error::InvalidString(rec.import_off));
                }
            }
            t if t == sys::ModuleTag_STAR_EXPORT => {}
            other => {
                return Err(Error::ModuleData(format!(
                    "unknown module record tag {other:#x} in blob at {offset:#x}"
                )));
            }
        }
    }
    Ok(())
}

fn resolve_foreign_entity_name_summary(
    f: *const sys::AbcFileHandle,
    initial_entities: &CompactU32Set,
    strings: &mut SummaryStrings<'_>,
    off: u32,
) {
    if initial_entities.contains(off) {
        return;
    }
    // SAFETY: `f` is a live `AbcFileHandle`.
    let name_off = unsafe { sys::abc_foreign_item_name_off(f, off) };
    if name_off == ABSENT || !strings.intern_offset_utf8(f, name_off) {
        strings.intern_utf8_str("");
    }
}

struct SummaryAnnFrame {
    off: u32,
    ar: OpenAnnotation,
    count: u32,
    next_idx: u32,
    pending_array: Option<std::vec::IntoIter<u32>>,
}

fn open_summary_ann_frame(
    f: *const sys::AbcFileHandle,
    off: u32,
    initial_entities: &CompactU32Set,
    visiting: &mut HashSet<u32>,
) -> Result<SummaryAnnFrame, Error> {
    if !visiting.insert(off) {
        return Err(Error::Malformed {
            field: "nested annotation",
            context: format!("cyclic annotation reference at offset {off:#x}"),
        });
    }
    // SAFETY: `f` is a live `AbcFileHandle`.
    let ar = unsafe { sys::abc_annotation_open(f, off) };
    if ar.is_null() {
        visiting.remove(&off);
        return Err(Error::InvalidOffset(off));
    }
    let ar = OpenAnnotation(ar);
    // SAFETY: `ar.0` is non-null and valid.
    let class_off = unsafe { sys::abc_annotation_class_off(ar.0) };
    if !initial_entities.contains(class_off) {
        visiting.remove(&off);
        return Err(Error::Malformed {
            field: "class_descriptor",
            context: format!("annotation at offset {off:#x}"),
        });
    }
    // SAFETY: `ar.0` is non-null and valid.
    let count = unsafe { sys::abc_annotation_count(ar.0) };
    Ok(SummaryAnnFrame {
        off,
        ar,
        count,
        next_idx: 0,
        pending_array: None,
    })
}

/// Iterative annotation validator & string/literal-offset collector (zero
/// recursion, active-path cycle detection, zero `Annotation` heap allocation).
fn inspect_annotation_at(
    f: *const sys::AbcFileHandle,
    root_off: u32,
    initial_entities: &CompactU32Set,
    strings: &mut SummaryStrings<'_>,
    ann_nested_raw_targets: &mut Vec<u32>,
    visiting: &mut HashSet<u32>,
) -> Result<(), Error> {
    use sys::AnnotationValueType as AVT;

    visiting.clear();
    let mut stack = vec![open_summary_ann_frame(
        f,
        root_off,
        initial_entities,
        visiting,
    )?];

    while let Some(frame) = stack.last_mut() {
        if let Some(mut remaining) = frame.pending_array.take()
            && let Some(next_off) = remaining.next()
        {
            frame.pending_array = Some(remaining);
            let child = open_summary_ann_frame(f, next_off, initial_entities, visiting)?;
            stack.push(child);
            continue;
        }

        let mut next_child: Option<SummaryAnnFrame> = None;
        while frame.next_idx < frame.count {
            let idx = frame.next_idx;
            frame.next_idx += 1;
            let off = frame.off;
            let ar = frame.ar.0;

            let mut out = sys::AbcAnnotationElem {
                name_off: 0,
                tag: 0,
                value: 0,
            };
            // SAFETY: `ar` is valid and `&mut out` is writable.
            if unsafe { sys::abc_annotation_get_element(ar, idx, &mut out) } != 0 {
                return Err(Error::Malformed {
                    field: "annotation element",
                    context: format!("annotation at offset {off:#x}, element {idx}"),
                });
            }
            if !strings.intern_offset_utf8(f, out.name_off) {
                return Err(Error::InvalidString(out.name_off));
            }
            let tag = AVT::try_from(out.tag).unwrap_or(AVT::Unknown);
            match tag {
                AVT::U1
                | AVT::I8
                | AVT::U8
                | AVT::I16
                | AVT::U16
                | AVT::I32
                | AVT::U32
                | AVT::F32
                | AVT::Void
                | AVT::StringNullptr => {}
                AVT::Unknown => {
                    return Err(Error::Malformed {
                        field: "annotation element tag",
                        context: format!(
                            "annotation at offset {off:#x}, element {idx}: unknown tag {:#x}",
                            out.tag
                        ),
                    });
                }
                AVT::I64 => {
                    let mut v = 0i64;
                    // SAFETY: `ar` is valid and `&mut v` is writable.
                    if unsafe { sys::abc_annotation_get_value_i64(ar, idx, &mut v) } != 0 {
                        return Err(Error::Malformed {
                            field: "annotation element value",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx} (tag {tag:?})"
                            ),
                        });
                    }
                }
                AVT::U64 => {
                    let mut v = 0u64;
                    // SAFETY: `ar` is valid and `&mut v` is writable.
                    if unsafe { sys::abc_annotation_get_value_u64(ar, idx, &mut v) } != 0 {
                        return Err(Error::Malformed {
                            field: "annotation element value",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx} (tag {tag:?})"
                            ),
                        });
                    }
                }
                AVT::F64 => {
                    let mut v = 0.0f64;
                    // SAFETY: `ar` is valid and `&mut v` is writable.
                    if unsafe { sys::abc_annotation_get_value_f64(ar, idx, &mut v) } != 0 {
                        return Err(Error::Malformed {
                            field: "annotation element value",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx} (tag {tag:?})"
                            ),
                        });
                    }
                }
                AVT::String => {
                    if !strings.intern_offset_utf8(f, out.value) {
                        return Err(Error::InvalidString(out.value));
                    }
                }
                AVT::Record => {
                    if !initial_entities.contains(out.value) {
                        return Err(Error::InvalidOffset(out.value));
                    }
                }
                AVT::Method | AVT::Enum => {
                    resolve_foreign_entity_name_summary(f, initial_entities, strings, out.value);
                }
                AVT::Annotation => {
                    next_child = Some(open_summary_ann_frame(
                        f,
                        out.value,
                        initial_entities,
                        visiting,
                    )?);
                    break;
                }
                AVT::MethodHandle => {
                    let mut handle_type_raw = 0u8;
                    let mut entity_off = 0u32;
                    // SAFETY: `f` is live and out-pointers are writable.
                    if unsafe {
                        sys::abc_method_handle_read(
                            f,
                            out.value,
                            &mut handle_type_raw,
                            &mut entity_off,
                        )
                    } != 0
                    {
                        return Err(Error::Malformed {
                            field: "method_handle",
                            context: format!("annotation at offset {off:#x}, element {idx}"),
                        });
                    }
                    if MethodHandleType::from_u8(handle_type_raw).is_none() {
                        return Err(Error::Malformed {
                            field: "method_handle_type",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx}: unknown handle type {handle_type_raw:#x}"
                            ),
                        });
                    }
                    if !initial_entities.contains(entity_off) {
                        strings.intern_utf8_str("");
                    }
                }
                AVT::LiteralArray => {
                    inspect_checked_literal_array_at(
                        f,
                        out.value,
                        strings,
                        ann_nested_raw_targets,
                    )?;
                }
                AVT::ArrayAnnotation => {
                    let mut arr = sys::AbcAnnotationArrayVal {
                        count: 0,
                        entity_off: 0,
                    };
                    // SAFETY: `ar` is valid and `&mut arr` is writable.
                    if unsafe { sys::abc_annotation_get_array_element(ar, idx, &mut arr) } != 0 {
                        return Err(Error::Malformed {
                            field: "annotation array element",
                            context: format!("annotation at offset {off:#x}, element {idx}"),
                        });
                    }
                    let (_, raw_values) =
                        read_annotation_array_raw(f, out.tag, arr.count, arr.entity_off)?;
                    let mut offsets_iter = raw_values
                        .into_iter()
                        .map(|v| v as u32)
                        .collect::<Vec<_>>()
                        .into_iter();
                    if let Some(first_off) = offsets_iter.next() {
                        frame.pending_array = Some(offsets_iter);
                        next_child = Some(open_summary_ann_frame(
                            f,
                            first_off,
                            initial_entities,
                            visiting,
                        )?);
                        break;
                    }
                }
                AVT::Array
                | AVT::ArrayU1
                | AVT::ArrayI8
                | AVT::ArrayU8
                | AVT::ArrayI16
                | AVT::ArrayU16
                | AVT::ArrayI32
                | AVT::ArrayU32
                | AVT::ArrayI64
                | AVT::ArrayU64
                | AVT::ArrayF32
                | AVT::ArrayF64
                | AVT::ArrayString
                | AVT::ArrayRecord
                | AVT::ArrayMethod
                | AVT::ArrayEnum
                | AVT::ArrayMethodHandle => {
                    let mut arr = sys::AbcAnnotationArrayVal {
                        count: 0,
                        entity_off: 0,
                    };
                    // SAFETY: `ar` is valid and `&mut arr` is writable.
                    if unsafe { sys::abc_annotation_get_array_element(ar, idx, &mut arr) } != 0 {
                        return Err(Error::Malformed {
                            field: "annotation array element",
                            context: format!("annotation at offset {off:#x}, element {idx}"),
                        });
                    }
                    let (avt, raw_values) =
                        read_annotation_array_raw(f, out.tag, arr.count, arr.entity_off)?;
                    for raw in raw_values {
                        match avt {
                            AVT::ArrayU1
                            | AVT::ArrayI8
                            | AVT::ArrayU8
                            | AVT::ArrayI16
                            | AVT::ArrayU16
                            | AVT::ArrayI32
                            | AVT::ArrayU32
                            | AVT::ArrayI64
                            | AVT::ArrayU64
                            | AVT::ArrayF32
                            | AVT::ArrayF64 => {}
                            AVT::ArrayString => {
                                if !strings.intern_offset_utf8(f, raw as u32) {
                                    return Err(Error::InvalidString(raw as u32));
                                }
                            }
                            AVT::ArrayRecord => {
                                if !initial_entities.contains(raw as u32) {
                                    return Err(Error::InvalidOffset(raw as u32));
                                }
                            }
                            AVT::ArrayMethod | AVT::ArrayEnum => {
                                resolve_foreign_entity_name_summary(
                                    f,
                                    initial_entities,
                                    strings,
                                    raw as u32,
                                );
                            }
                            AVT::ArrayMethodHandle => {
                                let mut handle_type_raw = 0u8;
                                let mut entity_off = 0u32;
                                // SAFETY: `f` is live and out-pointers are writable.
                                if unsafe {
                                    sys::abc_method_handle_read(
                                        f,
                                        raw as u32,
                                        &mut handle_type_raw,
                                        &mut entity_off,
                                    )
                                } != 0
                                {
                                    return Err(Error::Malformed {
                                        field: "method_handle",
                                        context: format!(
                                            "annotation array at offset {:#x}",
                                            arr.entity_off
                                        ),
                                    });
                                }
                                if MethodHandleType::from_u8(handle_type_raw).is_none() {
                                    return Err(Error::Malformed {
                                        field: "method_handle_type",
                                        context: format!(
                                            "annotation array at offset {:#x}: unknown handle type {handle_type_raw:#x}",
                                            arr.entity_off
                                        ),
                                    });
                                }
                                if !initial_entities.contains(entity_off) {
                                    strings.intern_utf8_str("");
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
        }

        if let Some(child) = next_child {
            stack.push(child);
            continue;
        }

        let Some(finished) = stack.pop() else {
            break;
        };
        visiting.remove(&finished.off);
        if stack.is_empty() {
            return Ok(());
        }
    }
    Ok(())
}

struct SummaryLiteralCbCtx<'a, 's> {
    file: *const sys::AbcFileHandle,
    strings: &'s mut SummaryStrings<'a>,
    nested: &'s mut Vec<u32>,
    error: Option<Error>,
}

unsafe extern "C" fn summary_literal_val_cb(val: *const sys::AbcLiteralVal, ctx: *mut c_void) {
    // SAFETY: `ctx` points to the caller's live `SummaryLiteralCbCtx`.
    let ctx = unsafe { &mut *ctx.cast::<SummaryLiteralCbCtx<'_, '_>>() };
    if ctx.error.is_some() {
        return;
    }
    // SAFETY: `val` is a valid non-null pointer supplied by C++.
    let v = unsafe { &*val };
    let tag = match crate::literal::LiteralTag::try_from(v.tag) {
        Ok(t) => t,
        Err(e) => {
            ctx.error = Some(e);
            return;
        }
    };
    match tag {
        crate::literal::LiteralTag::String | crate::literal::LiteralTag::EtsImplements => {
            // SAFETY: `STRING` and `ETS_IMPLEMENTS` populate `u32_val`.
            let off = unsafe { v.data.u32_val };
            if !ctx.strings.intern_offset_lossy(ctx.file, off) {
                ctx.error = Some(Error::InvalidString(off));
            }
        }
        crate::literal::LiteralTag::LiteralArray => {
            // SAFETY: `LITERALARRAY` populates `u32_val`.
            ctx.nested.push(unsafe { v.data.u32_val });
        }
        crate::literal::LiteralTag::ArrayU1
        | crate::literal::LiteralTag::ArrayU8
        | crate::literal::LiteralTag::ArrayI8 => {
            // SAFETY: `ARRAY_*` tags populate `u32_val` payload offset.
            let payload_off = unsafe { v.data.u32_val };
            if let Err(err) = crate::literal::read_typed_literal_array_raw(ctx.file, payload_off, 1)
            {
                ctx.error = Some(err);
            }
        }
        crate::literal::LiteralTag::ArrayU16 | crate::literal::LiteralTag::ArrayI16 => {
            // SAFETY: `ARRAY_*` tags populate `u32_val` payload offset.
            let payload_off = unsafe { v.data.u32_val };
            if let Err(err) = crate::literal::read_typed_literal_array_raw(ctx.file, payload_off, 2)
            {
                ctx.error = Some(err);
            }
        }
        crate::literal::LiteralTag::ArrayU32
        | crate::literal::LiteralTag::ArrayI32
        | crate::literal::LiteralTag::ArrayF32 => {
            // SAFETY: `ARRAY_*` tags populate `u32_val` payload offset.
            let payload_off = unsafe { v.data.u32_val };
            if let Err(err) = crate::literal::read_typed_literal_array_raw(ctx.file, payload_off, 4)
            {
                ctx.error = Some(err);
            }
        }
        crate::literal::LiteralTag::ArrayU64
        | crate::literal::LiteralTag::ArrayI64
        | crate::literal::LiteralTag::ArrayF64 => {
            // SAFETY: `ARRAY_*` tags populate `u32_val` payload offset.
            let payload_off = unsafe { v.data.u32_val };
            if let Err(err) = crate::literal::read_typed_literal_array_raw(ctx.file, payload_off, 8)
            {
                ctx.error = Some(err);
            }
        }
        crate::literal::LiteralTag::ArrayString => {
            // SAFETY: `ARRAY_STRING` populates `u32_val` payload offset.
            let payload_off = unsafe { v.data.u32_val };
            match crate::literal::read_typed_literal_array_raw(ctx.file, payload_off, 4) {
                Ok(raw) => {
                    for x in raw {
                        let off = x as u32;
                        if !ctx.strings.intern_offset_lossy(ctx.file, off) {
                            ctx.error = Some(Error::InvalidString(off));
                            return;
                        }
                    }
                }
                Err(err) => {
                    ctx.error = Some(err);
                }
            }
        }
        _ => {}
    }
}

fn inspect_checked_literal_array_at(
    f: *const sys::AbcFileHandle,
    offset: u32,
    strings: &mut SummaryStrings<'_>,
    nested_out: &mut Vec<u32>,
) -> Result<(), Error> {
    let mut ctx = SummaryLiteralCbCtx {
        file: f,
        strings,
        nested: nested_out,
        error: None,
    };
    // SAFETY: `f` and `ctx` are live for the synchronous enumeration call.
    let rc = unsafe {
        sys::abc_literal_enumerate_vals_checked(
            f,
            offset,
            Some(summary_literal_val_cb),
            (&raw mut ctx).cast::<c_void>(),
        )
    };
    if let Some(err) = ctx.error {
        return Err(err);
    }
    if rc != 0 {
        return Err(Error::InvalidOffset(offset));
    }
    Ok(())
}

fn count_literal_arrays_summary(
    f: *const sys::AbcFileHandle,
    file_size: u32,
    strings: &mut SummaryStrings<'_>,
    referenced_offsets: &CompactU32Set,
    module_data_offsets: &CompactU32Set,
    phase_blob_offsets: &CompactU32Set,
) -> Result<usize, Error> {
    // SAFETY: `f` is a live `AbcFileHandle`.
    let n = unsafe { sys::abc_file_num_literalarrays(f) };
    let mut offsets = Vec::new();
    let mut seen = CompactU32Set::default();
    if n != 0 {
        for i in 0..n {
            // SAFETY: `f` is live and `i < n`.
            let off = unsafe { sys::abc_file_literalarray_offset(f, i) };
            if off != ABSENT
                && !module_data_offsets.contains(off)
                && !phase_blob_offsets.contains(off)
                && seen.insert(off)
            {
                offsets.push(off);
            }
        }
    }
    let mut referenced: Vec<u32> = referenced_offsets
        .iter()
        .filter(|&off| {
            off != ABSENT
                && !seen.contains(off)
                && !module_data_offsets.contains(off)
                && !phase_blob_offsets.contains(off)
        })
        .collect();
    referenced.sort_unstable();
    for off in referenced {
        if seen.insert(off) {
            offsets.push(off);
        }
    }
    if offsets.is_empty() {
        return Ok(0);
    }

    let mut decoded = 0usize;
    let mut raw_nested = Vec::new();
    while decoded < offsets.len() {
        let mut batch_nested = Vec::new();
        for &off in &offsets[decoded..] {
            raw_nested.clear();
            let mut ctx = SummaryLiteralCbCtx {
                file: f,
                strings,
                nested: &mut raw_nested,
                error: None,
            };
            // SAFETY: `f` and `ctx` are live for the synchronous enumeration call.
            let rc = unsafe {
                sys::abc_literal_enumerate_vals_checked(
                    f,
                    off,
                    Some(summary_literal_val_cb),
                    (&raw mut ctx).cast::<c_void>(),
                )
            };
            if let Some(err) = ctx.error {
                return Err(err);
            }
            if rc != 0 {
                return Err(Error::InvalidOffset(off));
            }
            for &target in &raw_nested {
                if is_plausible_literal_array_offset(
                    target,
                    file_size,
                    module_data_offsets,
                    phase_blob_offsets,
                ) && !seen.contains(target)
                {
                    batch_nested.push(target);
                }
            }
        }
        decoded = offsets.len();
        batch_nested.sort_unstable();
        batch_nested.dedup();
        for off in batch_nested {
            if seen.insert(off) {
                offsets.push(off);
            }
        }
    }
    Ok(offsets.len())
}

struct SummaryDebugSink<'a, 's> {
    strings: &'s mut SummaryStrings<'a>,
    started_regs: Vec<i32>,
}

impl<'a, 's> SummaryDebugSink<'a, 's> {
    fn new(strings: &'s mut SummaryStrings<'a>) -> Self {
        Self {
            strings,
            started_regs: Vec::new(),
        }
    }

    #[inline]
    fn intern_required(&mut self, s: crate::debug::RawDebugStr<'_>) {
        match s {
            crate::debug::RawDebugStr::Empty => {
                self.strings.intern_utf8_str("");
            }
            crate::debug::RawDebugStr::Static(text) => {
                self.strings.intern_utf8_str(text);
            }
            crate::debug::RawDebugStr::Borrowed(_, start, len) => {
                self.strings.intern_in_place_utf8(start, len);
            }
            crate::debug::RawDebugStr::Owned(text) => {
                self.strings.intern_utf8_str(&text);
            }
        }
    }

    #[inline]
    fn intern_optional(&mut self, s: crate::debug::RawDebugStr<'_>) {
        match s {
            crate::debug::RawDebugStr::Empty => {}
            crate::debug::RawDebugStr::Static(text) => {
                if !text.is_empty() {
                    self.strings.intern_utf8_str(text);
                }
            }
            crate::debug::RawDebugStr::Borrowed(_, start, len) => {
                self.strings.intern_in_place_utf8(start, len);
            }
            crate::debug::RawDebugStr::Owned(text) => {
                if !text.is_empty() {
                    self.strings.intern_utf8_str(&text);
                }
            }
        }
    }
}

impl crate::debug::DebugSink for SummaryDebugSink<'_, '_> {
    fn set_source_file(&mut self, s: crate::debug::RawDebugStr<'_>) {
        self.intern_optional(s);
    }

    fn set_source_code(&mut self, s: crate::debug::RawDebugStr<'_>) {
        self.intern_optional(s);
    }

    fn push_line(&mut self, _pc_offset: u32, _line: u32) {}

    fn push_column(&mut self, _pc_offset: u32, _column: u32) {}

    fn start_local(
        &mut self,
        reg_number: i32,
        name: crate::debug::RawDebugStr<'_>,
        type_name: crate::debug::RawDebugStr<'_>,
        type_sig: Option<crate::debug::RawDebugStr<'_>>,
        _pc_offset: u32,
    ) {
        self.intern_required(name);
        self.intern_required(type_name);
        if let Some(sig) = type_sig {
            self.intern_required(sig);
        }
        self.started_regs.push(reg_number);
    }

    fn end_local(&mut self, reg_number: i32, _pc_offset: u32) -> Result<(), Error> {
        if !self.started_regs.contains(&reg_number) {
            return Err(Error::DebugInfoExtraction);
        }
        Ok(())
    }

    fn finish_locals(&mut self, _final_pc_offset: u32) {}

    fn push_param(
        &mut self,
        name: crate::debug::RawDebugStr<'_>,
        sig: crate::debug::RawDebugStr<'_>,
    ) {
        self.intern_required(name);
        self.intern_required(sig);
    }
}

// ---------------------------------------------------------------------------
// Internal decode helpers
// ---------------------------------------------------------------------------

/// Legacy (0.0.0.2) literal-array global table: `(num_literalarrays,
/// literalarray_idx_off)` read from the file header (`File::Header` field
/// layout is unchanged since 3.1: u32 fields start at offset 16, these two
/// are the 8th and 9th). Returns `None` if the header is truncated.
fn legacy_literalarray_table(data: &[u8]) -> Option<(u32, u32)> {
    let read = |off: usize| -> Option<u32> {
        let bytes: [u8; 4] = data.get(off..off.checked_add(4)?)?.try_into().ok()?;
        Some(u32::from_le_bytes(bytes))
    };
    let count = read(44)?;
    let table_off = read(48)?;
    let byte_len = count.checked_mul(4)?;
    let end = usize::try_from(table_off.checked_add(byte_len)?).ok()?;
    if end > data.len() {
        return None;
    }
    Some((count, table_off))
}

#[expect(
    clippy::too_many_arguments,
    reason = "method decoder threads class context, string cache, and reusable cycle-guard set directly"
)]
fn decode_method_at(
    f: *const sys::AbcFileHandle,
    file_bytes: &[u8],
    method_off: u32,
    class_id: u32,
    class_source_file_off: u32,
    dialect: Dialect,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache<'_>,
    ann_visiting: &mut HashSet<u32>,
) -> Result<Method, Error> {
    // SAFETY: `f` is a live `AbcFileHandle`.
    let mr = unsafe { sys::abc_method_open(f, method_off) };
    if mr.is_null() {
        return Err(Error::InvalidOffset(method_off));
    }
    let _mg = HandleGuard(Some(|| {
        // SAFETY: `mr` is non-null and owned by this scope.
        unsafe { sys::abc_method_close(mr) };
    }));

    // SAFETY: `mr` is valid.
    let method_id = unsafe { sys::abc_method_get_method_id(mr) };

    let name = str_cache
        .intern_method_name(method_off, mr, strings)
        .ok_or_else(|| Error::Malformed {
            field: "name",
            context: format!("method at offset {method_id:#x}"),
        })?;

    // SAFETY: `mr` is valid.
    let raw_flags = unsafe { sys::abc_method_access_flags(mr) };
    let function_kind = decode_function_kind_from_flags(raw_flags)?;
    // SAFETY: `mr` is valid.
    let source_lang = decode_source_lang(unsafe { sys::abc_method_get_source_lang(mr) })?;

    let (body, byte_offsets, code_byte_len) = {
        // SAFETY: `mr` is valid.
        let code_off = unsafe { sys::abc_method_code_off(mr) };
        if code_off == ABSENT {
            (None, Vec::new(), 0)
        } else {
            let (b, bo, csize) = decode_code_at(
                f, method_off, code_off, dialect, entity_map, strings, str_cache,
            )?;
            (Some(b), bo, csize)
        }
    };

    let (return_type, arg_types) = {
        // SAFETY: `mr` is valid.
        let has_valid = unsafe { sys::abc_method_has_valid_proto(mr) } != 0;
        if !has_valid {
            (None, Vec::new())
        } else {
            // SAFETY: `mr` is valid.
            let proto_id = unsafe { sys::abc_method_get_proto_id(mr) };
            if proto_id == ABSENT {
                (None, Vec::new())
            } else {
                let (rt, at) = decode_proto_types(f, proto_id, entity_map, strings)?;
                (Some(rt), at)
            }
        }
    };

    let annotations = Annotations {
        compile_time: decode_annotation_list(
            f,
            &collect_offsets_int(
                mr,
                sys::abc_method_enumerate_annotations,
                "method_annotations",
                method_off,
            )?,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        runtime: decode_annotation_list(
            f,
            &collect_offsets_int(
                mr,
                sys::abc_method_enumerate_runtime_annotations,
                "method_annotations",
                method_off,
            )?,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        compile_time_type: decode_annotation_list(
            f,
            &collect_offsets_int(
                mr,
                sys::abc_method_enumerate_type_annotations,
                "method_annotations",
                method_off,
            )?,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        runtime_type: decode_annotation_list(
            f,
            &collect_offsets_int(
                mr,
                sys::abc_method_enumerate_runtime_type_annotations,
                "method_annotations",
                method_off,
            )?,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
    };

    // N55 + D2: decode debug info directly in Rust ONLY when the method
    // structurally carries a `DebugInfoItem`.
    // SAFETY: `mr` is valid.
    let debug_off = unsafe { sys::abc_method_debug_info_off(mr) };
    let debug = if debug_off == ABSENT {
        None
    } else {
        let mut sink = ModelDebugSink::new(strings);
        decode_method_debug_item(
            f,
            file_bytes,
            class_id,
            class_source_file_off,
            mr,
            code_byte_len,
            debug_off,
            &mut sink,
        )?;
        Some(sink.into_debug_info(&byte_offsets))
    };

    let param_annotations = decode_param_annotations(
        f,
        mr,
        arg_types.len(),
        entity_map,
        strings,
        str_cache,
        ann_visiting,
    )?;

    Ok(Method {
        name,
        offset: method_off,
        access_flags: AccessFlags::from_bits_truncate(raw_flags),
        function_kind,
        source_lang,
        is_external: is_external(f, method_id),
        return_type,
        arg_types,
        body,
        annotations,
        param_annotations,
        debug,
    })
}

fn decode_param_annotations(
    f: *const sys::AbcFileHandle,
    mr: *mut sys::AbcMethodAccessor,
    num_params: usize,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache<'_>,
    ann_visiting: &mut HashSet<u32>,
) -> Result<ParamAnnotations, Error> {
    let mut result = ParamAnnotations::default();
    // SAFETY: `mr` is valid.
    let ct_off = unsafe { sys::abc_method_get_param_annotation_id(mr) };
    // SAFETY: `mr` is valid.
    let rt_off = unsafe { sys::abc_method_get_runtime_param_annotation_id(mr) };
    for (is_runtime, item_off) in [(false, ct_off), (true, rt_off)] {
        if item_off == ABSENT {
            continue;
        }
        let mut pairs: Vec<(u32, u32)> = Vec::new();
        unsafe extern "C" fn cb(param_idx: u32, annotation_off: u32, ctx: *mut c_void) -> i32 {
            // SAFETY: `ctx` points to the caller's live `Vec<(u32, u32)>`.
            let pairs = unsafe { &mut *ctx.cast::<Vec<(u32, u32)>>() };
            pairs.push((param_idx, annotation_off));
            0
        }
        // SAFETY: `f` and `pairs` are live for the synchronous enumeration call.
        let rc = unsafe {
            sys::abc_param_annotations_enumerate(
                f,
                item_off,
                Some(cb),
                (&raw mut pairs).cast::<c_void>(),
            )
        };
        if rc != 0 {
            return Err(Error::Malformed {
                field: "param_annotations",
                context: format!("param annotations item at offset {item_off:#x}"),
            });
        }
        if pairs.is_empty() {
            continue;
        }
        let bucket = if is_runtime {
            &mut result.runtime
        } else {
            &mut result.compile_time
        };
        let max_end = pairs
            .iter()
            .try_fold(0usize, |acc, &(i, _)| {
                i.checked_add(1)
                    .and_then(|n| usize::try_from(n).ok())
                    .map(|n| acc.max(n))
            })
            .ok_or_else(|| Error::Malformed {
                field: "param_annotations",
                context: format!("param annotations item at offset {item_off:#x}"),
            })?;
        let len = num_params.max(max_end);
        bucket.resize(len, Vec::new());
        for (idx, off) in pairs {
            let anns =
                decode_annotation_list(f, &[off], entity_map, strings, str_cache, ann_visiting)?;
            bucket[idx as usize].extend(anns);
        }
    }
    Ok(result)
}

/// Descriptor of the record class whose u32 fields reference module-record
/// blobs (upstream name `_ESModuleRecord`: abc2program/common/
/// abc_file_utils.h `ES_MODULE_RECORD`; collection policy:
/// libpandafile/util/collect_util.h `ES_MODULE_RECORD`).
/// PIN STATUS (V-I1): the only in-cone vendor constant is private
/// (collect_util.h:40) and the public one (abc_file_utils.h) sits outside
/// the CI sparse cone, so no bridge export exists — this stays behaviorally
/// pinned by the module-record tests. The other three names are pinned via
/// `abc_vendor_*` exports (vendor_name_pins.rs).
pub const ES_MODULE_RECORD_DESCRIPTOR: &str = "L_ESModuleRecord;";
/// Descriptor of the record class whose u32 fields reference scope-names
/// literal arrays (upstream `_ESScopeNamesRecord`, same sources).
pub const ES_SCOPE_NAMES_RECORD_DESCRIPTOR: &str = "L_ESScopeNamesRecord;";

/// Name of the u32 field on a `--merge-abc` module record class whose value is
/// the file offset of an untagged `ModuleDataAccessor` blob (upstream
/// `es2panda` `Emitter::AddModuleRecord` `IsMergeAbc` branch; `abc2program`
/// `abc_field_processor.cpp` `MODULE_RECORD_IDX`; `libpandafile`
/// `collect_util.h` `MODULE_RECORD_IDX`).
pub const MODULE_RECORD_IDX_FIELD: &str = "moduleRecordIdx";

/// Name of the u32 field on a `--merge-abc` module record class whose value is
/// the file offset of a tagged scope-names literal array (vendored
/// `libpandabase/utils/const_value.h` `ark::SCOPE_NAMES`; `disassembler.cpp`
/// `GetMetadataFieldValue`; `abc_field_processor.cpp` `SCOPE_NAMES`).
pub const SCOPE_NAMES_FIELD: &str = "scopeNames";

/// Name of the u32 field on a `--merge-abc` JSON module record class whose
/// value is the file offset of the `StringItem` holding the JSON text
/// (`es2panda` `Emitter::GenJsonContentRecord`; `ecmascript/jspandafile`
/// `JSPandaFile::JSON_FILE_CONTENT`; `abc_field_processor.cpp`
/// `JSON_FILE_CONTENT`).
pub const JSON_FILE_CONTENT_FIELD: &str = "jsonFileContent";

/// Name of the u32 field whose value is the file offset of an untagged
/// module-request-phase blob (one u8 lazy-import flag per module request).
/// Matched by NAME, not by class: upstream's merge-abc mode emits the field
/// on the module's own record (es2panda emitter.cpp
/// `Emitter::AddModuleRequestPhaseRecord` IsMergeAbc branch), and the
/// vendored runtime/disassembler key on the name too
/// (js_pandafile.cpp:217 `LAZY_IMPORT`, disassembler.cpp:1007
/// `MODULE_REQUEST_PAHSE_IDX`).
pub const MODULE_REQUEST_PHASE_FIELD: &str = "moduleRequestPhaseIdx";

/// Name of the field whose non-zero value is the file offset of a tagged
/// `LiteralArray` whose elements include nested `LiteralTag::LITERALARRAY`
/// (`0x18`) references to per-type literal arrays (`arkcompiler_runtime_core`
/// 2022-08-18 ISA changelog item 5; `TYPE_SUMMARY_FIELD_NAME` in vendored
/// `libpandabase/utils/const_value.h`). OpenHarmony 4.x–5.x `es2abc` emits
/// the field on AbilityStage/Application and module records.
///
/// A zero wire value (`TYPE_SUMMARY_OFFSET_NOT_FOUND`) decodes as
/// [`FieldValue::I32`]`(0)`; a non-zero offset is validated as a well-formed
/// tagged literal array, seeded into `scope_names_offsets` so both the
/// summary array and its transitively nested type arrays enter
/// [`File::literal_arrays`], and modeled as [`FieldValue::LiteralArrayRef`]
/// for full relocation on `encode`.
pub const TYPE_SUMMARY_OFFSET_FIELD: &str = "typeSummaryOffset";

/// Decode a module-record blob through the vendored ModuleDataAccessor.
///
/// Layout (module_data_accessor.cpp ctor + module_data_accessor-inl.h
/// `EnumerateModuleRecord`): `[u32 item count]` (skipped by the accessor),
/// `[u32 num_module_requests][u32 request string offset]*`, then per-tag
/// sections (count + entries) in vendored order REGULAR_IMPORT,
/// NAMESPACE_IMPORT, LOCAL_EXPORT, INDIRECT_EXPORT, STAR_EXPORT. All name
/// fields are string entity offsets. Unreadable strings and unknown tags
/// are hard errors — module data is never silently dropped.
fn decode_module_data_at(
    f: *const sys::AbcFileHandle,
    offset: u32,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache<'_>,
) -> Result<ModuleData, Error> {
    let mut intern_str = |off: u32, pool: &mut StringPool| -> Result<StringId, Error> {
        str_cache
            .intern_utf8(off, pool)
            .ok_or(Error::InvalidString(off))
    };

    // SAFETY: `f` is a live `AbcFileHandle`.
    let mr = unsafe { sys::abc_module_open(f, offset) };
    if mr.is_null() {
        return Err(Error::InvalidOffset(offset));
    }
    let _mg = HandleGuard(Some(|| {
        // SAFETY: `mr` is non-null and owned by this scope.
        unsafe { sys::abc_module_close(mr) };
    }));

    // SAFETY: `f` and `mr` are valid.
    let file_size = unsafe { sys::abc_file_size(f) };
    // SAFETY: `mr` is valid.
    let num_requests = unsafe { sys::abc_module_num_requests(mr) };
    let cap = num_requests.min(file_size.saturating_sub(offset) / 4) as usize;
    let mut requests = Vec::with_capacity(cap);
    for i in 0..num_requests {
        // SAFETY: `mr` is valid and `i < num_requests`.
        let off = unsafe { sys::abc_module_request_off(mr, i) };
        if off == ABSENT {
            return Err(Error::InvalidString(off));
        }
        requests.push(intern_str(off, strings)?);
    }

    struct RawRecord {
        tag: u8,
        export_off: u32,
        request_idx: u32,
        import_off: u32,
        local_off: u32,
    }
    unsafe extern "C" fn collect_record(
        tag: u8,
        export_off: u32,
        request_idx: u32,
        import_off: u32,
        local_off: u32,
        ctx: *mut c_void,
    ) {
        // SAFETY: `ctx` points to the caller's live `Vec<RawRecord>`.
        unsafe { &mut *ctx.cast::<Vec<RawRecord>>() }.push(RawRecord {
            tag,
            export_off,
            request_idx,
            import_off,
            local_off,
        });
    }
    let mut raw: Vec<RawRecord> = Vec::new();
    // SAFETY: `mr` and `raw` are live for the synchronous enumeration call.
    let rc = unsafe {
        sys::abc_module_enumerate_records(mr, Some(collect_record), (&raw mut raw).cast::<c_void>())
    };
    if rc < 0 {
        return Err(Error::Malformed {
            field: "module_data",
            context: format!("truncated or malformed module record blob at {offset:#x}"),
        });
    }

    let mut records = Vec::with_capacity(raw.len());
    for rec in raw {
        let record = match rec.tag {
            t if t == sys::ModuleTag_REGULAR_IMPORT => ModuleRecord::RegularImport {
                local_name: intern_str(rec.local_off, strings)?,
                import_name: intern_str(rec.import_off, strings)?,
                module_request_idx: rec.request_idx,
            },
            t if t == sys::ModuleTag_NAMESPACE_IMPORT => ModuleRecord::NamespaceImport {
                local_name: intern_str(rec.local_off, strings)?,
                module_request_idx: rec.request_idx,
            },
            t if t == sys::ModuleTag_LOCAL_EXPORT => ModuleRecord::LocalExport {
                local_name: intern_str(rec.local_off, strings)?,
                export_name: intern_str(rec.export_off, strings)?,
            },
            t if t == sys::ModuleTag_INDIRECT_EXPORT => ModuleRecord::IndirectExport {
                export_name: intern_str(rec.export_off, strings)?,
                import_name: intern_str(rec.import_off, strings)?,
                module_request_idx: rec.request_idx,
            },
            t if t == sys::ModuleTag_STAR_EXPORT => ModuleRecord::StarExport {
                module_request_idx: rec.request_idx,
            },
            other => {
                return Err(Error::ModuleData(format!(
                    "unknown module record tag {other:#x} in blob at {offset:#x}"
                )));
            }
        };
        records.push(record);
    }

    Ok(ModuleData {
        source_offset: offset,
        requests,
        records,
    })
}

fn decode_module_request_phase_at(
    f: *const sys::AbcFileHandle,
    offset: u32,
) -> Result<crate::ModuleRequestPhase, Error> {
    let mut flags: Vec<u8> = Vec::new();
    unsafe extern "C" fn collect(flag: u8, ctx: *mut c_void) {
        // SAFETY: `ctx` points to the caller's live `Vec<u8>`.
        unsafe { &mut *ctx.cast::<Vec<u8>>() }.push(flag);
    }
    // SAFETY: `f` and `flags` are live for the synchronous read call.
    let n = unsafe {
        sys::abc_module_request_phase_read(
            f,
            offset,
            Some(collect),
            (&raw mut flags).cast::<c_void>(),
        )
    };
    if n < 0 {
        return Err(Error::ModuleData(format!(
            "module-request-phase blob at {offset:#x} is unreadable"
        )));
    }
    Ok(crate::ModuleRequestPhase {
        source_offset: offset,
        flags,
    })
}

#[inline]
fn field_first_tag(file_bytes: &[u8], field_off: u32, is_ext: bool) -> Option<u8> {
    if is_ext {
        return None;
    }
    let start = usize::try_from(field_off).ok()?.checked_add(8)?;
    let mut sp = file_bytes.get(start..)?;
    crate::file::read_uleb128_slice(&mut sp)?;
    sp.first().copied()
}

#[expect(
    clippy::too_many_arguments,
    reason = "field decoder threads distinct discovery-offset sets, string cache, and annotation cycle set directly"
)]
fn decode_field_at(
    f: *const sys::AbcFileHandle,
    file_bytes: &[u8],
    field_off: u32,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache<'_>,
    ann_visiting: &mut HashSet<u32>,
    class_descriptor: &str,
    module_data_offsets: &mut HashSet<u32>,
    scope_names_offsets: &mut HashSet<u32>,
    phase_blob_offsets: &mut HashSet<u32>,
) -> Result<Field, Error> {
    // SAFETY: `f` is a live `AbcFileHandle`.
    let fr = unsafe { sys::abc_field_open(f, field_off) };
    if fr.is_null() {
        return Err(Error::InvalidOffset(field_off));
    }
    let _fg = HandleGuard(Some(|| {
        // SAFETY: `fr` is non-null and owned by this scope.
        unsafe { sys::abc_field_close(fr) };
    }));

    // SAFETY: `fr` is valid.
    let field_id = unsafe { sys::abc_field_get_field_id(fr) };

    // SAFETY: `fr` is valid.
    let name_off = unsafe { sys::abc_field_name_off(fr) };
    let name = if name_off == ABSENT {
        return Err(Error::Malformed {
            field: "name",
            context: format!("field at offset {field_id:#x}"),
        });
    } else {
        str_cache
            .intern_lossy(name_off, strings)
            .ok_or_else(|| Error::Malformed {
                field: "name",
                context: format!("field at offset {field_id:#x}"),
            })?
    };

    // SAFETY: `fr` is valid.
    let type_raw = unsafe { sys::abc_field_type(fr) };
    // SAFETY: `fr` is valid.
    let type_id = TypeId::try_from(unsafe { sys::abc_field_type_id(fr) })?;
    let field_type = if type_id == TypeId::Reference {
        let type_sid = entity_map
            .get(&type_raw)
            .copied()
            .ok_or_else(|| Error::Malformed {
                field: "field_type",
                context: format!("field {:?}", strings.resolve(name).unwrap_or("?")),
            })?;
        Type::Reference(type_sid)
    } else {
        Type::from_raw(type_id, None)?
    };

    let initial_value = match type_id {
        TypeId::U1
        | TypeId::I8
        | TypeId::U8
        | TypeId::I16
        | TypeId::U16
        | TypeId::I32
        | TypeId::U32
        | TypeId::Tagged => {
            let mut v = 0i32;
            // SAFETY: `fr` is valid and `&mut v` is writable.
            if unsafe { sys::abc_field_get_value_i32(fr, &mut v) } != 0 {
                Some(FieldValue::I32(v))
            } else {
                None
            }
        }
        TypeId::I64 | TypeId::U64 => {
            let mut v = 0i64;
            // SAFETY: `fr` is valid and `&mut v` is writable.
            if unsafe { sys::abc_field_get_value_i64(fr, &mut v) } != 0 {
                Some(FieldValue::I64(v))
            } else {
                None
            }
        }
        TypeId::F32 => {
            let mut v = 0.0f32;
            // SAFETY: `fr` is valid and `&mut v` is writable.
            if unsafe { sys::abc_field_get_value_f32(fr, &mut v) } != 0 {
                Some(FieldValue::F32(v))
            } else {
                None
            }
        }
        TypeId::F64 => {
            let mut v = 0.0f64;
            // SAFETY: `fr` is valid and `&mut v` is writable.
            if unsafe { sys::abc_field_get_value_f64(fr, &mut v) } != 0 {
                Some(FieldValue::F64(v))
            } else {
                None
            }
        }
        TypeId::Void => None,
        TypeId::Reference => {
            let mut v = 0i32;
            // SAFETY: `fr` is valid and `&mut v` is writable.
            if unsafe { sys::abc_field_get_value_i32(fr, &mut v) } != 0 {
                let offset = v as u32;
                if offset == 0 {
                    return Err(Error::InvalidString(0));
                }
                let sid = str_cache
                    .intern_lossy(offset, strings)
                    .ok_or(Error::InvalidString(offset))?;
                Some(FieldValue::String(sid))
            } else {
                None
            }
        }
    };

    let is_ext = is_external(f, field_id);
    let initial_value = match (class_descriptor, type_id, initial_value) {
        (_, TypeId::U32, Some(FieldValue::I32(off)))
            if strings.resolve(name) == Some(TYPE_SUMMARY_OFFSET_FIELD) =>
        {
            let offset = off as u32;
            if offset == 0 {
                Some(FieldValue::I32(0))
            } else {
                if entity_map.contains_key(&offset)
                    // SAFETY: `f` is live; null callback performs structural validation only.
                    || unsafe {
                        sys::abc_literal_enumerate_vals_checked(
                            f,
                            offset,
                            None,
                            std::ptr::null_mut(),
                        )
                    } != 0
                {
                    return Err(Error::InvalidOffset(offset));
                }
                scope_names_offsets.insert(offset);
                Some(FieldValue::LiteralArrayRef {
                    index: LiteralArrayIdx(offset),
                    source_offset: Some(offset),
                })
            }
        }
        (_, TypeId::U32, Some(FieldValue::I32(off)))
            if strings.resolve(name) == Some(MODULE_REQUEST_PHASE_FIELD) =>
        {
            let offset = u32::try_from(off).map_err(|_| {
                Error::ModuleData(format!(
                    "{class_descriptor} field at {field_off:#x}: negative blob offset {off}"
                ))
            })?;
            let phase = decode_module_request_phase_at(f, offset).map_err(|e| {
                Error::ModuleData(format!(
                    "{class_descriptor} moduleRequestPhaseIdx field at {field_off:#x}: {e}"
                ))
            })?;
            phase_blob_offsets.insert(offset);
            Some(FieldValue::ModuleRequestPhase(phase))
        }
        (desc, TypeId::U32, Some(FieldValue::I32(off)))
            if desc == ES_MODULE_RECORD_DESCRIPTOR
                || strings.resolve(name) == Some(MODULE_RECORD_IDX_FIELD) =>
        {
            let offset = u32::try_from(off).map_err(|_| {
                Error::ModuleData(format!(
                    "{class_descriptor} field at {field_off:#x}: negative blob offset {off}"
                ))
            })?;
            let data = match decode_module_data_at(f, offset, strings, str_cache) {
                Ok(d) => d,
                Err(e @ Error::Malformed { .. }) => return Err(e),
                Err(e) => {
                    return Err(Error::ModuleData(format!(
                        "{class_descriptor} field at {field_off:#x}: {e}"
                    )));
                }
            };
            module_data_offsets.insert(offset);
            Some(FieldValue::ModuleData(data))
        }
        (desc, TypeId::U32, Some(FieldValue::I32(off)))
            if desc == ES_SCOPE_NAMES_RECORD_DESCRIPTOR
                || strings.resolve(name) == Some(SCOPE_NAMES_FIELD) =>
        {
            let offset = u32::try_from(off).map_err(|_| {
                Error::ModuleData(format!(
                    "{class_descriptor} field at {field_off:#x}: negative blob offset {off}"
                ))
            })?;
            scope_names_offsets.insert(offset);
            Some(FieldValue::LiteralArrayRef {
                index: LiteralArrayIdx(offset),
                source_offset: Some(offset),
            })
        }
        (_, TypeId::U32, Some(FieldValue::I32(off)))
            if strings.resolve(name) == Some(JSON_FILE_CONTENT_FIELD) =>
        {
            let offset = off as u32;
            if offset == 0 {
                return Err(Error::InvalidString(0));
            }
            let content = str_cache
                .intern_lossy(offset, strings)
                .ok_or(Error::InvalidString(offset))?;
            Some(FieldValue::JsonFileContent {
                source_offset: offset,
                content,
            })
        }
        (_, TypeId::U32, Some(FieldValue::I32(off)))
            if field_first_tag(file_bytes, field_off, is_ext) == Some(0x02) =>
        {
            let offset = off as u32;
            if offset == 0 {
                return Err(Error::InvalidString(0));
            }
            let sid = str_cache
                .intern_lossy(offset, strings)
                .ok_or(Error::InvalidString(offset))?;
            Some(FieldValue::String(sid))
        }
        (_, _, value) => value,
    };

    let annotations = Annotations {
        compile_time: decode_annotation_list(
            f,
            &collect_offsets_int(
                fr,
                sys::abc_field_enumerate_annotations,
                "field_annotations",
                field_off,
            )?,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        runtime: decode_annotation_list(
            f,
            &collect_offsets_int(
                fr,
                sys::abc_field_enumerate_runtime_annotations,
                "field_annotations",
                field_off,
            )?,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        compile_time_type: decode_annotation_list(
            f,
            &collect_offsets_int(
                fr,
                sys::abc_field_enumerate_type_annotations,
                "field_annotations",
                field_off,
            )?,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        runtime_type: decode_annotation_list(
            f,
            &collect_offsets_int(
                fr,
                sys::abc_field_enumerate_runtime_type_annotations,
                "field_annotations",
                field_off,
            )?,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
    };

    // SAFETY: `fr` is valid.
    let access_flags = AccessFlags::from_bits_truncate(unsafe { sys::abc_field_access_flags(fr) });
    Ok(Field {
        name,
        offset: field_off,
        field_type,
        access_flags,
        is_external: is_ext,
        initial_value,
        annotations,
    })
}

fn resolve_foreign_entity_name(
    f: *const sys::AbcFileHandle,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache<'_>,
    off: u32,
) -> StringId {
    if let Some(&sid) = entity_map.get(&off) {
        return sid;
    }
    // SAFETY: `f` is a live `AbcFileHandle`.
    let name_off = unsafe { sys::abc_foreign_item_name_off(f, off) };
    if name_off == ABSENT {
        return strings.get_or_intern("");
    }
    str_cache
        .intern_utf8(name_off, strings)
        .unwrap_or_else(|| strings.get_or_intern(""))
}

/// Returns `(MethodBody, byte_offsets)` where `byte_offsets[i]` is the byte
/// offset of instruction `i` in the raw bytecode.  The table is needed by
/// `read_debug_info` to convert debug byte-offsets to instruction indices.
fn decode_code_at(
    f: *const sys::AbcFileHandle,
    method_off: u32,
    code_off: u32,
    dialect: Dialect,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache<'_>,
) -> Result<(MethodBody, Vec<u32>, u32), Error> {
    // SAFETY: `f` is a live `AbcFileHandle`.
    let cr = unsafe { sys::abc_code_open(f, code_off) };
    if cr.is_null() {
        return Err(Error::InvalidOffset(code_off));
    }
    let _cg = HandleGuard(Some(|| {
        // SAFETY: `cr` is non-null and owned by this scope.
        unsafe { sys::abc_code_close(cr) };
    }));

    let raw_insns = {
        // SAFETY: `cr` is valid.
        let ptr = unsafe { sys::abc_code_instructions(cr) };
        // SAFETY: `cr` is valid.
        let len = unsafe { sys::abc_code_code_size(cr) } as usize;
        if ptr.is_null() || len == 0 {
            &[]
        } else {
            // SAFETY: `ptr` points to `len` validated bytes inside `f`'s buffer.
            unsafe { std::slice::from_raw_parts(ptr, len) }
        }
    };
    let decoded = match dialect {
        Dialect::DynamicLegacy => abcd_isa::decode_legacy(raw_insns),
        Dialect::DynamicModern => abcd_isa::decode(raw_insns),
        Dialect::Static => {
            return Err(Error::Malformed {
                field: "file_type",
                context: "static .abc bytecode cannot be decoded with dynamic ISA".into(),
            });
        }
    }
    .map_err(|source| Error::BytecodeDecode {
        method_offset: method_off,
        source,
    })?;

    let (bytecodes, byte_offsets): (Vec<_>, Vec<_>) = decoded.into_iter().unzip();
    let code_byte_len = raw_insns.len() as u32;

    let exact_pc_to_index = |pc: u32, field: &'static str, label: &str| -> Result<u32, Error> {
        if pc == code_byte_len {
            return Ok(bytecodes.len() as u32);
        }
        byte_offsets
            .binary_search(&pc)
            .map(|i| i as u32)
            .map_err(|_| Error::Malformed {
                field,
                context: format!(
                    "method at offset {method_off:#x}: {label} PC {pc:#x} is not on an instruction boundary"
                ),
            })
    };

    let raw_try_blocks = collect_try_blocks(f, method_off, cr)?;
    let mut try_blocks = Vec::with_capacity(raw_try_blocks.len());
    for tb in raw_try_blocks {
        let end_pc = tb
            .start
            .checked_add(tb.len)
            .ok_or_else(|| Error::Malformed {
                field: "try_block",
                context: format!("method at offset {method_off:#x}: try span overflow"),
            })?;
        let start = exact_pc_to_index(tb.start, "try_block", "try start")?;
        let end = exact_pc_to_index(end_pc, "try_block", "try end")?;
        let mut catches = Vec::with_capacity(tb.catches.len());
        for cb in tb.catches {
            let handler_end_pc =
                cb.handler
                    .checked_add(cb.len)
                    .ok_or_else(|| Error::Malformed {
                        field: "catch_block",
                        context: format!("method at offset {method_off:#x}: catch span overflow"),
                    })?;
            let handler = exact_pc_to_index(cb.handler, "catch_block", "catch handler")?;
            let handler_end = exact_pc_to_index(handler_end_pc, "catch_block", "catch end")?;
            let type_class = match cb.type_class_off {
                None => None,
                Some(class_off) => {
                    let sid = entity_map
                        .get(&class_off)
                        .copied()
                        .or_else(|| {
                            is_external(f, class_off)
                                .then(|| str_cache.intern_lossy(class_off, strings))
                                .flatten()
                        })
                        .ok_or_else(|| Error::Malformed {
                            field: "catch_block",
                            context: format!(
                                "method at offset {method_off:#x}: catch type offset {class_off:#x} names no class"
                            ),
                        })?;
                    Some(sid)
                }
            };
            catches.push(CatchBlock {
                type_class,
                handler,
                len: handler_end.saturating_sub(handler),
            });
        }
        try_blocks.push(TryBlock {
            start,
            len: end.saturating_sub(start),
            catches,
        });
    }

    // SAFETY: `cr` is valid.
    let num_vregs = unsafe { sys::abc_code_num_vregs(cr) };
    // SAFETY: `cr` is valid.
    let num_args = unsafe { sys::abc_code_num_args(cr) };

    Ok((
        MethodBody {
            num_vregs,
            num_args,
            bytecodes,
            entities: HashMap::new(),
            try_blocks,
            ic_size: None,
        },
        byte_offsets,
        code_byte_len,
    ))
}

fn decode_proto_types(
    f: *const sys::AbcFileHandle,
    proto_off: u32,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
) -> Result<(Type, Vec<Type>), Error> {
    // SAFETY: `f` is a live `AbcFileHandle`.
    let pr = unsafe { sys::abc_proto_open(f, proto_off) };
    if pr.is_null() {
        return Err(Error::InvalidOffset(proto_off));
    }
    let _pg = HandleGuard(Some(|| {
        // SAFETY: `pr` is non-null and owned by this scope.
        unsafe { sys::abc_proto_close(pr) };
    }));

    // SAFETY: `pr` is valid.
    let ref_num = unsafe { sys::abc_proto_get_ref_num(pr) };
    let mut next_ref = 0u32;
    let mut resolve = |raw: TypeId, ctx: &str| -> Result<Type, Error> {
        if raw == TypeId::Reference {
            if next_ref >= ref_num {
                return Err(Error::Malformed {
                    field: "reference_type",
                    context: ctx.to_string(),
                });
            }
            // SAFETY: `pr` is valid and `next_ref < ref_num`.
            let off = unsafe { sys::abc_proto_get_reference_type(pr, next_ref) };
            next_ref += 1;
            let desc = (off != u32::MAX)
                .then(|| entity_map.get(&off).copied())
                .flatten()
                .ok_or_else(|| Error::Malformed {
                    field: "reference_type",
                    context: ctx.to_string(),
                })?;
            Ok(Type::Reference(desc))
        } else {
            Type::from_raw(raw, None)
        }
    };

    // SAFETY: `pr` is valid.
    let raw_ret = TypeId::try_from(unsafe { sys::abc_proto_get_return_type(pr) })?;
    let return_type = resolve(raw_ret, "return type")?;

    unsafe extern "C" fn push_proto_type(raw: u8, ctx: *mut c_void) {
        // SAFETY: `ctx` points to the caller's live `Vec<u8>`.
        unsafe { &mut *ctx.cast::<Vec<u8>>() }.push(raw);
    }
    let mut enum_raw: Vec<u8> = Vec::new();
    // SAFETY: `pr` and `enum_raw` are live for the synchronous enumeration call.
    let rc = unsafe {
        sys::abc_proto_enumerate_types(
            pr,
            Some(push_proto_type),
            (&raw mut enum_raw).cast::<c_void>(),
        )
    };
    if rc < 0 || enum_raw.is_empty() {
        return Err(Error::Malformed {
            field: "proto",
            context: format!("proto at offset {proto_off:#x}: truncated or malformed shorty"),
        });
    }
    let arg_types = enum_raw[1..]
        .iter()
        .enumerate()
        .map(|(i, &raw_byte)| {
            let raw = TypeId::try_from(raw_byte)?;
            resolve(raw, &format!("arg {i}"))
        })
        .collect::<Result<Vec<_>, _>>()?;

    let _ = strings;

    Ok((return_type, arg_types))
}

fn decode_class_annotations(
    f: *const sys::AbcFileHandle,
    cr: *mut sys::AbcClassAccessor,
    class_off: u32,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache<'_>,
    ann_visiting: &mut HashSet<u32>,
) -> Result<Annotations, Error> {
    Ok(Annotations {
        compile_time: decode_annotation_list(
            f,
            &collect_offsets_int(
                cr,
                sys::abc_class_enumerate_annotations,
                "class_annotations",
                class_off,
            )?,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        runtime: decode_annotation_list(
            f,
            &collect_offsets_int(
                cr,
                sys::abc_class_enumerate_runtime_annotations,
                "class_annotations",
                class_off,
            )?,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        compile_time_type: decode_annotation_list(
            f,
            &collect_offsets_int(
                cr,
                sys::abc_class_enumerate_type_annotations,
                "class_annotations",
                class_off,
            )?,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        runtime_type: decode_annotation_list(
            f,
            &collect_offsets_int(
                cr,
                sys::abc_class_enumerate_runtime_type_annotations,
                "class_annotations",
                class_off,
            )?,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
    })
}

fn decode_annotation_list(
    f: *const sys::AbcFileHandle,
    offsets: &[u32],
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache<'_>,
    ann_visiting: &mut HashSet<u32>,
) -> Result<Vec<Annotation>, Error> {
    offsets
        .iter()
        .map(|&off| decode_annotation_at(f, off, entity_map, strings, str_cache, ann_visiting))
        .collect()
}

/// RAII wrapper for an open `AbcAnnotationAccessor` stored in an explicit
/// iterative decode frame.
struct OpenAnnotation(*mut sys::AbcAnnotationAccessor);

impl Drop for OpenAnnotation {
    fn drop(&mut self) {
        if !self.0.is_null() {
            // SAFETY: `self.0` was returned by `abc_annotation_open` and is non-null.
            unsafe { sys::abc_annotation_close(self.0) };
        }
    }
}

enum PendingAnnSlot {
    Scalar {
        name: StringId,
    },
    Array {
        name: StringId,
        tag: u8,
        remaining: std::vec::IntoIter<u32>,
        decoded: Vec<AnnotationValue>,
    },
}

struct AnnDecodeFrame {
    off: u32,
    ar: OpenAnnotation,
    class_descriptor: StringId,
    count: u32,
    next_idx: u32,
    elements: Vec<AnnotationElem>,
    pending: Option<PendingAnnSlot>,
}

fn open_ann_frame(
    f: *const sys::AbcFileHandle,
    off: u32,
    entity_map: &HashMap<u32, StringId>,
    visiting: &mut HashSet<u32>,
) -> Result<AnnDecodeFrame, Error> {
    if !visiting.insert(off) {
        return Err(Error::Malformed {
            field: "nested annotation",
            context: format!("cyclic annotation reference at offset {off:#x}"),
        });
    }
    // SAFETY: `f` is a live `AbcFileHandle`.
    let ar = unsafe { sys::abc_annotation_open(f, off) };
    if ar.is_null() {
        visiting.remove(&off);
        return Err(Error::InvalidOffset(off));
    }
    let ar = OpenAnnotation(ar);

    // SAFETY: `ar.0` is non-null and valid.
    let class_off = unsafe { sys::abc_annotation_class_off(ar.0) };
    let Some(class_descriptor) = entity_map.get(&class_off).copied() else {
        visiting.remove(&off);
        return Err(Error::Malformed {
            field: "class_descriptor",
            context: format!("annotation at offset {off:#x}"),
        });
    };

    // SAFETY: `ar.0` and `f` are valid.
    let count = unsafe { sys::abc_annotation_count(ar.0) };
    // SAFETY: `f` is valid; each annotation element occupies 9 bytes (`u32 name_off + u32 val + u8 tag`).
    let file_size = unsafe { sys::abc_file_size(f) };
    let max_elems = (file_size.saturating_sub(off) / 9) as usize;
    Ok(AnnDecodeFrame {
        off,
        ar,
        class_descriptor,
        count,
        next_idx: 0,
        elements: Vec::with_capacity((count as usize).min(max_elems)),
        pending: None,
    })
}

/// Decode one annotation tree rooted at `root_off` using an explicit
/// iterative workstack and active-path cycle detection.
fn decode_annotation_at(
    f: *const sys::AbcFileHandle,
    root_off: u32,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache<'_>,
    visiting: &mut HashSet<u32>,
) -> Result<Annotation, Error> {
    use sys::AnnotationValueType as AVT;

    visiting.clear();
    let mut stack: Vec<AnnDecodeFrame> = vec![open_ann_frame(f, root_off, entity_map, visiting)?];
    let mut completed: Option<Annotation> = None;

    while let Some(frame) = stack.last_mut() {
        if let Some(child_ann) = completed.take() {
            match frame.pending.take() {
                Some(PendingAnnSlot::Scalar { name }) => {
                    frame.elements.push(AnnotationElem {
                        name,
                        value: AnnotationValue::Annotation(Box::new(child_ann)),
                    });
                }
                Some(PendingAnnSlot::Array {
                    name,
                    tag,
                    mut remaining,
                    mut decoded,
                }) => {
                    decoded.push(AnnotationValue::Annotation(Box::new(child_ann)));
                    if let Some(next_off) = remaining.next() {
                        frame.pending = Some(PendingAnnSlot::Array {
                            name,
                            tag,
                            remaining,
                            decoded,
                        });
                        let child = open_ann_frame(f, next_off, entity_map, visiting)?;
                        stack.push(child);
                        continue;
                    }
                    frame.elements.push(AnnotationElem {
                        name,
                        value: AnnotationValue::Array {
                            tag,
                            values: decoded,
                        },
                    });
                }
                None => {}
            }
        }

        let mut next_child: Option<AnnDecodeFrame> = None;
        while frame.next_idx < frame.count {
            let idx = frame.next_idx;
            frame.next_idx += 1;
            let off = frame.off;
            let ar = frame.ar.0;

            let mut out = sys::AbcAnnotationElem {
                name_off: 0,
                tag: 0,
                value: 0,
            };
            // SAFETY: `ar` is valid and `&mut out` is writable.
            let rc = unsafe { sys::abc_annotation_get_element(ar, idx, &mut out) };
            if rc != 0 {
                return Err(Error::Malformed {
                    field: "annotation element",
                    context: format!("annotation at offset {off:#x}, element {idx}"),
                });
            }
            let name = str_cache
                .intern_utf8(out.name_off, strings)
                .ok_or(Error::InvalidString(out.name_off))?;
            let tag = AVT::try_from(out.tag).unwrap_or(AVT::Unknown);
            let value = match tag {
                AVT::U1 => AnnotationValue::Bool(out.value != 0),
                AVT::I8 => AnnotationValue::I8(out.value as i8),
                AVT::U8 => AnnotationValue::U8(out.value as u8),
                AVT::I16 => AnnotationValue::I16(out.value as i16),
                AVT::U16 => AnnotationValue::U16(out.value as u16),
                AVT::I32 => AnnotationValue::I32(out.value as i32),
                AVT::U32 => AnnotationValue::U32(out.value),
                AVT::I64 => {
                    let mut v = 0i64;
                    // SAFETY: `ar` is valid and `&mut v` is writable.
                    if unsafe { sys::abc_annotation_get_value_i64(ar, idx, &mut v) } == 0 {
                        AnnotationValue::I64(v)
                    } else {
                        return Err(Error::Malformed {
                            field: "annotation element value",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx} (tag {tag:?})"
                            ),
                        });
                    }
                }
                AVT::U64 => {
                    let mut v = 0u64;
                    // SAFETY: `ar` is valid and `&mut v` is writable.
                    if unsafe { sys::abc_annotation_get_value_u64(ar, idx, &mut v) } == 0 {
                        AnnotationValue::U64(v)
                    } else {
                        return Err(Error::Malformed {
                            field: "annotation element value",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx} (tag {tag:?})"
                            ),
                        });
                    }
                }
                AVT::F32 => AnnotationValue::F32(f32::from_bits(out.value)),
                AVT::F64 => {
                    let mut v = 0.0f64;
                    // SAFETY: `ar` is valid and `&mut v` is writable.
                    if unsafe { sys::abc_annotation_get_value_f64(ar, idx, &mut v) } == 0 {
                        AnnotationValue::F64(v)
                    } else {
                        return Err(Error::Malformed {
                            field: "annotation element value",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx} (tag {tag:?})"
                            ),
                        });
                    }
                }
                AVT::String => {
                    let sid = str_cache
                        .intern_utf8(out.value, strings)
                        .ok_or(Error::InvalidString(out.value))?;
                    AnnotationValue::String(sid)
                }
                AVT::Record => {
                    let sid = entity_map
                        .get(&out.value)
                        .copied()
                        .ok_or(Error::InvalidOffset(out.value))?;
                    AnnotationValue::Record(sid)
                }
                AVT::Method => {
                    let sid =
                        resolve_foreign_entity_name(f, entity_map, strings, str_cache, out.value);
                    AnnotationValue::Method {
                        name: sid,
                        method: None,
                        offset: out.value,
                    }
                }
                AVT::Enum => {
                    let sid =
                        resolve_foreign_entity_name(f, entity_map, strings, str_cache, out.value);
                    AnnotationValue::Enum {
                        name: sid,
                        field: None,
                        offset: out.value,
                    }
                }
                AVT::Annotation => {
                    frame.pending = Some(PendingAnnSlot::Scalar { name });
                    next_child = Some(open_ann_frame(f, out.value, entity_map, visiting)?);
                    break;
                }
                AVT::MethodHandle => {
                    let mut handle_type_raw = 0u8;
                    let mut entity_off = 0u32;
                    // SAFETY: `f` is live and out-pointers are writable.
                    let rc = unsafe {
                        sys::abc_method_handle_read(
                            f,
                            out.value,
                            &mut handle_type_raw,
                            &mut entity_off,
                        )
                    };
                    if rc != 0 {
                        return Err(Error::Malformed {
                            field: "method_handle",
                            context: format!("annotation at offset {off:#x}, element {idx}"),
                        });
                    }
                    let ht = MethodHandleType::from_u8(handle_type_raw).ok_or_else(|| {
                        Error::Malformed {
                            field: "method_handle_type",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx}: unknown handle type {handle_type_raw:#x}"
                            ),
                        }
                    })?;
                    let entity = entity_map
                        .get(&entity_off)
                        .copied()
                        .unwrap_or_else(|| strings.get_or_intern(""));
                    AnnotationValue::MethodHandle(ResolvedMethodHandle {
                        handle_type: ht,
                        entity,
                        target_method: None,
                        target_field: None,
                        entity_offset: entity_off,
                    })
                }
                AVT::LiteralArray => {
                    let values = decode_literal_array_at(f, out.value, strings)?;
                    AnnotationValue::LiteralArray(values)
                }
                AVT::Void => AnnotationValue::Void,
                AVT::StringNullptr => AnnotationValue::StringNullptr,
                AVT::ArrayAnnotation => {
                    let mut arr = sys::AbcAnnotationArrayVal {
                        count: 0,
                        entity_off: 0,
                    };
                    // SAFETY: `ar` is valid and `&mut arr` is writable.
                    if unsafe { sys::abc_annotation_get_array_element(ar, idx, &mut arr) } != 0 {
                        return Err(Error::Malformed {
                            field: "annotation array element",
                            context: format!("annotation at offset {off:#x}, element {idx}"),
                        });
                    }
                    let (_, raw_values) =
                        read_annotation_array_raw(f, out.tag, arr.count, arr.entity_off)?;
                    let mut offsets_iter = raw_values
                        .into_iter()
                        .map(|v| v as u32)
                        .collect::<Vec<_>>()
                        .into_iter();
                    if let Some(first_off) = offsets_iter.next() {
                        frame.pending = Some(PendingAnnSlot::Array {
                            name,
                            tag: out.tag,
                            decoded: Vec::with_capacity(offsets_iter.len().saturating_add(1)),
                            remaining: offsets_iter,
                        });
                        next_child = Some(open_ann_frame(f, first_off, entity_map, visiting)?);
                        break;
                    }
                    AnnotationValue::Array {
                        tag: out.tag,
                        values: Vec::new(),
                    }
                }
                AVT::Array
                | AVT::ArrayU1
                | AVT::ArrayI8
                | AVT::ArrayU8
                | AVT::ArrayI16
                | AVT::ArrayU16
                | AVT::ArrayI32
                | AVT::ArrayU32
                | AVT::ArrayI64
                | AVT::ArrayU64
                | AVT::ArrayF32
                | AVT::ArrayF64
                | AVT::ArrayString
                | AVT::ArrayRecord
                | AVT::ArrayMethod
                | AVT::ArrayEnum
                | AVT::ArrayMethodHandle => {
                    let mut arr = sys::AbcAnnotationArrayVal {
                        count: 0,
                        entity_off: 0,
                    };
                    // SAFETY: `ar` is valid and `&mut arr` is writable.
                    if unsafe { sys::abc_annotation_get_array_element(ar, idx, &mut arr) } != 0 {
                        return Err(Error::Malformed {
                            field: "annotation array element",
                            context: format!("annotation at offset {off:#x}, element {idx}"),
                        });
                    }
                    let values = decode_annotation_array_elements(
                        f,
                        out.tag,
                        arr.count,
                        arr.entity_off,
                        entity_map,
                        strings,
                        Some(str_cache),
                    )?;
                    AnnotationValue::Array {
                        tag: out.tag,
                        values,
                    }
                }
                AVT::Unknown => {
                    return Err(Error::Malformed {
                        field: "annotation element tag",
                        context: format!(
                            "annotation at offset {off:#x}, element {idx}: unknown tag {:#x}",
                            out.tag
                        ),
                    });
                }
            };
            frame.elements.push(AnnotationElem { name, value });
        }

        if let Some(child) = next_child {
            stack.push(child);
            continue;
        }

        let Some(finished) = stack.pop() else {
            break;
        };
        visiting.remove(&finished.off);
        let ann = Annotation {
            class_descriptor: finished.class_descriptor,
            elements: finished.elements,
        };
        if stack.is_empty() {
            return Ok(ann);
        }
        completed = Some(ann);
    }

    Err(Error::Malformed {
        field: "nested annotation",
        context: format!("annotation at offset {root_off:#x}"),
    })
}

/// Read the raw element words of an annotation array at `entity_offset`,
/// validating the tag's element width and payload span.
fn read_annotation_array_raw(
    f: *const sys::AbcFileHandle,
    tag: u8,
    count: u32,
    entity_offset: u32,
) -> Result<(sys::AnnotationValueType, Vec<u64>), Error> {
    use sys::AnnotationValueType as AVT;

    let avt = AVT::try_from(tag);
    let (avt, element_size): (AVT, u32) = match avt {
        Ok(t @ (AVT::ArrayU1 | AVT::ArrayI8 | AVT::ArrayU8)) => (t, 1),
        Ok(t @ (AVT::ArrayI16 | AVT::ArrayU16)) => (t, 2),
        Ok(
            t @ (AVT::ArrayI32
            | AVT::ArrayU32
            | AVT::ArrayF32
            | AVT::ArrayString
            | AVT::ArrayRecord
            | AVT::ArrayMethod
            | AVT::ArrayEnum
            | AVT::ArrayAnnotation
            | AVT::ArrayMethodHandle
            | AVT::LiteralArray),
        ) => (t, 4),
        Ok(t @ (AVT::ArrayI64 | AVT::ArrayU64 | AVT::ArrayF64)) => (t, 8),
        _ => {
            return Err(Error::Malformed {
                field: "annotation array element tag",
                context: format!(
                    "annotation array at offset {entity_offset:#x}: tag {tag:#x} has no defined element size"
                ),
            });
        }
    };

    if count == 0 {
        return Ok((avt, Vec::new()));
    }

    // SAFETY: `f` is a live `AbcFileHandle`.
    let file_size = unsafe { sys::abc_file_size(f) };
    let max_by_span = file_size.saturating_sub(entity_offset) / element_size;
    let alloc_count = count.min(max_by_span);
    let alloc_len = usize::try_from(alloc_count).map_err(|_| Error::Malformed {
        field: "annotation array data",
        context: format!("annotation array at offset {entity_offset:#x}"),
    })?;
    let mut raw_values = Vec::new();
    raw_values
        .try_reserve_exact(alloc_len)
        .map_err(|_| Error::Malformed {
            field: "annotation array data",
            context: format!("annotation array at offset {entity_offset:#x}"),
        })?;
    raw_values.resize(alloc_len, 0u64);
    // SAFETY: `f` is live and `raw_values` holds `alloc_count` writable `u64`s.
    let n = unsafe {
        sys::abc_annotation_array_read(
            f,
            entity_offset,
            element_size,
            count,
            raw_values.as_mut_ptr(),
            alloc_count,
        )
    };
    if n < 0 {
        return Err(Error::Malformed {
            field: "annotation array data",
            context: format!("annotation array at offset {entity_offset:#x}"),
        });
    }
    let n_u32 = n as u32;
    if n_u32 < count {
        return Err(Error::Malformed {
            field: "annotation array data",
            context: format!(
                "annotation array at offset {entity_offset:#x}: declared {count} elements, {n_u32} readable"
            ),
        });
    }
    raw_values.truncate(n_u32 as usize);
    Ok((avt, raw_values))
}

/// Resolve annotation array elements at the given entity offset.
fn decode_annotation_array_elements(
    f: *const sys::AbcFileHandle,
    tag: u8,
    count: u32,
    entity_offset: u32,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    mut str_cache: Option<&mut StringItemCache<'_>>,
) -> Result<Vec<AnnotationValue>, Error> {
    use sys::AnnotationValueType as AVT;

    let (avt, raw_values) = read_annotation_array_raw(f, tag, count, entity_offset)?;

    let mut out = Vec::with_capacity(raw_values.len());
    for raw in raw_values {
        let value = match avt {
            AVT::ArrayU1 => AnnotationValue::Bool(raw != 0),
            AVT::ArrayI8 => AnnotationValue::I8(raw as i8),
            AVT::ArrayU8 => AnnotationValue::U8(raw as u8),
            AVT::ArrayI16 => AnnotationValue::I16(raw as i16),
            AVT::ArrayU16 => AnnotationValue::U16(raw as u16),
            AVT::ArrayI32 => AnnotationValue::I32(raw as i32),
            AVT::ArrayU32 => AnnotationValue::U32(raw as u32),
            AVT::ArrayI64 => AnnotationValue::I64(raw as i64),
            AVT::ArrayU64 => AnnotationValue::U64(raw),
            AVT::ArrayF32 => AnnotationValue::F32(f32::from_bits(raw as u32)),
            AVT::ArrayF64 => AnnotationValue::F64(f64::from_bits(raw)),
            AVT::ArrayString => {
                let sid = if let Some(cache) = str_cache.as_deref_mut() {
                    cache
                        .intern_utf8(raw as u32, strings)
                        .ok_or(Error::InvalidString(raw as u32))?
                } else {
                    let s = read_string(f, raw as u32).ok_or(Error::InvalidString(raw as u32))?;
                    strings.get_or_intern(&s)
                };
                AnnotationValue::String(sid)
            }
            AVT::ArrayRecord => {
                let sid = entity_map
                    .get(&(raw as u32))
                    .copied()
                    .ok_or(Error::InvalidOffset(raw as u32))?;
                AnnotationValue::Record(sid)
            }
            AVT::ArrayMethod => {
                let sid = if let Some(cache) = str_cache.as_deref_mut() {
                    resolve_foreign_entity_name(f, entity_map, strings, cache, raw as u32)
                } else if let Some(&sid) = entity_map.get(&(raw as u32)) {
                    sid
                } else {
                    // SAFETY: `f` is live.
                    let name_off = unsafe { sys::abc_foreign_item_name_off(f, raw as u32) };
                    match (name_off != ABSENT)
                        .then(|| read_string(f, name_off))
                        .flatten()
                    {
                        Some(n) => strings.get_or_intern(&n),
                        None => strings.get_or_intern(""),
                    }
                };
                AnnotationValue::Method {
                    name: sid,
                    method: None,
                    offset: raw as u32,
                }
            }
            AVT::ArrayEnum => {
                let sid = if let Some(cache) = str_cache.as_deref_mut() {
                    resolve_foreign_entity_name(f, entity_map, strings, cache, raw as u32)
                } else if let Some(&sid) = entity_map.get(&(raw as u32)) {
                    sid
                } else {
                    // SAFETY: `f` is live.
                    let name_off = unsafe { sys::abc_foreign_item_name_off(f, raw as u32) };
                    match (name_off != ABSENT)
                        .then(|| read_string(f, name_off))
                        .flatten()
                    {
                        Some(n) => strings.get_or_intern(&n),
                        None => strings.get_or_intern(""),
                    }
                };
                AnnotationValue::Enum {
                    name: sid,
                    field: None,
                    offset: raw as u32,
                }
            }
            AVT::ArrayAnnotation => {
                return Err(Error::Malformed {
                    field: "annotation array element tag",
                    context: format!(
                        "annotation array at offset {entity_offset:#x}: nested ArrayAnnotation must be decoded iteratively"
                    ),
                });
            }
            AVT::LiteralArray => {
                AnnotationValue::LiteralArray(decode_literal_array_at(f, raw as u32, strings)?)
            }
            AVT::ArrayMethodHandle => {
                let mut handle_type_raw = 0u8;
                let mut entity_off = 0u32;
                // SAFETY: `f` is live and out-pointers are writable.
                let rc = unsafe {
                    sys::abc_method_handle_read(
                        f,
                        raw as u32,
                        &mut handle_type_raw,
                        &mut entity_off,
                    )
                };
                if rc != 0 {
                    return Err(Error::Malformed {
                        field: "method_handle",
                        context: format!("annotation array at offset {entity_offset:#x}"),
                    });
                }
                let ht = MethodHandleType::from_u8(handle_type_raw).ok_or_else(|| {
                    Error::Malformed {
                        field: "method_handle_type",
                        context: format!(
                            "annotation array at offset {entity_offset:#x}: unknown handle type {handle_type_raw:#x}"
                        ),
                    }
                })?;
                let entity = entity_map
                    .get(&entity_off)
                    .copied()
                    .unwrap_or_else(|| strings.get_or_intern(""));
                AnnotationValue::MethodHandle(ResolvedMethodHandle {
                    handle_type: ht,
                    entity,
                    target_method: None,
                    target_field: None,
                    entity_offset: entity_off,
                })
            }
            _ => {
                return Err(Error::Malformed {
                    field: "annotation array element tag",
                    context: format!(
                        "annotation array at offset {entity_offset:#x}: tag {tag:#x} has no value conversion"
                    ),
                });
            }
        };
        out.push(value);
    }
    Ok(out)
}

/// Decode a single literal array at the given entity offset, strictly
/// validating that `offset` points at a well-formed tagged literal array.
fn decode_literal_array_at(
    f: *const sys::AbcFileHandle,
    offset: u32,
    strings: &mut StringPool,
) -> Result<Vec<crate::LiteralValue>, Error> {
    let mut ctx = crate::literal::LiteralCollectCtx {
        file: f,
        strings: std::ptr::from_mut(strings),
        str_cache: None,
        values: Vec::new(),
        error: None,
    };
    // SAFETY: `f` and `ctx` are live for the synchronous enumeration call.
    let rc = unsafe {
        sys::abc_literal_enumerate_vals_checked(
            f,
            offset,
            Some(crate::literal::collect_literal_val_cb),
            (&raw mut ctx).cast::<c_void>(),
        )
    };
    if let Some(err) = ctx.error {
        return Err(err);
    }
    if rc != 0 {
        return Err(Error::InvalidOffset(offset));
    }
    Ok(ctx.values)
}

trait U32OffsetSet {
    fn contains_offset(&self, off: u32) -> bool;
}

impl U32OffsetSet for HashSet<u32> {
    #[inline]
    fn contains_offset(&self, off: u32) -> bool {
        self.contains(&off)
    }
}

impl U32OffsetSet for CompactU32Set {
    #[inline]
    fn contains_offset(&self, off: u32) -> bool {
        self.contains(off)
    }
}

/// Minimum byte offset past the 60-byte `panda_file::File::Header` where a
/// 4-byte `num_lit` count header of a tagged literal array can reside,
/// excluding untagged module-record and module-request-phase blobs.
fn is_plausible_literal_array_offset<S: U32OffsetSet>(
    off: u32,
    file_size: u32,
    module_data_offsets: &S,
    phase_blob_offsets: &S,
) -> bool {
    const HEADER_SIZE: u32 = 60;
    off != ABSENT
        && off >= HEADER_SIZE
        && u64::from(off) + 4 <= u64::from(file_size)
        && !module_data_offsets.contains_offset(off)
        && !phase_blob_offsets.contains_offset(off)
}

/// Seed `out` with plausible nested literal-array offsets found inside any
/// `AnnotationValue::LiteralArray` across the file (`LiteralArray`,
/// `LiteralBufferIndex`, and `ArrayU1..ArrayString`), using an explicit
/// iterative workstack.
fn collect_annotation_nested_literal_offsets(
    f: *const sys::AbcFileHandle,
    classes: &BTreeMap<StringId, Class>,
    file_size: u32,
    module_data_offsets: &HashSet<u32>,
    phase_blob_offsets: &HashSet<u32>,
    out: &mut HashSet<u32>,
) {
    fn push_annotations<'a>(anns: &'a Annotations, stack: &mut Vec<&'a AnnotationValue>) {
        for ann in anns
            .compile_time
            .iter()
            .chain(anns.runtime.iter())
            .chain(anns.compile_time_type.iter())
            .chain(anns.runtime_type.iter())
        {
            for elem in &ann.elements {
                stack.push(&elem.value);
            }
        }
    }

    let is_valid_lit_array = |cand: u32| -> bool {
        is_plausible_literal_array_offset(cand, file_size, module_data_offsets, phase_blob_offsets)
            // SAFETY: `f` is live; null callback performs structural validation only.
            && unsafe {
                sys::abc_literal_enumerate_vals_checked(f, cand, None, std::ptr::null_mut())
            } == 0
    };

    let mut stack: Vec<&AnnotationValue> = Vec::new();
    for class in classes.values() {
        push_annotations(&class.annotations, &mut stack);
        for method in &class.methods {
            push_annotations(&method.annotations, &mut stack);
            for anns in method
                .param_annotations
                .compile_time
                .iter()
                .chain(method.param_annotations.runtime.iter())
            {
                for ann in anns {
                    for elem in &ann.elements {
                        stack.push(&elem.value);
                    }
                }
            }
        }
        for field in &class.fields {
            push_annotations(&field.annotations, &mut stack);
        }
    }

    while let Some(val) = stack.pop() {
        match val {
            AnnotationValue::LiteralArray(values) => {
                for item in values {
                    match item {
                        LiteralValue::LiteralArray(idx)
                            if is_plausible_literal_array_offset(
                                idx.0,
                                file_size,
                                module_data_offsets,
                                phase_blob_offsets,
                            ) =>
                        {
                            out.insert(idx.0);
                        }
                        LiteralValue::LiteralBufferIndex(idx) if is_valid_lit_array(idx.0) => {
                            out.insert(idx.0);
                        }
                        _ => {}
                    }
                }
            }
            AnnotationValue::Annotation(inner) => {
                for elem in &inner.elements {
                    stack.push(&elem.value);
                }
            }
            AnnotationValue::Array { values, .. } => {
                for item in values {
                    stack.push(item);
                }
            }
            _ => {}
        }
    }
}

fn rewrite_literal_item_refs(
    v: &mut LiteralValue,
    offset_to_index: &HashMap<u32, u32>,
    array_count: usize,
    header_offsets: &[u32],
    method_offset_to_idx: &HashMap<u32, MethodIdx>,
) {
    if let Some(midx) = v.method_idx_mut() {
        *midx = method_offset_to_idx
            .get(&midx.0)
            .copied()
            .unwrap_or(MethodIdx(ABSENT));
        return;
    }
    match v {
        LiteralValue::LiteralArray(idx) => {
            if let Some(&table_idx) = offset_to_index.get(&idx.0) {
                idx.0 = table_idx;
            } else if (idx.0 as usize) < array_count {
                idx.0 = ABSENT;
            }
        }
        LiteralValue::LiteralBufferIndex(idx) => {
            if let Some(&hdr_off) = header_offsets.get(idx.0 as usize)
                && let Some(&table_idx) = offset_to_index.get(&hdr_off)
            {
                idx.0 = table_idx;
            } else if let Some(&table_idx) = offset_to_index.get(&idx.0) {
                idx.0 = table_idx;
            }
        }
        _ => {}
    }
}

/// Populate dense `MethodIdx` / `FieldIdx` / `LiteralArrayIdx` handles across
/// every `AnnotationValue` in `classes` using an explicit iterative workstack.
fn rewrite_annotation_refs(
    classes: &mut BTreeMap<StringId, Class>,
    offset_to_index: &HashMap<u32, u32>,
    literal_array_count: usize,
    header_offsets: &[u32],
    method_offset_to_idx: &HashMap<u32, MethodIdx>,
    field_offset_to_idx: &HashMap<u32, FieldIdx>,
) {
    fn push_annotations<'a>(anns: &'a mut Annotations, stack: &mut Vec<&'a mut AnnotationValue>) {
        for ann in anns
            .compile_time
            .iter_mut()
            .chain(anns.runtime.iter_mut())
            .chain(anns.compile_time_type.iter_mut())
            .chain(anns.runtime_type.iter_mut())
        {
            for elem in &mut ann.elements {
                stack.push(&mut elem.value);
            }
        }
    }

    let mut stack: Vec<&mut AnnotationValue> = Vec::new();
    for class in classes.values_mut() {
        push_annotations(&mut class.annotations, &mut stack);
        for method in &mut class.methods {
            push_annotations(&mut method.annotations, &mut stack);
            for anns in method
                .param_annotations
                .compile_time
                .iter_mut()
                .chain(method.param_annotations.runtime.iter_mut())
            {
                for ann in anns {
                    for elem in &mut ann.elements {
                        stack.push(&mut elem.value);
                    }
                }
            }
        }
        for field in &mut class.fields {
            push_annotations(&mut field.annotations, &mut stack);
        }
    }

    while let Some(val) = stack.pop() {
        match val {
            AnnotationValue::Method { method, offset, .. } => {
                *method = method_offset_to_idx.get(offset).copied();
            }
            AnnotationValue::Enum { field, offset, .. } => {
                *field = field_offset_to_idx.get(offset).copied();
            }
            AnnotationValue::MethodHandle(mh) => {
                if mh.handle_type.is_field_op() {
                    mh.target_field = field_offset_to_idx.get(&mh.entity_offset).copied();
                } else {
                    mh.target_method = method_offset_to_idx.get(&mh.entity_offset).copied();
                }
            }
            AnnotationValue::LiteralArray(values) => {
                for item in values {
                    rewrite_literal_item_refs(
                        item,
                        offset_to_index,
                        literal_array_count,
                        header_offsets,
                        method_offset_to_idx,
                    );
                }
            }
            AnnotationValue::Annotation(inner) => {
                for elem in &mut inner.elements {
                    stack.push(&mut elem.value);
                }
            }
            AnnotationValue::Array { values, .. } => {
                for item in values {
                    stack.push(item);
                }
            }
            _ => {}
        }
    }
}

/// The literal-array table decode result: the decoded arrays, the
/// file-offset → table-index map, and the raw header offsets (kept for
/// the pandasm emitter's byte-identity with upstream ark_disasm).
type LiteralArrayTable = (Vec<LiteralArray>, HashMap<u32, u32>, Vec<u32>);

#[expect(
    clippy::too_many_arguments,
    reason = "literal-array table builder threads offset sets, string cache, and method index map directly"
)]
fn decode_literal_arrays<'a>(
    f: *const sys::AbcFileHandle,
    file_size: u32,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache<'a>,
    referenced_offsets: &HashSet<u32>,
    module_data_offsets: &HashSet<u32>,
    phase_blob_offsets: &HashSet<u32>,
    method_offset_to_idx: &HashMap<u32, MethodIdx>,
) -> Result<LiteralArrayTable, Error> {
    // SAFETY: `f` is a live `AbcFileHandle`.
    let n = unsafe { sys::abc_file_num_literalarrays(f) };
    let mut header_offsets = Vec::new();
    let mut offsets = Vec::new();
    let mut seen = CompactU32Set::default();
    if n != 0 {
        for i in 0..n {
            // SAFETY: `f` is live and `i < n`.
            let off = unsafe { sys::abc_file_literalarray_offset(f, i) };
            if off != ABSENT {
                header_offsets.push(off);
            }
            if off != ABSENT
                && !module_data_offsets.contains(&off)
                && !phase_blob_offsets.contains(&off)
                && seen.insert(off)
            {
                offsets.push(off);
            }
        }
    }
    let mut referenced: Vec<u32> = referenced_offsets
        .iter()
        .copied()
        .filter(|&off| {
            off != ABSENT
                && !seen.contains(off)
                && !module_data_offsets.contains(&off)
                && !phase_blob_offsets.contains(&off)
        })
        .collect();
    referenced.sort_unstable();
    for off in referenced {
        if seen.insert(off) {
            offsets.push(off);
        }
    }
    if offsets.is_empty() {
        return Ok((Vec::new(), HashMap::new(), header_offsets));
    }

    let mut offset_to_index: HashMap<u32, u32> = HashMap::with_capacity(offsets.len());
    for (i, &off) in offsets.iter().enumerate() {
        offset_to_index.insert(off, i as u32);
    }

    let mut arrays: Vec<LiteralArray> = Vec::with_capacity(offsets.len());
    let mut decoded = 0usize;
    while decoded < offsets.len() {
        let mut nested: Vec<u32> = Vec::new();
        for &off in &offsets[decoded..] {
            let mut ctx = crate::literal::LiteralCollectCtx {
                file: f,
                strings: std::ptr::from_mut(strings),
                str_cache: Some(std::ptr::from_mut(str_cache)),
                values: Vec::new(),
                error: None,
            };
            // SAFETY: `f`, `strings`, `str_cache`, and `ctx` are live and unaliased
            // across this synchronous enumeration call.
            let rc = unsafe {
                sys::abc_literal_enumerate_vals_checked(
                    f,
                    off,
                    Some(crate::literal::collect_literal_val_cb),
                    (&raw mut ctx).cast::<c_void>(),
                )
            };
            if let Some(err) = ctx.error {
                return Err(err);
            }
            if rc != 0 {
                return Err(Error::InvalidOffset(off));
            }
            for value in &ctx.values {
                match value {
                    LiteralValue::LiteralArray(idx)
                        if is_plausible_literal_array_offset(
                            idx.0,
                            file_size,
                            module_data_offsets,
                            phase_blob_offsets,
                        ) && !seen.contains(idx.0) =>
                    {
                        nested.push(idx.0);
                    }
                    LiteralValue::LiteralBufferIndex(idx)
                        if is_plausible_literal_array_offset(
                            idx.0,
                            file_size,
                            module_data_offsets,
                            phase_blob_offsets,
                        ) && !seen.contains(idx.0)
                            // SAFETY: `f` is live; null callback validates structural array span.
                            && unsafe {
                                sys::abc_literal_enumerate_vals_checked(
                                    f,
                                    idx.0,
                                    None,
                                    std::ptr::null_mut(),
                                )
                            } == 0 =>
                    {
                        nested.push(idx.0);
                    }
                    _ => {}
                }
            }
            arrays.push(LiteralArray::with_source_offset(off, ctx.values));
        }
        decoded = offsets.len();
        nested.sort_unstable();
        nested.dedup();
        for off in nested {
            if seen.insert(off) {
                offset_to_index.insert(off, offsets.len() as u32);
                offsets.push(off);
            }
        }
    }

    let array_count = arrays.len();
    for arr in &mut arrays {
        for v in &mut arr.values {
            rewrite_literal_item_refs(
                v,
                &offset_to_index,
                array_count,
                &header_offsets,
                method_offset_to_idx,
            );
        }
    }
    Ok((arrays, offset_to_index, header_offsets))
}

fn read_class_descriptor_cached(
    cr: *const sys::AbcClassAccessor,
    class_id: u32,
    str_cache: &mut StringItemCache<'_>,
    strings: &mut StringPool,
) -> Option<(StringId, String)> {
    if let Some(sid) = str_cache.intern_utf8(class_id, strings) {
        let s = strings.resolve(sid).unwrap_or_default().to_owned();
        return Some((sid, s));
    }
    // SAFETY: `cr` is valid; returns null or a NUL-terminated descriptor inside `f`'s buffer.
    let ptr = unsafe { sys::abc_class_get_descriptor(cr) };
    if ptr.is_null() {
        return None;
    }
    // SAFETY: `ptr` is non-null and NUL-terminated inside `f`'s zero-padded buffer.
    let cstr = unsafe { CStr::from_ptr(ptr.cast::<std::os::raw::c_char>()) };
    let text = cstr.to_string_lossy().into_owned();
    let sid = strings.get_or_intern(&text);
    Some((sid, text))
}

// ---------------------------------------------------------------------------
// FFI helper: collect offsets via callbacks
// ---------------------------------------------------------------------------

/// Collect u32 offsets from a checked int-returning enumerate callback (`0` = ok, `< 0` = malformed).
fn collect_offsets_void<T>(
    raw: *mut T,
    enumerate: unsafe extern "C" fn(
        *mut T,
        Option<unsafe extern "C" fn(u32, *mut c_void)>,
        *mut c_void,
    ) -> std::os::raw::c_int,
    field: &'static str,
    owner_off: u32,
) -> Result<Vec<u32>, Error> {
    let mut result = Vec::new();
    unsafe extern "C" fn cb(offset: u32, ctx: *mut c_void) {
        // SAFETY: `ctx` points to the caller's live `Vec<u32>`.
        let vec = unsafe { &mut *ctx.cast::<Vec<u32>>() };
        vec.push(offset);
    }
    // SAFETY: `raw` and `result` are live for the synchronous enumeration call.
    let rc = unsafe { enumerate(raw, Some(cb), (&raw mut result).cast::<c_void>()) };
    if rc < 0 {
        return Err(Error::Malformed {
            field,
            context: format!("{field} enumeration failed at offset {owner_off:#x}"),
        });
    }
    Ok(result)
}

/// Collect u32 offsets from a checked int-returning annotation enumerate callback (`0` = ok, `< 0` = malformed).
fn collect_offsets_int<T>(
    raw: *mut T,
    enumerate: unsafe extern "C" fn(
        *mut T,
        Option<unsafe extern "C" fn(u32, *mut c_void) -> i32>,
        *mut c_void,
    ) -> std::os::raw::c_int,
    field: &'static str,
    owner_off: u32,
) -> Result<Vec<u32>, Error> {
    let mut result = Vec::new();
    unsafe extern "C" fn cb(offset: u32, ctx: *mut c_void) -> i32 {
        // SAFETY: `ctx` points to the caller's live `Vec<u32>`.
        let vec = unsafe { &mut *ctx.cast::<Vec<u32>>() };
        vec.push(offset);
        0
    }
    // SAFETY: `raw` and `result` are live for the synchronous enumeration call.
    let rc = unsafe { enumerate(raw, Some(cb), (&raw mut result).cast::<c_void>()) };
    if rc < 0 {
        return Err(Error::Malformed {
            field,
            context: format!("{field} enumeration failed at offset {owner_off:#x}"),
        });
    }
    Ok(result)
}

struct RawCatchBlock {
    type_class_off: Option<u32>,
    handler: u32,
    len: u32,
}

struct RawTryBlock {
    start: u32,
    len: u32,
    catches: Vec<RawCatchBlock>,
}

/// Collect try-blocks from a code accessor, strictly resolving typed catch
/// class indices to entity offsets.
fn collect_try_blocks(
    f: *const sys::AbcFileHandle,
    method_off: u32,
    cr: *mut sys::AbcCodeAccessor,
) -> Result<Vec<RawTryBlock>, Error> {
    struct Ctx {
        f: *const sys::AbcFileHandle,
        method_off: u32,
        blocks: Vec<RawTryBlock>,
        err: Option<Error>,
    }
    let mut ctx = Ctx {
        f,
        method_off,
        blocks: Vec::new(),
        err: None,
    };
    unsafe extern "C" fn cb(
        try_info: *const sys::AbcTryBlockInfo,
        catches: *const sys::AbcCatchBlockInfo,
        ctx_raw: *mut c_void,
    ) -> i32 {
        // SAFETY: `ctx_raw` points to the caller's live `Ctx`.
        let ctx = unsafe { &mut *ctx_raw.cast::<Ctx>() };
        if ctx.err.is_some() {
            return 0;
        }
        // SAFETY: `try_info` is a valid non-null pointer supplied by C++.
        let info = unsafe { &*try_info };
        let catch_slice = if info.num_catches > 0 {
            // SAFETY: `catches` holds `info.num_catches` contiguous entries during callback.
            unsafe { std::slice::from_raw_parts(catches, info.num_catches as usize) }
        } else {
            &[]
        };
        let mut decoded_catches = Vec::with_capacity(catch_slice.len());
        for c in catch_slice {
            let type_class_off = if c.type_idx == u32::MAX {
                None
            } else {
                let Ok(idx) = u16::try_from(c.type_idx) else {
                    ctx.err = Some(Error::InvalidOffset(c.type_idx));
                    return 0;
                };
                // SAFETY: `ctx.f` is a live `AbcFileHandle`.
                let resolved = unsafe { sys::abc_resolve_class_index(ctx.f, ctx.method_off, idx) };
                if resolved == ABSENT {
                    ctx.err = Some(Error::InvalidOffset(c.type_idx));
                    return 0;
                }
                Some(resolved)
            };
            decoded_catches.push(RawCatchBlock {
                type_class_off,
                handler: c.handler_pc,
                len: c.code_size,
            });
        }
        ctx.blocks.push(RawTryBlock {
            start: info.start_pc,
            len: info.length,
            catches: decoded_catches,
        });
        0
    }
    // SAFETY: `cr` is valid.
    let expected_tries = unsafe { sys::abc_code_tries_size(cr) };
    // SAFETY: `cr` and `ctx` are live for the synchronous enumeration call.
    let rc = unsafe {
        sys::abc_code_enumerate_try_blocks_full(cr, Some(cb), (&raw mut ctx).cast::<c_void>())
    };
    if let Some(err) = ctx.err {
        return Err(err);
    }
    if rc < 0 || ctx.blocks.len() != expected_tries as usize {
        return Err(Error::Malformed {
            field: "try_block",
            context: format!(
                "method at offset {method_off:#x}: truncated or malformed try/catch table"
            ),
        });
    }
    Ok(ctx.blocks)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Arm: annotation-array payload read failure (bridge
    /// `abc_annotation_array_read` returning < 0). This is unreachable
    /// through the public `decode` path: the caller's
    /// `abc_annotation_get_array_element` has already read the same span and
    /// ULEB count successfully, so the re-read here cannot fail for
    /// deterministic bytes. The arm is still loud (never a silent empty
    /// array); exercise it by calling the decoder directly with a dangling
    /// array offset.
    #[test]
    fn annotation_array_data_read_failure_is_hard_error() {
        let mut b = crate::Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, crate::types::SourceLang::EcmaScript);
        let proto = b.create_proto(crate::types::Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            crate::types::AccessFlags::PUBLIC,
            &[0x65],
            1,
            0,
        );
        b.method_set_source_lang(m, crate::types::SourceLang::EcmaScript);
        let data = b.finalize().expect("finalize");
        let abc = crate::file::AbcFile::open(&data).expect("open");
        let mut strings = StringPool::new();
        let entity_map = HashMap::new();
        // Tag 'Q' = ArrayU32 (element size 4); the offset dangles past EOF.
        let result = decode_annotation_array_elements(
            abc.raw,
            b'Q',
            1,
            0xFFFF_FF00,
            &entity_map,
            &mut strings,
            None,
        );
        assert!(
            matches!(
                result,
                Err(Error::Malformed {
                    field: "annotation array data",
                    ..
                })
            ),
            "expected Malformed/annotation array data, got: {result:?}"
        );
    }

    /// Arm: a literal array as an annotation ARRAY element ('#' inside the
    /// array-element converter). Upstream cannot represent arrays of
    /// literal arrays (pandasm `GetArrayTypeAsChar` has no '#' case), so no
    /// producer emits this and the public `decode` path never routes '#'
    /// here (the element dispatch treats '#' as the SCALAR literal-array
    /// tag). Drive the converter directly over a crafted payload.
    #[test]
    fn literal_array_as_array_element_decodes() {
        let mut b = crate::Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, crate::types::SourceLang::EcmaScript);
        // An array element whose payload is `[uleb 1][u32 string_off]` —
        // the exact layout the '#' arm reads.
        let s = b.add_string("probe_s");
        let name = b.add_string("e");
        let ann = b.create_annotation_ex(
            cls,
            &[crate::AnnotationElemDefEx {
                name,
                tag: b'V', // ArrayString
                value: crate::AnnotationElemValue::EntityArray(vec![s.as_raw()]),
            }],
        );
        b.class_add_runtime_annotation(cls, ann);
        let proto = b.create_proto(crate::types::Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            crate::types::AccessFlags::PUBLIC,
            &[0x65],
            1,
            0,
        );
        b.method_set_source_lang(m, crate::types::SourceLang::EcmaScript);
        let la = b.add_literal_array("la");
        b.literal_array_add_integer(la, 7);
        let mut data = b.finalize().expect("finalize");

        // The literal array's source offset, learned through a decode.
        let file = decode(&data).expect("decode");
        let la_off = file.literal_arrays[0]
            .source_offset
            .expect("literal array offset");

        // Find the annotation array payload: the string item offset of
        // "probe_s" preceded by the uleb count byte 0x01.
        let mut pat = vec![(7u8 << 1) | 1]; // "probe_s" is 7 ASCII chars
        pat.extend_from_slice(b"probe_s");
        pat.push(0);
        let str_off = data
            .windows(pat.len())
            .position(|w| w == pat.as_slice())
            .expect("string item") as u32;
        let payload_pos = data
            .windows(5)
            .position(|w| w[0] == 1 && w[1..5] == str_off.to_le_bytes())
            .expect("array payload") as u32;

        // Rewrite the element to hold the literal array's offset.
        data[payload_pos as usize + 1..payload_pos as usize + 5]
            .copy_from_slice(&la_off.to_le_bytes());

        let abc = crate::file::AbcFile::open(&data).expect("open");
        let mut strings = StringPool::new();
        let entity_map = HashMap::new();
        let result = decode_annotation_array_elements(
            abc.raw,
            b'#',
            1,
            payload_pos,
            &entity_map,
            &mut strings,
            None,
        )
        .expect("literal-array element must decode");
        assert_eq!(result.len(), 1);
        match &result[0] {
            AnnotationValue::LiteralArray(values) => {
                assert_eq!(values, &vec![crate::LiteralValue::Integer(7)]);
            }
            other => panic!("expected LiteralArray element, got {other:?}"),
        }
    }

    /// Arm: the '#' array-element converter propagates a dangling nested
    /// literal array loudly (the `?` inside the `Ok(AVT::LiteralArray)`
    /// arm). Same unreachable-through-decode reasoning as its sibling test
    /// above ('#' is the SCALAR literal-array tag in the element dispatch):
    /// drive the converter directly with a payload whose element dangles.
    #[test]
    fn literal_array_array_element_dangling_is_hard_error() {
        let mut b = crate::Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, crate::types::SourceLang::EcmaScript);
        let s = b.add_string("probe_s");
        let name = b.add_string("e");
        let ann = b.create_annotation_ex(
            cls,
            &[crate::AnnotationElemDefEx {
                name,
                tag: b'V', // ArrayString
                value: crate::AnnotationElemValue::EntityArray(vec![s.as_raw()]),
            }],
        );
        b.class_add_runtime_annotation(cls, ann);
        let proto = b.create_proto(crate::types::Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            crate::types::AccessFlags::PUBLIC,
            &[0x65],
            1,
            0,
        );
        b.method_set_source_lang(m, crate::types::SourceLang::EcmaScript);
        let mut data = b.finalize().expect("finalize");

        // Find the array payload (`[uleb 1][u32 string_off]`) and rewrite
        // the element to dangle past the declared file size.
        let mut pat = vec![(7u8 << 1) | 1]; // "probe_s" is 7 ASCII chars
        pat.extend_from_slice(b"probe_s");
        pat.push(0);
        let str_off = data
            .windows(pat.len())
            .position(|w| w == pat.as_slice())
            .expect("string item") as u32;
        let payload_pos = data
            .windows(5)
            .position(|w| w[0] == 1 && w[1..5] == str_off.to_le_bytes())
            .expect("array payload") as u32;
        let bogus = 0xFFFF_FF00u32;
        data[payload_pos as usize + 1..payload_pos as usize + 5]
            .copy_from_slice(&bogus.to_le_bytes());

        let abc = crate::file::AbcFile::open(&data).expect("open");
        let mut strings = StringPool::new();
        let entity_map = HashMap::new();
        let result = decode_annotation_array_elements(
            abc.raw,
            b'#',
            1,
            payload_pos,
            &entity_map,
            &mut strings,
            None,
        );
        assert!(
            matches!(result, Err(Error::InvalidOffset(o)) if o == bogus),
            "expected InvalidOffset({bogus:#x}), got: {result:?}"
        );
    }

    /// Arm: a declared element count that overruns the array's data span is
    /// a hard error, never a silent truncation (the bridge clamps the read
    /// to what the span holds and yields the short count). Reaching this
    /// through the public `decode` path would require the array payload to
    /// sit at the declared file end with every later-decoded item below it
    /// — the builder's item order never produces that — so drive the
    /// converter directly with an inflated count over a valid payload.
    #[test]
    fn annotation_array_short_read_is_hard_error() {
        let mut b = crate::Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, crate::types::SourceLang::EcmaScript);
        let s = b.add_string("probe_s");
        let name = b.add_string("e");
        let ann = b.create_annotation_ex(
            cls,
            &[crate::AnnotationElemDefEx {
                name,
                tag: b'V', // ArrayString
                value: crate::AnnotationElemValue::EntityArray(vec![s.as_raw()]),
            }],
        );
        b.class_add_runtime_annotation(cls, ann);
        let proto = b.create_proto(crate::types::Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            crate::types::AccessFlags::PUBLIC,
            &[0x65],
            1,
            0,
        );
        b.method_set_source_lang(m, crate::types::SourceLang::EcmaScript);
        let data = b.finalize().expect("finalize");

        // Find the array payload (`[uleb 1][u32 string_off]`).
        let mut pat = vec![(7u8 << 1) | 1]; // "probe_s" is 7 ASCII chars
        pat.extend_from_slice(b"probe_s");
        pat.push(0);
        let str_off = data
            .windows(pat.len())
            .position(|w| w == pat.as_slice())
            .expect("string item") as u32;
        let payload_pos = data
            .windows(5)
            .position(|w| w[0] == 1 && w[1..5] == str_off.to_le_bytes())
            .expect("array payload") as u32;

        let abc = crate::file::AbcFile::open(&data).expect("open");
        let mut strings = StringPool::new();
        let entity_map = HashMap::new();
        // Tag 'Q' = ArrayU32 (4-byte elements). The declared count vastly
        // overruns the span between the payload and the declared file end,
        // so the bridge yields fewer elements than declared.
        let result = decode_annotation_array_elements(
            abc.raw,
            b'Q',
            0xFFFF,
            payload_pos,
            &entity_map,
            &mut strings,
            None,
        );
        assert!(
            matches!(
                result,
                Err(Error::Malformed {
                    field: "annotation array data",
                    ..
                })
            ),
            "expected Malformed/annotation array data, got: {result:?}"
        );
    }

    #[test]
    fn legacy_literalarray_table_rejects_32bit_overflows() {
        let mut buf = vec![0u8; 128];
        let set_header = |buf: &mut [u8], count: u32, table_off: u32| {
            buf[44..48].copy_from_slice(&count.to_le_bytes());
            buf[48..52].copy_from_slice(&table_off.to_le_bytes());
        };

        // Valid table inside the buffer succeeds.
        set_header(&mut buf, 2, 60);
        assert_eq!(legacy_literalarray_table(&buf), Some((2, 60)));

        // Every 32-bit `u32`/`usize` overflow or out-of-bounds combination
        // returns `None` without panicking.
        for (count, table_off) in [
            (u32::MAX, u32::MAX),
            (u32::MAX, 60),
            (0x4000_0000, 0),
            (0x4000_0001, 60),
            (1, u32::MAX),
            (1, u32::MAX - 2),
            (0, u32::MAX),
            (0x2000_0001, 0x8000_0000),
        ] {
            set_header(&mut buf, count, table_off);
            assert_eq!(
                legacy_literalarray_table(&buf),
                None,
                "expected None for count={count:#x}, table_off={table_off:#x}"
            );
        }
    }

    #[test]
    fn annotation_array_32bit_overflowing_counts_are_hard_errors() {
        let mut b = crate::Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, crate::types::SourceLang::EcmaScript);
        let s = b.add_string("probe_s");
        let name = b.add_string("e");
        let ann = b.create_annotation_ex(
            cls,
            &[crate::AnnotationElemDefEx {
                name,
                tag: b'V',
                value: crate::AnnotationElemValue::EntityArray(vec![s.as_raw()]),
            }],
        );
        b.class_add_runtime_annotation(cls, ann);
        let proto = b.create_proto(crate::types::Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            crate::types::AccessFlags::PUBLIC,
            &[0x65],
            1,
            0,
        );
        b.method_set_source_lang(m, crate::types::SourceLang::EcmaScript);
        let data = b.finalize().expect("finalize");

        let mut pat = vec![(7u8 << 1) | 1];
        pat.extend_from_slice(b"probe_s");
        pat.push(0);
        let str_off = data
            .windows(pat.len())
            .position(|w| w == pat.as_slice())
            .expect("string item") as u32;
        let payload_pos = data
            .windows(5)
            .position(|w| w[0] == 1 && w[1..5] == str_off.to_le_bytes())
            .expect("array payload") as u32;

        let abc = crate::file::AbcFile::open(&data).expect("open");
        let mut strings = StringPool::new();
        let entity_map = HashMap::new();
        for bad_count in [0x4000_0001u32, u32::MAX] {
            let result = decode_annotation_array_elements(
                abc.raw,
                b'Q',
                bad_count,
                payload_pos,
                &entity_map,
                &mut strings,
                None,
            );
            assert!(
                matches!(
                    result,
                    Err(Error::Malformed {
                        field: "annotation array data",
                        ..
                    })
                ),
                "expected Malformed for count {bad_count:#x}, got: {result:?}"
            );
        }
    }

    #[test]
    fn compact_u32_set_iter_covers_rehash_and_max_sentinel() {
        let mut set = CompactU32Set::default();
        assert_eq!(set.iter().count(), 0);

        let mut expected: Vec<u32> = (0..100).map(|i| i * 97 + 13).collect();
        expected.push(0);
        expected.push(u32::MAX);
        for &v in &expected {
            assert!(set.insert(v));
            assert!(!set.insert(v));
            assert!(set.contains(v));
        }
        assert_eq!(set.len(), expected.len());

        let mut got: Vec<u32> = set.iter().collect();
        got.sort_unstable();
        expected.sort_unstable();
        assert_eq!(got, expected);
    }

    #[test]
    fn inspect_summary_zeropadded_parity_and_tail_validation() {
        let mut b = crate::Builder::new();
        b.set_api(12, "beta1");

        let _foreign_cls = b.add_foreign_class("LForeignBase;");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, crate::types::SourceLang::EcmaScript);
        let sf = b.add_string("entry.ts");
        b.class_set_source_file(cls, sf);

        // Nested tagged literal arrays + scope-names literal array.
        let la_leaf = b.add_literal_array("la_leaf");
        let leaf_str = b.add_string("leaf_val");
        b.literal_array_add_string(la_leaf, leaf_str);
        b.literal_array_add_integer(la_leaf, 42);

        let la_root = b.add_literal_array("la_root");
        b.literal_array_add_literalarray(la_root, la_leaf);

        let scope_la = b.add_literal_array("scope_la");
        let scope_str = b.add_string("local_x");
        b.literal_array_add_string(scope_la, scope_str);
        let scope_field = b.class_add_field(
            cls,
            SCOPE_NAMES_FIELD,
            crate::types::Type::U32,
            crate::types::AccessFlags::PUBLIC,
        );
        b.field_set_value_literalarray(scope_field, scope_la)
            .expect("scopeNames field");

        // Untagged module-record blob and module-request-phase blob (excluded from literal_arrays).
        let req = b.add_string("./dep");
        let imp = b.add_string("foo");
        let loc = b.add_string("foo_local");
        let mod_la = b.add_literal_array("mod_la");
        b.literal_array_add_module_data(
            mod_la,
            &[req],
            &[crate::ModuleRecordDef::RegularImport {
                local_name: loc,
                import_name: imp,
                module_request_idx: 0,
            }],
        )
        .expect("module data");
        let mod_field = b.class_add_field(
            cls,
            MODULE_RECORD_IDX_FIELD,
            crate::types::Type::U32,
            crate::types::AccessFlags::PUBLIC,
        );
        b.field_set_value_literalarray(mod_field, mod_la)
            .expect("moduleRecordIdx field");

        let phase_la = b.add_literal_array("phase_la");
        b.literal_array_add_module_request_phase(phase_la, &[1])
            .expect("phase blob");
        let phase_field = b.class_add_field(
            cls,
            MODULE_REQUEST_PHASE_FIELD,
            crate::types::Type::U32,
            crate::types::AccessFlags::PUBLIC,
        );
        b.field_set_value_literalarray(phase_field, phase_la)
            .expect("moduleRequestPhaseIdx field");

        let proto = b.create_proto(crate::types::Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            crate::types::AccessFlags::PUBLIC,
            &[0x65], // returnundefined
            1,
            0,
        );
        b.method_set_source_lang(m, crate::types::SourceLang::EcmaScript);

        let data = b.finalize().expect("finalize");
        let decoded = decode(&data).expect("decode");

        let mut padded = data.clone();
        padded.extend_from_slice(&[0u8; 16]);

        for verify in [false, true] {
            let expected = inspect_summary(&data, verify).expect("inspect_summary");
            let actual =
                inspect_summary_zeropadded(&padded, verify).expect("inspect_summary_zeropadded");
            assert_eq!(actual, expected, "parity mismatch for verify={verify}");
            assert_eq!(actual.classes, decoded.classes.len());
            assert_eq!(actual.literal_arrays, decoded.literal_arrays.len());
            assert_eq!(actual.strings, decoded.strings.len());
            assert!(
                actual.entity_index_entries
                    >= decoded.classes.len() + actual.methods + actual.fields
            );
        }

        // Every non-zero byte in the 16-byte trailing padding must be rejected.
        for tail_idx in 0..16 {
            let mut bad = padded.clone();
            bad[data.len() + tail_idx] = 0xAA;
            assert!(
                matches!(inspect_summary_zeropadded(&bad, false), Err(Error::Open(_))),
                "non-zero tail byte at {tail_idx} must fail"
            );
        }

        // Unpadded or short buffers must be rejected cleanly.
        for short in [&[][..], &[0u8; 15][..], &[0u8; 16][..], data.as_slice()] {
            assert!(matches!(
                inspect_summary_zeropadded(short, false),
                Err(Error::Open(_))
            ));
        }
    }
}
