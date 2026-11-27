//! Low-RSS streaming container inspector and verifier (`inspect_summary`,
//! `inspect_summary_zeropadded`) backed by `CompactU32Set` and SipHash-keyed
//! `SummaryStrings` (`#49`, `#77`).

use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::{BuildHasher, RandomState};

use abcd_file_sys as sys;
use hashbrown::HashTable;

use crate::debug::decode_method_debug_item;
use crate::error::Error;
use crate::file::{
    AbcReader, DecodedString, RawAnnotation, RawClass, RawField, RawFieldValue, RawMethod,
    RawModuleRecord,
};
use crate::literal::{LiteralWalkError, RawLiteralElem, walk_raw_literal_array};
use crate::model::MethodHandleType;
use crate::types::{Dialect, Type, TypeId};

use super::items::read_annotation_array_from_elem;
use super::{
    ABSENT, ES_MODULE_RECORD_DESCRIPTOR, ES_SCOPE_NAMES_RECORD_DESCRIPTOR, JSON_FILE_CONTENT_FIELD,
    MODULE_RECORD_IDX_FIELD, MODULE_REQUEST_PHASE_FIELD, SCOPE_NAMES_FIELD,
    TYPE_SUMMARY_OFFSET_FIELD, check_supported_dialect, decode_function_kind_from_flags,
    decode_source_lang, is_plausible_literal_array_offset, legacy_literalarray_table,
    probe_literal_array_valid,
};

// Lightweight Streaming Summary & Verifier (`inspect_summary`, `#77`)
// ---------------------------------------------------------------------------

/// Bytecode verification counts produced by [`inspect_summary`] when `verify` is `true`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifySummary {
    pub methods_checked: usize,
    pub instructions_decoded: usize,
}

/// Lightweight header and entity summary of an `.abc` file produced by
/// [`inspect_summary`] without materializing an owned [`crate::File`] in memory.
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

/// Compact open-addressed `u32` hash set (`u32::MAX` empty sentinel + `has_max` flag).
#[derive(Default)]
pub(super) struct CompactU32Set {
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
    pub(super) fn contains(&self, v: u32) -> bool {
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

    pub(super) fn insert(&mut self, v: u32) -> bool {
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum SymId {
    Utf8(u32),
    Lossy(u32),
}

/// SipHash-keyed flat-arena string deduplicator for [`inspect_summary`] (`#77`).
///
/// Replaces the former unkeyed FNV-1a `utf8_buckets` linear-probing table with
/// `hashbrown::HashTable<u32>` keyed by `std::hash::RandomState`, slicing
/// pre-validated UTF-8 text from `utf8_text` without redundant `from_utf8`
/// rescans on probe comparisons.
struct SummaryStrings {
    hasher: RandomState,
    utf8_text: String,
    utf8_offs: Vec<u32>,
    utf8_table: HashTable<u32>,
    raw_list: Vec<Box<[u8]>>,
    raw_table: HashTable<u32>,
    seen_lossy_offsets: CompactU32Set,
    seen_utf8_offsets: CompactU32Set,
    utf16_scratch: Vec<u16>,
}

impl SummaryStrings {
    fn new() -> Self {
        Self {
            hasher: RandomState::new(),
            utf8_text: String::new(),
            utf8_offs: vec![0],
            utf8_table: HashTable::new(),
            raw_list: Vec::new(),
            raw_table: HashTable::new(),
            seen_lossy_offsets: CompactU32Set::default(),
            seen_utf8_offsets: CompactU32Set::default(),
            utf16_scratch: Vec::with_capacity(64),
        }
    }

    #[inline]
    fn utf8_len(&self) -> usize {
        self.utf8_offs.len() - 1
    }

    #[inline]
    fn len(&self) -> usize {
        self.utf8_len() + self.raw_list.len()
    }

    #[inline]
    fn lossy_count(&self) -> usize {
        self.raw_list.len()
    }

    #[inline]
    fn utf8_slice<'a>(text: &'a str, offs: &[u32], id: u32) -> &'a str {
        let i = id as usize;
        let start = offs[i] as usize;
        let end = offs[i + 1] as usize;
        &text[start..end]
    }

    fn resolve_utf8(&self, sym: SymId) -> Option<&str> {
        match sym {
            SymId::Utf8(id) => {
                let i = id as usize;
                let start = *self.utf8_offs.get(i)? as usize;
                let end = *self.utf8_offs.get(i + 1)? as usize;
                self.utf8_text.get(start..end)
            }
            SymId::Lossy(_) => None,
        }
    }

    fn intern_utf8_str(&mut self, s: &str) -> Result<SymId, Error> {
        let hash = self.hasher.hash_one(s);
        let text_ref = &self.utf8_text;
        let offs_ref = &self.utf8_offs;
        if let Some(&existing) = self
            .utf8_table
            .find(hash, |&id| Self::utf8_slice(text_ref, offs_ref, id) == s)
        {
            return Ok(SymId::Utf8(existing));
        }

        let id = u32::try_from(self.utf8_len())
            .ok()
            .filter(|&x| x < u32::MAX)
            .ok_or_else(|| Error::Malformed {
                field: "string_pool",
                context: "summary string count exceeded u32::MAX".into(),
            })?;
        let end_off = self
            .utf8_text
            .len()
            .checked_add(s.len())
            .and_then(|n| u32::try_from(n).ok())
            .filter(|&x| x < u32::MAX)
            .ok_or_else(|| Error::Malformed {
                field: "string_pool",
                context: "summary UTF-8 arena exceeded u32::MAX bytes".into(),
            })?;

        self.utf8_text.push_str(s);
        self.utf8_offs.push(end_off);
        let hasher = &self.hasher;
        let text_after = &self.utf8_text;
        let offs_after = &self.utf8_offs;
        self.utf8_table.insert_unique(hash, id, |&existing_id| {
            hasher.hash_one(Self::utf8_slice(text_after, offs_after, existing_id))
        });
        Ok(SymId::Utf8(id))
    }

    fn intern_lossy_raw(&mut self, raw: &[u8]) -> Result<SymId, Error> {
        let hash = self.hasher.hash_one(raw);
        let raw_list = &self.raw_list;
        if let Some(&existing) = self
            .raw_table
            .find(hash, |&idx| &*raw_list[idx as usize] == raw)
        {
            return Ok(SymId::Lossy(existing));
        }
        let idx = u32::try_from(self.raw_list.len())
            .ok()
            .filter(|&x| x < u32::MAX)
            .ok_or_else(|| Error::Malformed {
                field: "string_pool",
                context: "summary lossy string count exceeded u32::MAX".into(),
            })?;
        self.raw_list.push(Box::from(raw));
        let hasher = &self.hasher;
        let raw_list_after = &self.raw_list;
        self.raw_table.insert_unique(hash, idx, |&existing_idx| {
            hasher.hash_one(&*raw_list_after[existing_idx as usize])
        });
        Ok(SymId::Lossy(idx))
    }

    fn intern_offset_lossy_sym(&mut self, reader: &AbcReader<'_>, offset: u32) -> Option<SymId> {
        let decoded = reader.read_string_item(offset, &mut self.utf16_scratch)?;
        let sym = match decoded {
            DecodedString::Utf8Borrowed(s) => self.intern_utf8_str(s).ok()?,
            DecodedString::Utf8Owned(s) => self.intern_utf8_str(&s).ok()?,
            DecodedString::LossyRaw { raw, .. } => self.intern_lossy_raw(raw).ok()?,
        };
        self.seen_lossy_offsets.insert(offset);
        Some(sym)
    }

    fn intern_offset_lossy(&mut self, reader: &AbcReader<'_>, offset: u32) -> bool {
        if self.seen_lossy_offsets.contains(offset) {
            return true;
        }
        self.intern_offset_lossy_sym(reader, offset).is_some()
    }

    fn intern_offset_utf8_sym(&mut self, reader: &AbcReader<'_>, offset: u32) -> Option<SymId> {
        let decoded = reader.read_string_item(offset, &mut self.utf16_scratch)?;
        let sym = match decoded {
            DecodedString::Utf8Borrowed(s) => self.intern_utf8_str(s).ok()?,
            DecodedString::Utf8Owned(s) | DecodedString::LossyRaw { lossy: s, .. } => {
                self.intern_utf8_str(&s).ok()?
            }
        };
        self.seen_utf8_offsets.insert(offset);
        Some(sym)
    }

    fn intern_offset_utf8(&mut self, reader: &AbcReader<'_>, offset: u32) -> bool {
        if self.seen_utf8_offsets.contains(offset) {
            return true;
        }
        self.intern_offset_utf8_sym(reader, offset).is_some()
    }

    fn intern_method_name(&mut self, reader: &AbcReader<'_>, name_off: u32) -> bool {
        if name_off == ABSENT {
            return false;
        }
        let Some(decoded) = reader.read_string_item(name_off, &mut self.utf16_scratch) else {
            return false;
        };
        match decoded {
            DecodedString::Utf8Borrowed(s) if !s.is_empty() => {
                self.seen_utf8_offsets.insert(name_off);
                self.seen_lossy_offsets.insert(name_off);
                self.intern_utf8_str(s).is_ok()
            }
            DecodedString::Utf8Owned(s) if !s.is_empty() => {
                self.seen_utf8_offsets.insert(name_off);
                self.seen_lossy_offsets.insert(name_off);
                self.intern_utf8_str(&s).is_ok()
            }
            _ => false,
        }
    }
}

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
/// [`crate::decode`] with minimal peak memory (`#49`, `#77`).
pub fn inspect_summary(data: &[u8], verify: bool) -> Result<FileSummary, Error> {
    let reader = AbcReader::open(data)?;
    inspect_summary_with_reader(&reader, data, verify)
}

/// Zero-copy counterpart to [`inspect_summary`] over a caller-owned slice
/// carrying `16` trailing zero padding bytes (`logical_data =
/// &padded_data[..padded_data.len() - 16]`).
pub fn inspect_summary_zeropadded(padded_data: &[u8], verify: bool) -> Result<FileSummary, Error> {
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
    };
    let logical_data = &padded_data[..logical_len];
    let reader = AbcReader::open(logical_data)?;
    inspect_summary_with_reader(&reader, logical_data, verify)
}

fn inspect_summary_with_reader(
    reader: &AbcReader<'_>,
    raw_data: &[u8],
    verify: bool,
) -> Result<FileSummary, Error> {
    let version = reader.version();
    let file_type = reader.file_type();
    let dialect = if verify {
        check_supported_dialect(file_type, version)?
    } else {
        Dialect::from_header(file_type, version).unwrap_or(Dialect::DynamicModern)
    };
    let legacy = dialect == Dialect::DynamicLegacy;
    let legacy_lit_table = if legacy {
        legacy_literalarray_table(reader.bytes())
    } else {
        None
    };
    let checksum = reader.checksum();
    let size = reader.file_size();

    let mut strings = SummaryStrings::new();

    // Pass 1: initial entity_map offsets (classes, methods, fields).
    let mut initial_entities = CompactU32Set::default();
    let mut valid_method_names = CompactU32Set::default();
    let num_classes = reader.num_classes();
    type StagedSummaryClass<'a> = (u32, Option<(RawClass<'a>, Vec<RawField>, Vec<RawMethod>)>);
    let mut staged_summary_classes: Vec<StagedSummaryClass<'_>> =
        Vec::with_capacity(num_classes.min((size / 4) as usize));

    for i in 0..num_classes {
        let class_off = reader.class_off_by_idx(i).unwrap_or(ABSENT);
        if class_off == ABSENT {
            return Err(Error::InvalidOffset(class_off));
        }
        if reader.is_external(class_off) {
            if strings.intern_offset_lossy(reader, class_off) {
                initial_entities.insert(class_off);
            }
            staged_summary_classes.push((class_off, None));
            continue;
        }
        let raw_cls = reader
            .open_class(class_off)
            .ok_or(Error::InvalidOffset(class_off))?;

        if read_class_descriptor_summary(reader, class_off, &mut strings).is_some() {
            initial_entities.insert(class_off);
        }
        let (raw_fields, raw_methods) =
            reader
                .enumerate_class_members(&raw_cls)
                .map_err(|()| Error::Malformed {
                    field: "class_members",
                    context: format!("class_members enumeration failed at offset {class_off:#x}"),
                })?;

        for m in &raw_methods {
            if strings.intern_method_name(reader, m.name_off) {
                valid_method_names.insert(m.offset);
                initial_entities.insert(m.offset);
            }
        }
        for fl in &raw_fields {
            if fl.name_off != ABSENT && strings.intern_offset_lossy(reader, fl.name_off) {
                initial_entities.insert(fl.offset);
            }
        }
        staged_summary_classes.push((class_off, Some((raw_cls, raw_fields, raw_methods))));
    }

    // Pass 2: stream classes, methods, fields, and annotations with zero retention.
    let mut classes: BTreeMap<SymId, ClassSummary> = BTreeMap::new();
    let mut extra_entities = CompactU32Set::default();
    let mut module_data_offsets = CompactU32Set::default();
    let mut scope_names_offsets = CompactU32Set::default();
    let mut phase_blob_offsets = CompactU32Set::default();
    let mut referenced_literal_offsets = CompactU32Set::default();
    let mut ann_nested_raw_targets: Vec<u32> = Vec::new();
    let mut ann_visiting: HashSet<u32> = HashSet::new();
    let mut ann_verified = CompactU32Set::default();
    let mut lnp_budget = crate::debug::initial_lnp_budget(size);
    let mut lit_probe_cache: HashMap<u32, bool> = HashMap::new();

    for (class_off, parsed_opt) in staged_summary_classes {
        let Some((raw_cls, raw_fields, raw_methods)) = parsed_opt else {
            if let Some(desc_sym) = strings.intern_offset_lossy_sym(reader, class_off) {
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
        };

        let Some(desc_sym) = read_class_descriptor_summary(reader, class_off, &mut strings) else {
            continue;
        };
        if classes.contains_key(&desc_sym) {
            let dup = strings.resolve_utf8(desc_sym).unwrap_or("?").to_owned();
            return Err(Error::Malformed {
                field: "class",
                context: format!("duplicate class descriptor {dup:?}"),
            });
        }
        if !strings.intern_offset_utf8(reader, class_off) {
            let desc_text = strings.resolve_utf8(desc_sym).unwrap_or("?").to_owned();
            return Err(Error::Malformed {
                field: "name",
                context: format!("class {desc_text}"),
            });
        }
        decode_source_lang(raw_cls.source_lang)?;
        let is_mod_rec_cls = strings.resolve_utf8(desc_sym) == Some(ES_MODULE_RECORD_DESCRIPTOR);
        let is_scope_rec_cls =
            strings.resolve_utf8(desc_sym) == Some(ES_SCOPE_NAMES_RECORD_DESCRIPTOR);

        let mut cls_summary = ClassSummary {
            is_external: false,
            ..ClassSummary::default()
        };

        for raw_m in &raw_methods {
            inspect_method_item(
                reader,
                raw_data,
                raw_m,
                class_off,
                raw_cls.source_file_off,
                dialect,
                legacy_lit_table,
                &valid_method_names,
                &initial_entities,
                &mut extra_entities,
                &mut strings,
                &mut referenced_literal_offsets,
                &mut ann_nested_raw_targets,
                &mut ann_visiting,
                &mut ann_verified,
                &mut lnp_budget,
                &mut lit_probe_cache,
                &mut cls_summary,
            )?;
        }

        for raw_f in &raw_fields {
            inspect_field_item(
                reader,
                raw_f,
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
                &mut ann_verified,
                &mut lit_probe_cache,
            )?;
            cls_summary.fields += 1;
        }

        for list in [
            &raw_cls.annotations,
            &raw_cls.runtime_annotations,
            &raw_cls.type_annotations,
            &raw_cls.runtime_type_annotations,
        ] {
            for &ann_off in list {
                inspect_annotation_at(
                    reader,
                    ann_off,
                    &initial_entities,
                    &mut strings,
                    &mut ann_nested_raw_targets,
                    &mut ann_visiting,
                    &mut ann_verified,
                    &mut lit_probe_cache,
                )?;
            }
        }

        if let Some(sf_off) = raw_cls.source_file_off {
            let _ = strings.intern_offset_utf8(reader, sf_off);
        }

        classes.insert(desc_sym, cls_summary);
    }

    for off in scope_names_offsets.iter() {
        referenced_literal_offsets.insert(off);
    }
    for target in ann_nested_raw_targets {
        if is_plausible_literal_array_offset(
            target,
            reader.header_size(),
            size,
            &module_data_offsets,
            &phase_blob_offsets,
        ) {
            referenced_literal_offsets.insert(target);
        }
    }

    let literal_arrays = count_literal_arrays_summary(
        reader,
        size,
        &mut strings,
        &referenced_literal_offsets,
        &module_data_offsets,
        &phase_blob_offsets,
        &mut lit_probe_cache,
    )?;

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
    reader: &AbcReader<'_>,
    class_off: u32,
    strings: &mut SummaryStrings,
) -> Option<SymId> {
    if let Some(sym) = strings.intern_offset_utf8_sym(reader, class_off) {
        return Some(sym);
    }
    let raw = reader.raw_cstr_at(class_off)?;
    let lossy = String::from_utf8_lossy(raw);
    strings.intern_utf8_str(&lossy).ok()
}

#[expect(
    clippy::too_many_arguments,
    reason = "streaming method inspector threads distinct summary accumulators without intermediate allocations"
)]
fn inspect_method_item(
    reader: &AbcReader<'_>,
    raw_data: &[u8],
    raw_m: &RawMethod,
    class_id: u32,
    class_source_file_off: Option<u32>,
    dialect: Dialect,
    legacy_lit_table: Option<(u32, u32)>,
    valid_method_names: &CompactU32Set,
    initial_entities: &CompactU32Set,
    extra_entities: &mut CompactU32Set,
    strings: &mut SummaryStrings,
    referenced_literal_offsets: &mut CompactU32Set,
    ann_nested_raw_targets: &mut Vec<u32>,
    ann_visiting: &mut HashSet<u32>,
    ann_verified: &mut CompactU32Set,
    lnp_budget: &mut usize,
    lit_probe_cache: &mut HashMap<u32, bool>,
    cls_summary: &mut ClassSummary,
) -> Result<(), Error> {
    let method_off = raw_m.offset;
    if !valid_method_names.contains(method_off)
        && !strings.intern_method_name(reader, raw_m.name_off)
    {
        return Err(Error::Malformed {
            field: "name",
            context: format!("method at offset {method_off:#x}"),
        });
    }

    if dialect != Dialect::Static {
        decode_function_kind_from_flags(raw_m.access_flags)?;
    }
    decode_source_lang(raw_m.source_lang)?;

    let mut code_size = 0u32;
    if let Some(code_off) = raw_m.code_off {
        cls_summary.methods_with_body += 1;
        if dialect != Dialect::Static {
            let (insns, csize) = inspect_code_at(
                reader,
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

    if let Some(proto_off) = reader.method_proto_off(raw_m) {
        inspect_proto_types(reader, proto_off, initial_entities)?;
    }

    for list in [
        &raw_m.annotations,
        &raw_m.runtime_annotations,
        &raw_m.type_annotations,
        &raw_m.runtime_type_annotations,
    ] {
        for &ann_off in list {
            inspect_annotation_at(
                reader,
                ann_off,
                initial_entities,
                strings,
                ann_nested_raw_targets,
                ann_visiting,
                ann_verified,
                lit_probe_cache,
            )?;
        }
    }

    if let Some(debug_off) = raw_m.debug_info_off {
        cls_summary.debug_infos += 1;
        let mut sink = SummaryDebugSink::new(strings);
        decode_method_debug_item(
            reader,
            class_id,
            class_source_file_off,
            raw_m,
            code_size,
            debug_off,
            lnp_budget,
            &mut sink,
        )?;
    }

    inspect_param_annotations(
        reader,
        raw_m,
        initial_entities,
        strings,
        ann_nested_raw_targets,
        ann_visiting,
        ann_verified,
        lit_probe_cache,
    )?;

    cls_summary.methods += 1;
    Ok(())
}

#[expect(
    clippy::too_many_arguments,
    reason = "streaming code inspector resolves operands directly into summary sets without allocating MethodBody"
)]
fn inspect_code_at(
    reader: &AbcReader<'_>,
    raw_data: &[u8],
    method_off: u32,
    code_off: u32,
    dialect: Dialect,
    legacy_lit_table: Option<(u32, u32)>,
    initial_entities: &CompactU32Set,
    extra_entities: &mut CompactU32Set,
    strings: &mut SummaryStrings,
    referenced_literal_offsets: &mut CompactU32Set,
) -> Result<(usize, u32), Error> {
    let legacy = dialect == Dialect::DynamicLegacy;
    let raw_code = reader
        .open_code(code_off)
        .ok_or(Error::InvalidOffset(code_off))?;
    let raw_insns = raw_code.instructions;

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

    validate_try_block_spans(
        reader,
        method_off,
        &raw_code,
        raw_insns.len() as u32,
        &decoded,
        initial_entities,
        strings,
    )?;

    let file_slice = reader.bytes();
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
            let offset = if legacy {
                match kind {
                    EntityKind::StringId => {
                        let off = id.0;
                        if off == 0 || (off as usize) >= raw_data.len() {
                            return Err(invalid());
                        }
                        off
                    }
                    EntityKind::MethodId => {
                        let index = u16::try_from(id.0).map_err(|_| invalid())?;
                        reader
                            .resolve_method_index(method_off, index)
                            .ok_or_else(invalid)?
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
                                    entry
                                        .checked_add(4)
                                        .and_then(|end| file_slice.get(entry..end))
                                })
                                .and_then(|s| s.try_into().ok())
                                .ok_or_else(invalid)?;
                        let off = u32::from_le_bytes(bytes);
                        if off == 0 || (off as usize) >= raw_data.len() {
                            return Err(invalid());
                        }
                        off
                    }
                }
            } else {
                let index = u16::try_from(id.0).map_err(|_| invalid())?;
                reader
                    .resolve_method_index(method_off, index)
                    .ok_or_else(invalid)?
            };

            if kind == EntityKind::LiteralarrayId {
                referenced_literal_offsets.insert(offset);
                continue;
            }
            if initial_entities.contains(offset) || extra_entities.contains(offset) {
                continue;
            }
            if kind == EntityKind::StringId {
                if !strings.intern_offset_lossy(reader, offset) {
                    return Err(invalid());
                }
                extra_entities.insert(offset);
                continue;
            }
            let rm = reader.open_method(offset).ok_or_else(invalid)?;
            if !strings.intern_method_name(reader, rm.name_off) {
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
                .and_then(|entry| {
                    entry
                        .checked_add(4)
                        .and_then(|end| file_slice.get(entry..end))
                })
                .and_then(|s| s.try_into().ok())
                .ok_or_else(invalid)?;
            let off = u32::from_le_bytes(bytes);
            if off == 0 || (off as usize) >= raw_data.len() {
                return Err(invalid());
            }
            referenced_literal_offsets.insert(off);
        }
    }

    Ok((insn_count, raw_insns.len() as u32))
}

fn validate_try_block_spans(
    reader: &AbcReader<'_>,
    method_off: u32,
    raw_code: &crate::file::RawCode<'_>,
    code_byte_len: u32,
    decoded: &[(abcd_isa::Bytecode, u32)],
    initial_entities: &CompactU32Set,
    strings: &mut SummaryStrings,
) -> Result<(), Error> {
    let check_pc = |pc: u32, field: &'static str, label: &str| -> Result<(), Error> {
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
    };

    let raw_tries = raw_code.read_try_blocks().ok_or_else(|| Error::Malformed {
        field: "try_block",
        context: format!(
            "method at offset {method_off:#x}: truncated or malformed try/catch table"
        ),
    })?;

    for tb in raw_tries {
        let end_pc = tb
            .start_pc
            .checked_add(tb.length)
            .ok_or_else(|| Error::Malformed {
                field: "try_block",
                context: format!("method at offset {method_off:#x}: try span overflow"),
            })?;
        check_pc(tb.start_pc, "try_block", "try start")?;
        check_pc(end_pc, "try_block", "try end")?;
        for c in tb.catches {
            let type_class_off = match c.type_idx {
                None => None,
                Some(idx) => {
                    let resolved = reader
                        .resolve_class_index(method_off, idx)
                        .ok_or(Error::InvalidOffset(u32::from(idx)))?;
                    Some(resolved)
                }
            };
            let handler_end =
                c.handler_pc
                    .checked_add(c.code_size)
                    .ok_or_else(|| Error::Malformed {
                        field: "catch_block",
                        context: format!("method at offset {method_off:#x}: catch span overflow"),
                    })?;
            check_pc(c.handler_pc, "catch_block", "catch handler")?;
            check_pc(handler_end, "catch_block", "catch end")?;
            if let Some(class_off) = type_class_off
                && !initial_entities.contains(class_off)
                && !(reader.is_external(class_off)
                    && strings.intern_offset_lossy(reader, class_off))
            {
                return Err(Error::Malformed {
                    field: "catch_block",
                    context: format!(
                        "method at offset {method_off:#x}: catch type offset {class_off:#x} names no class"
                    ),
                });
            }
        }
    }
    Ok(())
}

fn inspect_proto_types(
    reader: &AbcReader<'_>,
    proto_off: u32,
    initial_entities: &CompactU32Set,
) -> Result<usize, Error> {
    let Some(proto) = reader.open_proto(proto_off) else {
        return Err(Error::UnknownTypeId(u8::MAX));
    };
    let ref_num = proto.ref_types_sp.len() / 2;
    let mut next_ref = 0usize;
    let mut check_type = |raw: TypeId, ctx: &str| -> Result<(), Error> {
        if raw == TypeId::Reference {
            if next_ref >= ref_num {
                return Err(Error::Malformed {
                    field: "reference_type",
                    context: ctx.to_string(),
                });
            }
            let off = proto.reference_type_off(reader, next_ref);
            next_ref += 1;
            if !off.is_some_and(|o| initial_entities.contains(o)) {
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

    let raw_ret = TypeId::try_from(proto.return_type_raw())?;
    check_type(raw_ret, "return type")?;

    for idx in 0..proto.num_args() {
        let raw = TypeId::try_from(proto.arg_type_raw(idx))?;
        check_type(raw, &format!("arg {idx}"))?;
    }
    Ok(proto.num_args())
}

#[expect(
    clippy::too_many_arguments,
    reason = "streaming param annotation inspector threads summary sets and verified annotation cache"
)]
fn inspect_param_annotations(
    reader: &AbcReader<'_>,
    raw_m: &RawMethod,
    initial_entities: &CompactU32Set,
    strings: &mut SummaryStrings,
    ann_nested_raw_targets: &mut Vec<u32>,
    ann_visiting: &mut HashSet<u32>,
    ann_verified: &mut CompactU32Set,
    lit_probe_cache: &mut HashMap<u32, bool>,
) -> Result<(), Error> {
    for item_off_opt in [
        raw_m.param_annotations_off,
        raw_m.runtime_param_annotations_off,
    ] {
        let Some(item_off) = item_off_opt else {
            continue;
        };
        let pairs = reader
            .read_param_annotations(item_off)
            .ok_or_else(|| Error::Malformed {
                field: "param_annotations",
                context: format!("param annotations item at offset {item_off:#x}"),
            })?;
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
                reader,
                off,
                initial_entities,
                strings,
                ann_nested_raw_targets,
                ann_visiting,
                ann_verified,
                lit_probe_cache,
            )?;
        }
    }
    Ok(())
}

#[expect(
    clippy::too_many_arguments,
    reason = "streaming field inspector populates independent offset sets directly without allocating Field structs"
)]
fn inspect_field_item(
    reader: &AbcReader<'_>,
    raw_f: &RawField,
    class_desc_sym: SymId,
    is_mod_rec_cls: bool,
    is_scope_rec_cls: bool,
    initial_entities: &CompactU32Set,
    strings: &mut SummaryStrings,
    module_data_offsets: &mut CompactU32Set,
    scope_names_offsets: &mut CompactU32Set,
    phase_blob_offsets: &mut CompactU32Set,
    ann_nested_raw_targets: &mut Vec<u32>,
    ann_visiting: &mut HashSet<u32>,
    ann_verified: &mut CompactU32Set,
    lit_probe_cache: &mut HashMap<u32, bool>,
) -> Result<(), Error> {
    let field_off = raw_f.offset;
    let name_sym = if raw_f.name_off == ABSENT {
        return Err(Error::Malformed {
            field: "name",
            context: format!("field at offset {field_off:#x}"),
        });
    } else {
        strings
            .intern_offset_lossy_sym(reader, raw_f.name_off)
            .ok_or_else(|| Error::Malformed {
                field: "name",
                context: format!("field at offset {field_off:#x}"),
            })?
    };

    let type_id = raw_f.type_id;
    if type_id == TypeId::Reference {
        if !initial_entities.contains(raw_f.type_off) {
            let fname = strings.resolve_utf8(name_sym).unwrap_or("?").to_owned();
            return Err(Error::Malformed {
                field: "field_type",
                context: format!("field {fname:?}"),
            });
        }
    } else {
        Type::from_raw(type_id, None)?;
    }

    if type_id == TypeId::Reference
        && let Some(rv) = raw_f.raw_value
    {
        let offset = rv.as_u32();
        if offset == 0 || !strings.intern_offset_lossy(reader, offset) {
            return Err(Error::InvalidString(offset));
        }
    }

    if type_id == TypeId::U32
        && let Some(rv) = raw_f.raw_value
    {
        let off = rv.as_i32();
        let field_name = strings.resolve_utf8(name_sym);
        if field_name == Some(TYPE_SUMMARY_OFFSET_FIELD) {
            let offset = off as u32;
            if offset != 0 {
                if initial_entities.contains(offset)
                    || !probe_literal_array_valid(reader, offset, lit_probe_cache)
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
            if reader.read_module_request_phase(offset).is_none() {
                return Err(Error::ModuleData(format!(
                    "{class_desc} moduleRequestPhaseIdx field at {field_off:#x}: module-request-phase blob at {offset:#x} is unreadable"
                )));
            }
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
            match inspect_module_data_at(reader, offset, strings) {
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
            || matches!(rv, RawFieldValue::Bits32(_))
        {
            let offset = off as u32;
            if offset == 0 || !strings.intern_offset_lossy(reader, offset) {
                return Err(Error::InvalidString(offset));
            }
        }
    }

    for list in [&raw_f.annotations, &raw_f.runtime_annotations] {
        for &ann_off in list {
            inspect_annotation_at(
                reader,
                ann_off,
                initial_entities,
                strings,
                ann_nested_raw_targets,
                ann_visiting,
                ann_verified,
                lit_probe_cache,
            )?;
        }
    }
    Ok(())
}

fn inspect_module_data_at(
    reader: &AbcReader<'_>,
    offset: u32,
    strings: &mut SummaryStrings,
) -> Result<(), Error> {
    if reader.get_span(offset).is_none() {
        return Err(Error::InvalidOffset(offset));
    }
    let raw = reader
        .read_module_data(offset)
        .ok_or_else(|| Error::Malformed {
            field: "module_data",
            context: format!("truncated or malformed module record blob at {offset:#x}"),
        })?;
    for req_off in raw.request_offs {
        if req_off == ABSENT || !strings.intern_offset_utf8(reader, req_off) {
            return Err(Error::InvalidString(req_off));
        }
    }
    for rec in raw.records {
        match rec {
            RawModuleRecord::RegularImport {
                local_off,
                import_off,
                ..
            } => {
                if !strings.intern_offset_utf8(reader, local_off) {
                    return Err(Error::InvalidString(local_off));
                }
                if !strings.intern_offset_utf8(reader, import_off) {
                    return Err(Error::InvalidString(import_off));
                }
            }
            RawModuleRecord::NamespaceImport { local_off, .. } => {
                if !strings.intern_offset_utf8(reader, local_off) {
                    return Err(Error::InvalidString(local_off));
                }
            }
            RawModuleRecord::LocalExport {
                local_off,
                export_off,
            } => {
                if !strings.intern_offset_utf8(reader, local_off) {
                    return Err(Error::InvalidString(local_off));
                }
                if !strings.intern_offset_utf8(reader, export_off) {
                    return Err(Error::InvalidString(export_off));
                }
            }
            RawModuleRecord::IndirectExport {
                export_off,
                import_off,
                ..
            } => {
                if !strings.intern_offset_utf8(reader, export_off) {
                    return Err(Error::InvalidString(export_off));
                }
                if !strings.intern_offset_utf8(reader, import_off) {
                    return Err(Error::InvalidString(import_off));
                }
            }
            RawModuleRecord::StarExport { .. } => {}
        }
    }
    Ok(())
}

fn resolve_foreign_entity_name_summary(
    reader: &AbcReader<'_>,
    initial_entities: &CompactU32Set,
    strings: &mut SummaryStrings,
    off: u32,
) -> Result<(), Error> {
    if initial_entities.contains(off) {
        return Ok(());
    }
    let ok = reader
        .foreign_item_name_off(off)
        .is_some_and(|name_off| strings.intern_offset_utf8(reader, name_off));
    if !ok {
        strings.intern_utf8_str("")?;
    }
    Ok(())
}

struct SummaryAnnFrame<'a> {
    off: u32,
    ar: RawAnnotation<'a>,
    next_idx: u16,
    pending_array: Option<std::vec::IntoIter<u32>>,
}

fn open_summary_ann_frame<'a>(
    reader: &AbcReader<'a>,
    off: u32,
    initial_entities: &CompactU32Set,
    visiting: &mut HashSet<u32>,
) -> Result<SummaryAnnFrame<'a>, Error> {
    if !visiting.insert(off) {
        return Err(Error::Malformed {
            field: "nested annotation",
            context: format!("cyclic annotation reference at offset {off:#x}"),
        });
    }
    let Some(ar) = reader.open_annotation(off) else {
        visiting.remove(&off);
        return Err(Error::InvalidOffset(off));
    };
    if !initial_entities.contains(ar.class_off) {
        visiting.remove(&off);
        return Err(Error::Malformed {
            field: "class_descriptor",
            context: format!("annotation at offset {off:#x}"),
        });
    }
    Ok(SummaryAnnFrame {
        off,
        ar,
        next_idx: 0,
        pending_array: None,
    })
}

#[expect(
    clippy::too_many_arguments,
    reason = "streaming annotation inspector threads summary sets, verified DAG cache, and literal probe cache"
)]
fn inspect_annotation_at(
    reader: &AbcReader<'_>,
    root_off: u32,
    initial_entities: &CompactU32Set,
    strings: &mut SummaryStrings,
    ann_nested_raw_targets: &mut Vec<u32>,
    visiting: &mut HashSet<u32>,
    ann_verified: &mut CompactU32Set,
    lit_probe_cache: &mut HashMap<u32, bool>,
) -> Result<(), Error> {
    visiting.clear();
    if ann_verified.contains(root_off) {
        return Ok(());
    }
    let res = inspect_annotation_at_inner(
        reader,
        root_off,
        initial_entities,
        strings,
        ann_nested_raw_targets,
        visiting,
        ann_verified,
        lit_probe_cache,
    );
    if res.is_err() {
        visiting.clear();
    }
    res
}

#[expect(
    clippy::too_many_arguments,
    reason = "inner iterative annotation inspector threads summary sets, verified DAG cache, and literal probe cache"
)]
fn inspect_annotation_at_inner(
    reader: &AbcReader<'_>,
    root_off: u32,
    initial_entities: &CompactU32Set,
    strings: &mut SummaryStrings,
    ann_nested_raw_targets: &mut Vec<u32>,
    visiting: &mut HashSet<u32>,
    ann_verified: &mut CompactU32Set,
    lit_probe_cache: &mut HashMap<u32, bool>,
) -> Result<(), Error> {
    use sys::AnnotationValueType as AVT;

    let mut stack = vec![open_summary_ann_frame(
        reader,
        root_off,
        initial_entities,
        visiting,
    )?];

    while let Some(frame) = stack.last_mut() {
        if let Some(mut remaining) = frame.pending_array.take() {
            let mut pending_child: Option<SummaryAnnFrame<'_>> = None;
            for next_off in &mut remaining {
                if !visiting.contains(&next_off) && ann_verified.contains(next_off) {
                    continue;
                }
                frame.pending_array = Some(remaining);
                pending_child = Some(open_summary_ann_frame(
                    reader,
                    next_off,
                    initial_entities,
                    visiting,
                )?);
                break;
            }
            if let Some(child) = pending_child {
                stack.push(child);
                continue;
            }
        }

        let mut next_child: Option<SummaryAnnFrame<'_>> = None;
        while frame.next_idx < frame.ar.count {
            let idx = frame.next_idx;
            frame.next_idx += 1;
            let off = frame.off;

            let Some((name_off, raw_tag, val)) = frame.ar.element(idx) else {
                return Err(Error::Malformed {
                    field: "annotation element",
                    context: format!("annotation at offset {off:#x}, element {idx}"),
                });
            };
            if !strings.intern_offset_utf8(reader, name_off) {
                return Err(Error::InvalidString(name_off));
            }
            let tag = AVT::try_from(raw_tag).unwrap_or(AVT::Unknown);
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
                            "annotation at offset {off:#x}, element {idx}: unknown tag {raw_tag:#x}"
                        ),
                    });
                }
                AVT::I64 | AVT::U64 | AVT::F64 => {
                    if reader.read_scalar_u64(val).is_none() {
                        return Err(Error::Malformed {
                            field: "annotation element value",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx} (tag {tag:?})"
                            ),
                        });
                    }
                }
                AVT::String => {
                    if !strings.intern_offset_utf8(reader, val) {
                        return Err(Error::InvalidString(val));
                    }
                }
                AVT::Record => {
                    if !initial_entities.contains(val) {
                        return Err(Error::InvalidOffset(val));
                    }
                }
                AVT::Method | AVT::Enum => {
                    resolve_foreign_entity_name_summary(reader, initial_entities, strings, val)?;
                }
                AVT::Annotation => {
                    if !visiting.contains(&val) && ann_verified.contains(val) {
                        continue;
                    }
                    next_child = Some(open_summary_ann_frame(
                        reader,
                        val,
                        initial_entities,
                        visiting,
                    )?);
                    break;
                }
                AVT::MethodHandle => {
                    let Some((ht_raw, entity_off)) = reader.read_method_handle(val) else {
                        return Err(Error::Malformed {
                            field: "method_handle",
                            context: format!("annotation at offset {off:#x}, element {idx}"),
                        });
                    };
                    if MethodHandleType::from_u8(ht_raw).is_none() {
                        return Err(Error::Malformed {
                            field: "method_handle_type",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx}: unknown handle type {ht_raw:#x}"
                            ),
                        });
                    }
                    if !initial_entities.contains(entity_off) {
                        strings.intern_utf8_str("")?;
                    }
                }
                AVT::LiteralArray => {
                    inspect_checked_literal_array_at(
                        reader,
                        val,
                        strings,
                        ann_nested_raw_targets,
                        lit_probe_cache,
                    )?;
                }
                AVT::ArrayAnnotation => {
                    let (_, raw_values) =
                        read_annotation_array_from_elem(reader, off, idx, raw_tag, val, None)?;
                    let mut offsets_iter = raw_values
                        .into_iter()
                        .map(|v| v as u32)
                        .collect::<Vec<_>>()
                        .into_iter();
                    for cand_off in &mut offsets_iter {
                        if !visiting.contains(&cand_off) && ann_verified.contains(cand_off) {
                            continue;
                        }
                        frame.pending_array = Some(offsets_iter);
                        next_child = Some(open_summary_ann_frame(
                            reader,
                            cand_off,
                            initial_entities,
                            visiting,
                        )?);
                        break;
                    }
                    if next_child.is_some() {
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
                    let (avt, raw_values) =
                        read_annotation_array_from_elem(reader, off, idx, raw_tag, val, None)?;
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
                                if !strings.intern_offset_utf8(reader, raw as u32) {
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
                                    reader,
                                    initial_entities,
                                    strings,
                                    raw as u32,
                                )?;
                            }
                            AVT::ArrayMethodHandle => {
                                let Some((ht_raw, entity_off)) =
                                    reader.read_method_handle(raw as u32)
                                else {
                                    return Err(Error::Malformed {
                                        field: "method_handle",
                                        context: format!("annotation array at offset {val:#x}"),
                                    });
                                };
                                if MethodHandleType::from_u8(ht_raw).is_none() {
                                    return Err(Error::Malformed {
                                        field: "method_handle_type",
                                        context: format!(
                                            "annotation array at offset {val:#x}: unknown handle type {ht_raw:#x}"
                                        ),
                                    });
                                }
                                if !initial_entities.contains(entity_off) {
                                    strings.intern_utf8_str("")?;
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
        ann_verified.insert(finished.off);
        if stack.is_empty() {
            return Ok(());
        }
    }
    Ok(())
}

fn inspect_checked_literal_array_at(
    reader: &AbcReader<'_>,
    offset: u32,
    strings: &mut SummaryStrings,
    nested_out: &mut Vec<u32>,
    lit_probe_cache: &mut HashMap<u32, bool>,
) -> Result<(), Error> {
    let mut first_err: Option<Error> = None;
    let mut buf_indices: Vec<u32> = Vec::new();
    let walk = walk_raw_literal_array(reader, offset, |elem| {
        if first_err.is_some() {
            return Ok(());
        }
        match elem {
            RawLiteralElem::String(off) | RawLiteralElem::EtsImplements(off) => {
                if !strings.intern_offset_lossy(reader, off) {
                    let e = Error::InvalidString(off);
                    first_err = Some(e.clone());
                    return Err(e);
                }
            }
            RawLiteralElem::LiteralArray(off) => {
                nested_out.push(off);
            }
            RawLiteralElem::LiteralBufferIndex(off) => {
                buf_indices.push(off);
            }
            RawLiteralElem::TypedArray {
                tag: crate::literal::LiteralTag::ArrayString,
                elem_count,
                mut payload,
            } => {
                for _ in 0..elem_count {
                    let off = crate::file::read_u32_le(&mut payload).unwrap_or(0);
                    if !strings.intern_offset_lossy(reader, off) {
                        let e = Error::InvalidString(off);
                        first_err = Some(e.clone());
                        return Err(e);
                    }
                }
            }
            _ => {}
        }
        Ok(())
    });

    match walk {
        Ok(()) => {
            if let Some(e) = first_err {
                return Err(e);
            }
        }
        Err(LiteralWalkError::UnknownTag(t)) => {
            return Err(first_err.unwrap_or(Error::UnknownLiteralTag(t)));
        }
        Err(LiteralWalkError::Structural) => return Err(Error::InvalidOffset(offset)),
    }

    let header_size = reader.header_size();
    let file_size = reader.file_size();
    for cand in buf_indices {
        if cand != ABSENT
            && cand >= header_size
            && u64::from(cand) + 4 <= u64::from(file_size)
            && probe_literal_array_valid(reader, cand, lit_probe_cache)
        {
            nested_out.push(cand);
        }
    }
    Ok(())
}

fn count_literal_arrays_summary(
    reader: &AbcReader<'_>,
    file_size: u32,
    strings: &mut SummaryStrings,
    referenced_offsets: &CompactU32Set,
    module_data_offsets: &CompactU32Set,
    phase_blob_offsets: &CompactU32Set,
    lit_probe_cache: &mut HashMap<u32, bool>,
) -> Result<usize, Error> {
    let mut offsets = Vec::new();
    let mut seen = CompactU32Set::default();
    for off in reader.literal_array_offsets() {
        if off != ABSENT
            && !module_data_offsets.contains(off)
            && !phase_blob_offsets.contains(off)
            && seen.insert(off)
        {
            offsets.push(off);
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

    let header_size = reader.header_size();
    let mut decoded = 0usize;
    let mut raw_nested = Vec::new();
    while decoded < offsets.len() {
        let mut batch_nested = Vec::new();
        for &off in &offsets[decoded..] {
            raw_nested.clear();
            inspect_checked_literal_array_at(
                reader,
                off,
                strings,
                &mut raw_nested,
                lit_probe_cache,
            )?;
            for &target in &raw_nested {
                if is_plausible_literal_array_offset(
                    target,
                    header_size,
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

struct SummaryDebugSink<'s> {
    strings: &'s mut SummaryStrings,
    started_regs: HashSet<i32>,
}

impl<'s> SummaryDebugSink<'s> {
    fn new(strings: &'s mut SummaryStrings) -> Self {
        Self {
            strings,
            started_regs: HashSet::new(),
        }
    }

    #[inline]
    fn intern_required(&mut self, s: crate::debug::RawDebugStr<'_>) -> Result<(), Error> {
        match s {
            crate::debug::RawDebugStr::Empty => self.strings.intern_utf8_str("").map(|_| ()),
            crate::debug::RawDebugStr::Static(text) | crate::debug::RawDebugStr::Borrowed(text) => {
                self.strings.intern_utf8_str(text).map(|_| ())
            }
            crate::debug::RawDebugStr::Owned(text) => {
                self.strings.intern_utf8_str(&text).map(|_| ())
            }
        }
    }

    #[inline]
    fn intern_optional(&mut self, s: crate::debug::RawDebugStr<'_>) -> Result<(), Error> {
        match s {
            crate::debug::RawDebugStr::Empty => Ok(()),
            crate::debug::RawDebugStr::Static(text) | crate::debug::RawDebugStr::Borrowed(text) => {
                if text.is_empty() {
                    Ok(())
                } else {
                    self.strings.intern_utf8_str(text).map(|_| ())
                }
            }
            crate::debug::RawDebugStr::Owned(text) => {
                if text.is_empty() {
                    Ok(())
                } else {
                    self.strings.intern_utf8_str(&text).map(|_| ())
                }
            }
        }
    }
}

impl crate::debug::DebugSink for SummaryDebugSink<'_> {
    fn set_source_file(&mut self, s: crate::debug::RawDebugStr<'_>) -> Result<(), Error> {
        self.intern_optional(s)
    }

    fn set_source_code(&mut self, s: crate::debug::RawDebugStr<'_>) -> Result<(), Error> {
        self.intern_optional(s)
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
    ) -> Result<(), Error> {
        self.intern_required(name)?;
        self.intern_required(type_name)?;
        if let Some(sig) = type_sig {
            self.intern_required(sig)?;
        }
        self.started_regs.insert(reg_number);
        Ok(())
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
    ) -> Result<(), Error> {
        self.intern_required(name)?;
        self.intern_required(sig)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decode;

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
    fn summary_strings_siphash_dedup_and_lossy_separation() {
        let mut ss = SummaryStrings::new();
        for i in 0..2048u32 {
            let s = format!("fnv_probe_key_{i:04}");
            let a = ss.intern_utf8_str(&s).expect("intern");
            let b = ss.intern_utf8_str(&s).expect("re-intern");
            assert_eq!(a, b);
            assert_eq!(ss.resolve_utf8(a), Some(s.as_str()));
        }
        let lossy_a = ss.intern_lossy_raw(&[0xED, 0xA0, 0xB4]).expect("lossy a");
        let lossy_b = ss.intern_lossy_raw(&[0xED, 0xB4, 0x86]).expect("lossy b");
        let fffd = ss
            .intern_utf8_str("\u{FFFD}\u{FFFD}\u{FFFD}")
            .expect("fffd");
        assert_ne!(lossy_a, lossy_b);
        assert_ne!(lossy_a, fffd);
        assert_eq!(ss.lossy_count(), 2);
        assert_eq!(ss.len(), 2048 + 1 + 2);
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
            &[0x65],
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

        for tail_idx in 0..16 {
            let mut bad = padded.clone();
            bad[data.len() + tail_idx] = 0xAA;
            assert!(
                matches!(inspect_summary_zeropadded(&bad, false), Err(Error::Open(_))),
                "non-zero tail byte at {tail_idx} must fail"
            );
        }

        for short in [&[][..], &[0u8; 15][..], &[0u8; 16][..], data.as_slice()] {
            assert!(matches!(
                inspect_summary_zeropadded(short, false),
                Err(Error::Open(_))
            ));
        }
    }
}
