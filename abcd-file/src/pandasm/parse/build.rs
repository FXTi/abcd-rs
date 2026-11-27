//! Semantic `File` model assembly from the syntactic `Pa*` parse tree:
//! record/field/module materialization, opcode-driven operand typing,
//! register/label/try-catch resolution, and 13.x/24.x literal index recovery.

use std::collections::{BTreeMap, HashMap};
use std::sync::OnceLock;

use abcd_isa::{BytecodeFlags, EntityKind};

use crate::model::{
    Annotation, AnnotationElem, AnnotationValue, Annotations, CatchBlock, Class, EntityRef, Field,
    FieldValue, File, LiteralArray, Method, MethodBody, MethodIdx, ModuleData, ModuleRecord,
    ModuleRequestPhase, ParamAnnotations, TryBlock,
};
use crate::types::{AccessFlags, FunctionKind, SourceLang, Type};
use crate::{LiteralArrayIdx, LiteralValue, StringId};

use super::super::insn_ctor;
use super::{
    LAST_HEADER_LITERAL_VERSION, PaElemValue, PaField, PaFunction, PaItem, PaLiteral, PaModule,
    PaModuleRecord, PaOp, PaRecord, ParseError, Parser, RawOperand, SYNTHETIC_OFFSET_BASE, err,
    lossy,
};

// Instruction operand spec (runtime-discovered from the vendored ISA)
// ---------------------------------------------------------------------------

/// How one operand position of a mnemonic is typed (upstream
/// `opcode_parsing.h.erb`: opcode-driven operand kinds).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OpKind {
    Reg,
    Imm,
    /// Float immediate (the FLOAT flag): the text is a decimal rendering.
    ImmFloat,
    Label,
    Str,
    Method,
    LiteralArr,
}

struct InsnSpec {
    kinds: Vec<OpKind>,
}

/// The spec table, built once by constructing a zero-valued instance of
/// every mnemonic and reading the operand kinds / FLOAT flag back.
fn insn_specs() -> &'static HashMap<&'static str, InsnSpec> {
    static SPECS: OnceLock<HashMap<&'static str, InsnSpec>> = OnceLock::new();
    SPECS.get_or_init(|| {
        let mut map = HashMap::new();
        for &mnemonic in insn_ctor::MNEMONICS {
            let Some(bc) = insn_ctor::dummy(mnemonic) else {
                continue;
            };
            let float = bc.has_flag(BytecodeFlags::FLOAT);
            let kinds = bc
                .operands()
                .iter()
                .map(|op| match *op {
                    abcd_isa::Operand::Reg(_) => OpKind::Reg,
                    abcd_isa::Operand::Imm(_) => {
                        if float {
                            OpKind::ImmFloat
                        } else {
                            OpKind::Imm
                        }
                    }
                    abcd_isa::Operand::Label(_) => OpKind::Label,
                    abcd_isa::Operand::Entity(kind, _) => match kind {
                        EntityKind::StringId => OpKind::Str,
                        EntityKind::MethodId => OpKind::Method,
                        EntityKind::LiteralarrayId => OpKind::LiteralArr,
                    },
                })
                .collect();
            map.insert(mnemonic, InsnSpec { kinds });
        }
        map
    })
}

impl Parser {
    // -- model construction ---------------------------------------------------

    pub(super) fn build(mut self) -> Result<File, ParseError> {
        let mut b = BuildCtx::default();
        // Detach the section data so the interning loops below can take
        // `&mut self` while iterating.
        let records = std::mem::take(&mut self.records);
        let functions = std::mem::take(&mut self.functions);

        // Records → classes (fields resolved below; methods attached when
        // functions are built). Descriptors intern in BYTE-SORTED order —
        // the file's class-index order, which is also the decode-time
        // interning order; the 13.x/24.x literal-table index assignment
        // (emitter's unordered_set simulation) depends on the class
        // iteration order that interning order induces.
        //
        // `_GLOBAL` (a system record) is never printed; synthesize it up
        // front when any function's name matches no printed record prefix,
        // so it takes its sorted place among the descriptors.
        let needs_global = functions
            .iter()
            .any(|f| record_prefix_of(&f.name, &records).is_none());
        let mut descriptors: Vec<Vec<u8>> =
            records.iter().map(|r| record_descriptor(&r.name)).collect();
        if needs_global {
            descriptors.push(b"L_GLOBAL;".to_vec());
        }
        descriptors.sort();
        descriptors.dedup();
        for desc in &descriptors {
            let sid = self.intern(desc)?;
            if desc == b"L_GLOBAL;" {
                b.global_class = Some(sid);
            }
            b.class_by_descriptor.insert(desc.clone(), sid);
        }
        let mut record_classes: Vec<StringId> = Vec::new();
        for rec in &records {
            let desc = record_descriptor(&rec.name);
            let sid = b
                .class_by_descriptor
                .get(&desc)
                .copied()
                .ok_or_else(|| ParseError {
                    line: 0,
                    message: "record descriptor missing".to_owned(),
                })?;
            record_classes.push(sid);
            b.class_by_record_name.insert(rec.name.clone(), sid);
        }

        // Fields (classification mirrors decode_field_at: phase by name,
        // module/scope blobs by record descriptor). `BTreeMap` preserves
        // deterministic `N20` iteration order when collecting scope/phase offsets.
        let mut class_fields: BTreeMap<StringId, Vec<Field>> = BTreeMap::new();
        for (rec, &desc_sid) in records.iter().zip(&record_classes) {
            let mut fields = Vec::new();
            for pf in &rec.fields {
                fields.push(self.build_field(rec, desc_sid, pf, &mut b)?);
            }
            class_fields.insert(desc_sid, fields);
        }

        // Method shells: owner record (longest name prefix), demangled
        // name, synthetic offset, signature registration.
        for fun in &functions {
            let (owner_name, bare) = split_owner(&fun.name, &b.class_by_record_name);
            let bare = demangle(bare, fun.is_ctor, fun.is_cctor);
            let owner_sid = match owner_name {
                Some(name) => {
                    b.class_by_record_name
                        .get(name)
                        .copied()
                        .ok_or_else(|| ParseError {
                            line: fun.line,
                            message: "function owner record missing".to_owned(),
                        })?
                }
                // System-type owners are never printed; unprefixed
                // functions belong to the global record (synthesized above).
                None => match b.global_class {
                    Some(sid) => sid,
                    None => return err(fun.line, "function owner record missing".to_owned()),
                },
            };
            let name_sid = self.intern(&bare)?;
            let offset = b.next_synthetic_offset();
            let sig = function_signature(&fun.name, &fun.params);
            // First signature wins (the emitter dedups; the text holds each
            // signature at most once anyway).
            b.method_by_signature.entry(sig).or_insert(offset);
            b.method_by_name.entry(bare).or_insert(offset);
            b.method_shells.push(MethodShell {
                owner: owner_sid,
                name_sid,
                offset,
            });
        }

        // Rank-order same-content literal groups by the printed LITERALS
        // index (the 13.x/24.x index order approximates the original
        // first-appearance order), keeping lit_offset-pinned offsets last —
        // they are referenced exactly by their nesting parent.
        {
            let mut rank: HashMap<u32, u32> = HashMap::new();
            let mut sorted = self.key_index_to_offset.clone();
            sorted.sort_by_key(|(index, _)| *index);
            for (i, (_, off)) in sorted.iter().enumerate() {
                rank.insert(*off, i as u32);
            }
            let nested = std::mem::take(&mut self.nested_targets);
            for (offsets, _) in self.lit_by_text.values_mut() {
                offsets.sort_by_key(|off| {
                    (
                        nested.contains(off),
                        rank.get(off).copied().unwrap_or(u32::MAX),
                    )
                });
            }
            self.nested_targets = nested;
        }

        // Bodies (temporary method shell offsets and literal source offsets in
        // `MethodBody::entities` are rewritten to dense indices below).
        let mut methods_by_owner: BTreeMap<StringId, Vec<Method>> = BTreeMap::new();
        for (idx, fun) in functions.iter().enumerate() {
            let shell = MethodShell {
                owner: b.method_shells[idx].owner,
                name_sid: b.method_shells[idx].name_sid,
                offset: b.method_shells[idx].offset,
            };
            let method = self.build_method(fun, &shell, &mut b)?;
            methods_by_owner
                .entry(shell.owner)
                .or_default()
                .push(method);
        }

        // Allocate `literal_arrays` slots with `source_offset` first so both
        // `FieldValue::LiteralArrayRef` and bytecode `EntityRef::LiteralArray`
        // have final dense `LiteralArrayIdx` handles before `fix_literal_assignment`.
        let regular = std::mem::take(&mut self.regular);
        let mut literal_arrays: Vec<LiteralArray> = Vec::with_capacity(regular.len());
        let mut offset_to_lit_idx: HashMap<u32, LiteralArrayIdx> = HashMap::new();
        for (_, offset, _, _) in &regular {
            let idx = LiteralArrayIdx(literal_arrays.len() as u32);
            offset_to_lit_idx.insert(*offset, idx);
            literal_arrays.push(LiteralArray::with_source_offset(*offset, Vec::new()));
        }

        // 13/24 scope-names arrays are not printed: synthesize an empty
        // array for every LiteralArrayRef target that has no key.
        let scope_targets: Vec<u32> = class_fields
            .values()
            .flat_map(|fields| fields.iter())
            .filter_map(|f| match f.initial_value {
                Some(FieldValue::LiteralArrayRef {
                    source_offset: Some(off),
                    ..
                }) => Some(off),
                _ => None,
            })
            .collect();
        for off in scope_targets {
            if let std::collections::hash_map::Entry::Vacant(e) = offset_to_lit_idx.entry(off) {
                let idx = LiteralArrayIdx(literal_arrays.len() as u32);
                e.insert(idx);
                literal_arrays.push(LiteralArray::with_source_offset(off, Vec::new()));
            }
        }
        for fields in class_fields.values_mut() {
            for field in fields {
                if let Some(FieldValue::LiteralArrayRef {
                    index,
                    source_offset: Some(off),
                }) = &mut field.initial_value
                {
                    *index = offset_to_lit_idx[off];
                }
            }
        }
        for methods in methods_by_owner.values_mut() {
            for method in methods {
                if let Some(body) = &mut method.body {
                    for eref in body.entities.values_mut() {
                        if let EntityRef::LiteralArray(la_idx) = eref {
                            *la_idx = offset_to_lit_idx[&la_idx.0];
                        }
                    }
                }
            }
        }

        // The ≤12 header literal table: key index → key offset, with gaps
        // (excluded phase-blob slots) filled from the parsed phase fields.
        let mut literal_array_header_offsets = Vec::new();
        if self.version <= LAST_HEADER_LITERAL_VERSION && !self.key_index_to_offset.is_empty() {
            let phase_offsets: Vec<u32> = class_fields
                .values()
                .flat_map(|fields| fields.iter())
                .filter_map(|f| match &f.initial_value {
                    Some(FieldValue::ModuleRequestPhase(p)) => Some(p.source_offset),
                    _ => None,
                })
                .collect();
            let max_index = self
                .key_index_to_offset
                .iter()
                .map(|(i, _)| *i)
                .max()
                .unwrap_or(0);
            let max_table_len = self
                .key_index_to_offset
                .len()
                .saturating_add(phase_offsets.len())
                .saturating_add(65_536);
            let table_len = max_index
                .checked_add(1)
                .and_then(|n| usize::try_from(n).ok())
                .filter(|&n| n <= max_table_len)
                .ok_or_else(|| ParseError {
                    line: 0,
                    message: format!("LITERALS header index {max_index} out of range"),
                })?;
            let mut table = vec![0u32; table_len];
            let mut known = vec![false; table_len];
            for (index, offset) in &self.key_index_to_offset {
                table[*index as usize] = *offset;
                known[*index as usize] = true;
            }
            // Gap fill: phase-blob offsets in field order.
            let mut phase_iter = phase_offsets.iter();
            for slot in known.iter_mut().zip(table.iter_mut()) {
                if !*slot.0 {
                    *slot.1 = phase_iter.next().copied().unwrap_or(0);
                }
            }
            literal_array_header_offsets = table;
        }

        // Assemble classes in record order, then the global class (if it
        // was synthesized and is not already present).
        let mut classes: BTreeMap<StringId, Class> = BTreeMap::new();
        for (rec, &desc_sid) in records.iter().zip(&record_classes) {
            let class = Class {
                descriptor: desc_sid,
                name: desc_sid,
                access_flags: AccessFlags::empty(),
                source_lang: rec.lang,
                source_file: None,
                is_external: rec.external,
                super_class: None,
                interfaces: Vec::new(),
                methods: methods_by_owner.remove(&desc_sid).unwrap_or_default(),
                fields: class_fields.remove(&desc_sid).unwrap_or_default(),
                annotations: Annotations::default(),
            };
            classes.insert(desc_sid, class);
        }
        if let Some(global_sid) = b.global_class {
            classes.entry(global_sid).or_insert_with(|| Class {
                descriptor: global_sid,
                name: global_sid,
                access_flags: AccessFlags::empty(),
                source_lang: SourceLang::EcmaScript,
                source_file: None,
                is_external: false,
                super_class: None,
                interfaces: Vec::new(),
                methods: methods_by_owner.remove(&global_sid).unwrap_or_default(),
                fields: Vec::new(),
                annotations: Annotations::default(),
            });
        }

        // 13.x/24.x: sort per-class methods BEFORE computing final dense
        // `MethodIdx` positions so `MethodIdx` reflects the final method order.
        if self.version > LAST_HEADER_LITERAL_VERSION && !self.key_index_to_offset.is_empty() {
            let mut target: Vec<(u32, u32)> = self.key_index_to_offset.clone();
            target.sort_by_key(|(index, _)| *index);
            fix_literal_assignment(&mut classes, &literal_arrays, &target);
        }

        let offset_to_method_idx: HashMap<u32, MethodIdx> = classes
            .values()
            .flat_map(|c| c.methods.iter())
            .enumerate()
            .map(|(idx, m)| (m.offset, MethodIdx(idx as u32)))
            .collect();
        for class in classes.values_mut() {
            for method in &mut class.methods {
                if let Some(body) = &mut method.body {
                    for eref in body.entities.values_mut() {
                        if let EntityRef::Method(midx) = eref {
                            *midx = offset_to_method_idx[&midx.0];
                        }
                    }
                }
            }
        }

        // Populate literal array items now that both `offset_to_lit_idx` and
        // `offset_to_method_idx` are finalized.
        for (slot, (_, _, items, _)) in regular.iter().enumerate() {
            literal_arrays[slot].values =
                self.resolve_literal_items(items, &b, &offset_to_method_idx, &offset_to_lit_idx)?;
        }

        Ok(File {
            version: self.version,
            checksum: 0,
            size: 0,
            file_type: crate::FileType::Dynamic,
            strings: self.strings,
            classes,
            literal_arrays,
            literal_array_header_offsets,
        })
    }

    /// Build one field; the value classification mirrors `decode_field_at`
    /// (phase/json by field name, module/scope blobs by record descriptor or
    /// `--merge-abc` field name).
    fn build_field(
        &mut self,
        rec: &PaRecord,
        desc_sid: StringId,
        pf: &PaField,
        b: &mut BuildCtx,
    ) -> Result<Field, ParseError> {
        let field_type = parse_type(&mut |raw| self.intern(raw), &pf.ty)?;
        let name_sid = self.intern(&pf.name)?;
        let offset = b.next_synthetic_offset();
        let descriptor = self.strings.resolve(desc_sid).unwrap_or("").to_owned();
        let value_text = pf.value.as_deref();
        let initial_value = match value_text {
            None => None,
            Some(text) => {
                let name_str = lossy(&pf.name);
                if name_str == crate::JSON_FILE_CONTENT_FIELD && field_type == Type::U32 {
                    // Upstream ark_disasm prints `u32 jsonFileContent = 0x…`
                    // as a raw u32 scalar without emitting the target string
                    // into `# STRINGS`; assembling the raw offset would dangle
                    // when `JSPandaFile` reads `GetStringData(EntityId(off))`.
                    return err(
                        pf.line,
                        "jsonFileContent fields are not representable in pandasm text".to_owned(),
                    );
                }
                let parse_hex_u32 = |raw: &[u8]| -> Result<u32, ParseError> {
                    let text = std::str::from_utf8(raw).map_err(|_| ParseError {
                        line: pf.line,
                        message: "field value is not ASCII".to_owned(),
                    })?;
                    let hex = text.strip_prefix("0x").unwrap_or(text);
                    u32::from_str_radix(hex, 16).map_err(|_| ParseError {
                        line: pf.line,
                        message: format!("field value `{text}` does not parse as hex"),
                    })
                };
                if name_str == crate::TYPE_SUMMARY_OFFSET_FIELD && field_type == Type::U32 {
                    let off = parse_hex_u32(text)?;
                    Some(if off == 0 {
                        FieldValue::I32(0)
                    } else {
                        FieldValue::LiteralArrayRef {
                            index: LiteralArrayIdx(u32::MAX),
                            source_offset: Some(off),
                        }
                    })
                } else if name_str == crate::MODULE_REQUEST_PHASE_FIELD && field_type == Type::U32 {
                    let off = parse_hex_u32(text)?;
                    // In `--merge-abc`, pair with the sibling `moduleRecordIdx`
                    // on the same record first; fall back to the file's first
                    // module blob for standalone `_ModuleRequestPhaseRecord`.
                    let sibling_module = rec
                        .fields
                        .iter()
                        .find(|f| f.name == crate::MODULE_RECORD_IDX_FIELD.as_bytes())
                        .and_then(|f| f.value.as_deref())
                        .and_then(|v| parse_hex_u32(v).ok())
                        .and_then(|mod_off| self.modules.get(&mod_off));
                    let target_module = sibling_module.or_else(|| self.modules.values().next());
                    Some(FieldValue::ModuleRequestPhase(ModuleRequestPhase {
                        source_offset: off,
                        // The phase flags are never printed; one zero flag
                        // per module request of the paired module blob.
                        flags: target_module
                            .map(|m| vec![0u8; m.requests.len()])
                            .unwrap_or_default(),
                    }))
                } else if (descriptor == crate::ES_MODULE_RECORD_DESCRIPTOR
                    || name_str == crate::MODULE_RECORD_IDX_FIELD)
                    && field_type == Type::U32
                {
                    let off = parse_hex_u32(text)?;
                    let pa_module = self.modules.get(&off).cloned();
                    let md = match pa_module {
                        Some(ref pa) => self.build_module_data(off, pa)?,
                        None => {
                            // 13.x/24.x standalone `_ESModuleRecord`: the
                            // disassembler never prints the module blob when
                            // the field name is not `moduleRecordIdx`, so an
                            // empty blob keeps the model structurally valid.
                            ModuleData {
                                source_offset: off,
                                requests: Vec::new(),
                                records: Vec::new(),
                            }
                        }
                    };
                    Some(FieldValue::ModuleData(md))
                } else if (descriptor == crate::ES_SCOPE_NAMES_RECORD_DESCRIPTOR
                    || name_str == crate::SCOPE_NAMES_FIELD)
                    && field_type == Type::U32
                {
                    let off = parse_hex_u32(text)?;
                    Some(FieldValue::LiteralArrayRef {
                        index: LiteralArrayIdx(u32::MAX),
                        source_offset: Some(off),
                    })
                } else {
                    match field_type {
                        Type::U32 | Type::U8 | Type::Bool => {
                            let v = parse_hex_u32(text)?;
                            Some(FieldValue::I32(v as i32))
                        }
                        Type::F64 => {
                            let text = std::str::from_utf8(text).map_err(|_| ParseError {
                                line: pf.line,
                                message: "field f64 value is not ASCII".to_owned(),
                            })?;
                            let v = text.parse::<f64>().map_err(|_| ParseError {
                                line: pf.line,
                                message: format!("field f64 `{text}` does not parse"),
                            })?;
                            Some(FieldValue::F64(v))
                        }
                        // The emitter only prints U32/U8/F64/Bool values.
                        _ => {
                            return err(
                                pf.line,
                                "field initial value on a type the emitter never prints".to_owned(),
                            );
                        }
                    }
                }
            }
        };
        Ok(Field {
            name: name_sid,
            offset,
            field_type,
            access_flags: AccessFlags::empty(),
            is_external: false,
            initial_value,
            annotations: Annotations::default(),
        })
    }

    /// PaModule → ModuleData with interned strings; `module_request:` names
    /// resolve to request indices (first match — identical names print
    /// identically either way).
    fn build_module_data(&mut self, offset: u32, pa: &PaModule) -> Result<ModuleData, ParseError> {
        let mut requests = Vec::with_capacity(pa.requests.len());
        for req in &pa.requests {
            requests.push(self.intern(req)?);
        }
        let request_idx = |name: &[u8]| -> Result<u32, ParseError> {
            pa.requests
                .iter()
                .position(|r| r == name)
                .map(|p| p as u32)
                .ok_or_else(|| ParseError {
                    line: 0,
                    message: format!(
                        "module_request `{}` not in the request array",
                        String::from_utf8_lossy(name)
                    ),
                })
        };
        let mut records = Vec::with_capacity(pa.records.len());
        for rec in &pa.records {
            let r = match rec {
                PaModuleRecord::RegularImport {
                    local,
                    import,
                    request,
                } => ModuleRecord::RegularImport {
                    local_name: self.intern(local)?,
                    import_name: self.intern(import)?,
                    module_request_idx: request_idx(request)?,
                },
                PaModuleRecord::NamespaceImport { local, request } => {
                    ModuleRecord::NamespaceImport {
                        local_name: self.intern(local)?,
                        module_request_idx: request_idx(request)?,
                    }
                }
                PaModuleRecord::LocalExport { local, export } => ModuleRecord::LocalExport {
                    local_name: self.intern(local)?,
                    export_name: self.intern(export)?,
                },
                PaModuleRecord::IndirectExport {
                    export,
                    import,
                    request,
                } => ModuleRecord::IndirectExport {
                    export_name: self.intern(export)?,
                    import_name: self.intern(import)?,
                    module_request_idx: request_idx(request)?,
                },
                PaModuleRecord::StarExport { request } => ModuleRecord::StarExport {
                    module_request_idx: request_idx(request)?,
                },
            };
            records.push(r);
        }
        Ok(ModuleData {
            source_offset: offset,
            requests,
            records,
        })
    }

    /// Resolve parsed literal items to model values (method names → dense
    /// [`MethodIdx`] handles, `lit_offset` → [`LiteralArrayIdx`] handles).
    fn resolve_literal_items(
        &mut self,
        items: &[PaItem],
        b: &BuildCtx,
        offset_to_method_idx: &HashMap<u32, MethodIdx>,
        offset_to_lit_idx: &HashMap<u32, LiteralArrayIdx>,
    ) -> Result<Vec<LiteralValue>, ParseError> {
        let mut out = Vec::with_capacity(items.len());
        for item in items {
            let v = match item {
                PaItem::Bool(v) => LiteralValue::Bool(*v),
                PaItem::Int(v) => LiteralValue::Integer(*v),
                PaItem::Int8(v) => LiteralValue::Integer8(*v),
                PaItem::Float(v) => LiteralValue::Float(*v),
                PaItem::Double(v) => LiteralValue::Double(*v),
                PaItem::Str(s) => LiteralValue::String(self.intern(s)?),
                PaItem::EtsImplements(s) => LiteralValue::EtsImplements(self.intern(s)?),
                PaItem::Method(name) => {
                    LiteralValue::Method(self.method_ref(name, b, offset_to_method_idx)?)
                }
                PaItem::GeneratorMethod(name) => {
                    LiteralValue::GeneratorMethod(self.method_ref(name, b, offset_to_method_idx)?)
                }
                PaItem::Getter(name) => {
                    LiteralValue::Getter(self.method_ref(name, b, offset_to_method_idx)?)
                }
                PaItem::Setter(name) => {
                    LiteralValue::Setter(self.method_ref(name, b, offset_to_method_idx)?)
                }
                PaItem::AsyncGeneratorMethod(name) => LiteralValue::AsyncGeneratorMethod(
                    self.method_ref(name, b, offset_to_method_idx)?,
                ),
                PaItem::Accessor(v) => LiteralValue::Accessor(*v),
                PaItem::MethodAffiliate(v) => LiteralValue::MethodAffiliate(*v),
                PaItem::NullValue(v) => LiteralValue::NullValue(*v),
                PaItem::LitOffset(off) => {
                    let idx = offset_to_lit_idx
                        .get(off)
                        .copied()
                        .ok_or_else(|| ParseError {
                            line: 0,
                            message: format!("lit_offset 0x{off:x} names no literal array"),
                        })?;
                    LiteralValue::LiteralArray(idx)
                }
                PaItem::LitBufferIndex(v) => LiteralValue::LiteralBufferIndex(LiteralArrayIdx(*v)),
                PaItem::BuiltinType(v) => LiteralValue::BuiltinTypeIndex(*v),
                PaItem::ArrayU1(v) => LiteralValue::ArrayU1(v.clone()),
                PaItem::ArrayU8(v) => LiteralValue::ArrayU8(v.clone()),
                PaItem::ArrayI8(v) => LiteralValue::ArrayI8(v.clone()),
                PaItem::ArrayU16(v) => LiteralValue::ArrayU16(v.clone()),
                PaItem::ArrayI16(v) => LiteralValue::ArrayI16(v.clone()),
                PaItem::ArrayU32(v) => LiteralValue::ArrayU32(v.clone()),
                PaItem::ArrayI32(v) => LiteralValue::ArrayI32(v.clone()),
                PaItem::ArrayU64(v) => LiteralValue::ArrayU64(v.clone()),
                PaItem::ArrayI64(v) => LiteralValue::ArrayI64(v.clone()),
                PaItem::ArrayF32(v) => LiteralValue::ArrayF32(v.clone()),
                PaItem::ArrayF64(v) => LiteralValue::ArrayF64(v.clone()),
                PaItem::ArrayString(v) => {
                    let mut sids = Vec::with_capacity(v.len());
                    for raw in v {
                        sids.push(self.intern(raw)?);
                    }
                    LiteralValue::ArrayString(sids)
                }
            };
            out.push(v);
        }
        Ok(out)
    }

    /// Method name (bare bytes) → the method's dense [`MethodIdx`].
    fn method_ref(
        &mut self,
        name: &[u8],
        b: &BuildCtx,
        offset_to_method_idx: &HashMap<u32, MethodIdx>,
    ) -> Result<MethodIdx, ParseError> {
        let off = b
            .method_by_name
            .get(name)
            .copied()
            .ok_or_else(|| ParseError {
                line: 0,
                message: format!(
                    "literal method reference `{}` names no defined function",
                    String::from_utf8_lossy(name)
                ),
            })?;
        Ok(offset_to_method_idx[&off])
    }

    /// Build one method (body finalization: registers, labels, entities,
    /// try blocks — then ISA construction).
    fn build_method(
        &mut self,
        fun: &PaFunction,
        shell: &MethodShell,
        b: &mut BuildCtx,
    ) -> Result<Method, ParseError> {
        // Access flags: the corpus prints `static` only; ctor/cctor carry
        // no extra model flags here (the name carries the semantics).
        let mut access_flags = AccessFlags::empty();
        if fun.is_static {
            access_flags |= AccessFlags::STATIC;
        }

        let num_args = fun.params.len().saturating_sub(usize::from(!fun.is_static)) as u32;

        let annotations = self.build_annotations(fun)?;

        let body = if fun.has_body && !fun.is_external {
            Some(self.build_body(fun, b)?)
        } else {
            if !fun.insns.is_empty() || !fun.catches.is_empty() {
                return err(
                    fun.line,
                    "code-less function (no return type) with a body".to_owned(),
                );
            }
            None
        };

        // Proto types: ≤12.0.6.0 protos carry no shorty (decode yields
        // None/[]); 13.x/24.x es2abc protos are all-`any` (Tagged).
        let (return_type, arg_types) = if self.version <= LAST_HEADER_LITERAL_VERSION {
            (None, Vec::new())
        } else if fun.has_body {
            (Some(Type::Tagged), vec![Type::Tagged; num_args as usize])
        } else {
            (None, Vec::new())
        };

        Ok(Method {
            name: shell.name_sid,
            offset: shell.offset,
            access_flags,
            function_kind: FunctionKind::None,
            source_lang: fun.lang,
            is_external: fun.is_external,
            return_type,
            arg_types,
            body,
            annotations,
            param_annotations: ParamAnnotations::default(),
            debug: None,
        })
    }

    fn build_annotations(&mut self, fun: &PaFunction) -> Result<Annotations, ParseError> {
        let mut compile_time = Vec::new();
        for pa in &fun.annotations {
            let descriptor = self.intern(&pa.descriptor)?;
            let mut elements = Vec::new();
            for (name, value) in &pa.elements {
                let name = self.intern(name)?;
                let value = match value {
                    PaElemValue::U32(v) => AnnotationValue::U32(*v),
                    PaElemValue::Bool(v) => AnnotationValue::Bool(*v),
                    PaElemValue::F64(v) => AnnotationValue::F64(*v),
                    PaElemValue::Str(raw) => AnnotationValue::String(self.intern(raw)?),
                };
                elements.push(AnnotationElem { name, value });
            }
            compile_time.push(Annotation {
                class_descriptor: descriptor,
                elements,
            });
        }
        Ok(Annotations {
            compile_time,
            ..Annotations::default()
        })
    }

    /// Finalize one function body: the upstream register rule
    /// (`num_vregs = max(v-index) + 1`, `a`-regs shifted by it), label
    /// resolution, entity registration, and ISA construction.
    fn build_body(&mut self, fun: &PaFunction, b: &mut BuildCtx) -> Result<MethodBody, ParseError> {
        let num_vregs = fun
            .insns
            .iter()
            .flat_map(|insn| insn.ops.iter())
            .filter_map(|op| match op {
                PaOp::VReg(v) => Some(*v as u32 + 1),
                _ => None,
            })
            .max()
            .unwrap_or(0);

        let insn_count = fun.insns.len() as u32;
        let mut state = BodyBuildState {
            fun,
            num_vregs,
            insn_count,
            entities: HashMap::new(),
            next_raw: HashMap::new(),
            string_slots: HashMap::new(),
            method_slots: HashMap::new(),
            literal_slots: HashMap::new(),
        };
        let mut bytecodes = Vec::with_capacity(fun.insns.len());

        for insn in &fun.insns {
            let mnemonic = std::str::from_utf8(&insn.mnemonic).map_err(|_| ParseError {
                line: insn.line,
                message: "instruction mnemonic is not ASCII".to_owned(),
            })?;
            let spec = insn_specs().get(mnemonic).ok_or_else(|| ParseError {
                line: insn.line,
                message: format!("unknown instruction `{mnemonic}`"),
            })?;
            // Align tokens to the spec. An empty literal-array operand
            // prints as NOTHING (the token was dropped by the splitter), so
            // a LiteralArr position with a non-literal/exhausted token gets
            // an implicit empty literal.
            let mut raw_ops: Vec<RawOperand> = Vec::with_capacity(spec.kinds.len());
            let mut ops_iter = insn.ops.iter().peekable();
            for (pos, kind) in spec.kinds.iter().enumerate() {
                let op = if *kind == OpKind::LiteralArr
                    && !matches!(ops_iter.peek(), Some(PaOp::Literal(_)))
                {
                    &PaOp::Literal(Vec::new())
                } else {
                    ops_iter.next().ok_or_else(|| ParseError {
                        line: insn.line,
                        message: format!("`{mnemonic}` expects more operands"),
                    })?
                };
                let raw =
                    self.convert_operand(insn.line, mnemonic, pos, *kind, op, &mut state, b)?;
                raw_ops.push(raw);
            }
            if ops_iter.next().is_some() {
                return err(
                    insn.line,
                    format!("`{mnemonic}` has more operands than the ISA allows"),
                );
            }
            let bc = insn_ctor::construct(mnemonic, &raw_ops).ok_or_else(|| ParseError {
                line: insn.line,
                message: format!("`{mnemonic}` operand kinds do not match the ISA"),
            })?;
            bytecodes.push(bc);
        }

        let try_blocks = self.build_try_blocks(fun, insn_count)?;

        Ok(MethodBody {
            num_vregs,
            num_args: fun.params.len().saturating_sub(usize::from(!fun.is_static)) as u32,
            code: crate::MethodCode::Decoded(bytecodes),
            entities: crate::MethodEntities::from(state.entities),
            try_blocks,
            ic_size: None,
        })
    }

    /// Convert one syntactic operand to its typed form per the spec kind,
    /// registering entities as needed.
    #[expect(
        clippy::too_many_arguments,
        reason = "operand converter threads line/mnemonic/position diagnostics alongside body state and builder"
    )]
    fn convert_operand(
        &mut self,
        line: usize,
        mnemonic: &str,
        pos: usize,
        kind: OpKind,
        op: &PaOp,
        state: &mut BodyBuildState<'_>,
        b: &mut BuildCtx,
    ) -> Result<RawOperand, ParseError> {
        let mismatch = || ParseError {
            line,
            message: format!("`{mnemonic}` operand {pos} has the wrong kind for the ISA"),
        };
        match (kind, op) {
            (OpKind::Reg, PaOp::VReg(v)) => Ok(RawOperand::R(*v)),
            (OpKind::Reg, PaOp::AReg(a)) => {
                let reg = state.num_vregs + *a as u32;
                let reg = u16::try_from(reg).map_err(|_| ParseError {
                    line,
                    message: format!("`{mnemonic}` register {reg} out of range"),
                })?;
                Ok(RawOperand::R(reg))
            }
            (OpKind::Imm, PaOp::Imm(v)) => Ok(RawOperand::I(*v)),
            (OpKind::ImmFloat, PaOp::Float(v)) => Ok(RawOperand::I(v.to_bits() as i64)),
            (OpKind::ImmFloat, PaOp::Imm(v)) => Ok(RawOperand::I(*v)),
            (OpKind::Label, PaOp::LabelRef(name)) => {
                let idx = match state.fun.labels.get(name) {
                    Some(&idx) => idx,
                    None if state.fun.trailing_empty_label => state.insn_count,
                    None => {
                        return err(
                            line,
                            format!("undefined label `{}`", String::from_utf8_lossy(name)),
                        );
                    }
                };
                Ok(RawOperand::L(idx))
            }
            // The emitter's out-of-range jump quirk prints the raw index
            // in decimal.
            (OpKind::Label, PaOp::Imm(v)) => Ok(RawOperand::L(*v as u32)),
            (OpKind::Str, PaOp::Str(content)) => {
                let sid = self.intern(content)?;
                // Preserve the STRING section's first listed offset when
                // present so re-emission reproduces the section verbatim.
                let source_offset = self
                    .string_offsets
                    .get(content)
                    .and_then(|offsets| offsets.first().copied());
                let id = match state.string_slots.get(&(sid, source_offset)).copied() {
                    Some(existing) => existing,
                    None => {
                        let raw = state.next_raw.entry(EntityKind::StringId).or_insert(0);
                        let id = *raw;
                        *raw += 1;
                        state.string_slots.insert((sid, source_offset), id);
                        state.entities.insert(
                            (EntityKind::StringId, id),
                            EntityRef::String {
                                id: sid,
                                source_offset,
                            },
                        );
                        id
                    }
                };
                Ok(RawOperand::E(id))
            }
            (OpKind::Method, PaOp::MethodSig(sig)) => {
                let offset = b
                    .method_by_signature
                    .get(sig)
                    .copied()
                    .ok_or_else(|| ParseError {
                        line,
                        message: format!(
                            "method reference `{}` names no defined function",
                            String::from_utf8_lossy(sig)
                        ),
                    })?;
                let id = match state.method_slots.get(&offset).copied() {
                    Some(existing) => existing,
                    None => {
                        let raw = state.next_raw.entry(EntityKind::MethodId).or_insert(0);
                        let id = *raw;
                        *raw += 1;
                        state.method_slots.insert(offset, id);
                        // Temporarily store the synthetic method offset; rewritten to
                        // the post-sort dense `MethodIdx` in `build()`.
                        state.entities.insert(
                            (EntityKind::MethodId, id),
                            EntityRef::Method(MethodIdx(offset)),
                        );
                        id
                    }
                };
                Ok(RawOperand::E(id))
            }
            (OpKind::LiteralArr, PaOp::Literal(text)) => {
                let offset = match self.lit_by_text.get_mut(text) {
                    Some((offsets, cursor)) => {
                        let off = offsets[*cursor % offsets.len()];
                        *cursor += 1;
                        off
                    }
                    None => {
                        let items = if text.is_empty() {
                            Vec::new()
                        } else {
                            match self.parse_literal_value(text, line)? {
                                PaLiteral::Regular(items) => items,
                                PaLiteral::Module(_) => {
                                    return err(
                                        line,
                                        "module array as an instruction operand".to_owned(),
                                    );
                                }
                            }
                        };
                        let off = b.next_synthetic_offset();
                        self.lit_by_text
                            .entry(text.clone())
                            .or_default()
                            .0
                            .push(off);
                        self.lit_by_offset.insert(off, self.regular.len());
                        self.regular.push((0, off, items, text.clone()));
                        off
                    }
                };
                let id = match state.literal_slots.get(&offset).copied() {
                    Some(existing) => existing,
                    None => {
                        let raw = state
                            .next_raw
                            .entry(EntityKind::LiteralarrayId)
                            .or_insert(0);
                        let id = *raw;
                        *raw += 1;
                        state.literal_slots.insert(offset, id);
                        // Temporarily store the literal source offset; rewritten to
                        // `offset_to_lit_idx[&offset]` in `build()`.
                        state.entities.insert(
                            (EntityKind::LiteralarrayId, id),
                            EntityRef::LiteralArray(LiteralArrayIdx(offset)),
                        );
                        id
                    }
                };
                Ok(RawOperand::E(id))
            }
            _ => Err(mismatch()),
        }
    }

    /// Group the printed `.catch`/`.catchall` lines into try blocks (one
    /// block per (try-begin, try-end) pair, first-appearance order — the
    /// emitter's enumeration order).
    fn build_try_blocks(
        &mut self,
        fun: &PaFunction,
        insn_count: u32,
    ) -> Result<Vec<TryBlock>, ParseError> {
        let label_idx = |fun: &PaFunction, name: &[u8], line: usize| -> Result<u32, ParseError> {
            match fun.labels.get(name) {
                Some(&idx) => Ok(idx),
                None if fun.trailing_empty_label => Ok(insn_count),
                None => err(
                    line,
                    format!("undefined catch label `{}`", String::from_utf8_lossy(name)),
                ),
            }
        };
        let mut blocks: Vec<TryBlock> = Vec::new();
        let mut by_range: HashMap<(u32, u32), usize> = HashMap::new();
        for catch in &fun.catches {
            let begin = label_idx(fun, &catch.try_begin, catch.line)?;
            let end = label_idx(fun, &catch.try_end, catch.line)?;
            if end < begin || end > insn_count {
                return err(catch.line, "catch try range out of bounds".to_owned());
            }
            let handler = label_idx(fun, &catch.catch_begin, catch.line)?;
            let handler_end = if catch.catch_end.is_empty() {
                handler
            } else {
                label_idx(fun, &catch.catch_end, catch.line)?
            };
            if handler_end < handler || handler_end > insn_count {
                return err(catch.line, "catch handler range out of bounds".to_owned());
            }
            let type_class = if catch.record.is_empty() {
                None
            } else {
                let desc = record_descriptor(&catch.record);
                Some(self.intern(&desc)?)
            };
            let cb = CatchBlock {
                type_class,
                handler,
                len: handler_end - handler,
            };
            let key = (begin, end);
            match by_range.get(&key) {
                Some(&idx) => blocks[idx].catches.push(cb),
                None => {
                    by_range.insert(key, blocks.len());
                    blocks.push(TryBlock {
                        start: begin,
                        len: end - begin,
                        catches: vec![cb],
                    });
                }
            }
        }
        Ok(blocks)
    }
}

// Build-time state
// ---------------------------------------------------------------------------

#[derive(Default)]
struct BuildCtx {
    /// Record name (pandasm form) → class descriptor id.
    class_by_record_name: HashMap<Vec<u8>, StringId>,
    /// Descriptor bytes → id (all classes, including synthesized _GLOBAL).
    class_by_descriptor: HashMap<Vec<u8>, StringId>,
    /// Synthesized `_GLOBAL` class descriptor (unprefixed functions).
    global_class: Option<StringId>,
    /// `name:(sig)` → synthetic method offset.
    method_by_signature: HashMap<Vec<u8>, u32>,
    /// Bare method name → synthetic method offset (literal method refs).
    method_by_name: HashMap<Vec<u8>, u32>,
    method_shells: Vec<MethodShell>,
    next_offset: u32,
}

impl BuildCtx {
    fn next_synthetic_offset(&mut self) -> u32 {
        self.next_offset = self
            .next_offset
            .checked_add(4)
            .unwrap_or(SYNTHETIC_OFFSET_BASE);
        if self.next_offset < SYNTHETIC_OFFSET_BASE {
            self.next_offset = SYNTHETIC_OFFSET_BASE;
        }
        self.next_offset
    }
}

struct MethodShell {
    owner: StringId,
    name_sid: StringId,
    offset: u32,
}

struct BodyBuildState<'a> {
    fun: &'a PaFunction,
    num_vregs: u32,
    insn_count: u32,
    entities: HashMap<(EntityKind, u32), EntityRef>,
    next_raw: HashMap<EntityKind, u32>,
    string_slots: HashMap<(StringId, Option<u32>), u32>,
    method_slots: HashMap<u32, u32>,
    literal_slots: HashMap<u32, u32>,
}

// ---------------------------------------------------------------------------
// Name / type helpers
// ---------------------------------------------------------------------------

/// Inverse of the emitter's `record_pandasm_name` for non-array record
/// names: dots become slashes inside an `L…;` wrapper.
pub(super) fn record_descriptor(name: &[u8]) -> Vec<u8> {
    let mut desc = Vec::with_capacity(name.len() + 2);
    desc.push(b'L');
    for &b in name {
        desc.push(if b == b'.' { b'/' } else { b });
    }
    desc.push(b';');
    desc
}

/// Inverse of the emitter's `replace_once(".ctor", "_ctor_")` mangling.
fn demangle(name: &[u8], is_ctor: bool, is_cctor: bool) -> Vec<u8> {
    let mut out = name.to_vec();
    let (needle, with): (&[u8], &[u8]) = if is_ctor {
        (b"_ctor_", b".ctor")
    } else if is_cctor {
        (b"_cctor_", b".cctor")
    } else {
        return out;
    };
    if let Some(pos) = out.windows(needle.len()).position(|w| w == needle) {
        out.splice(pos..pos + needle.len(), with.iter().copied());
    }
    out
}

/// The longest printed record name that prefixes `name` + `.` (owner
/// resolution before the name→id map exists).
fn record_prefix_of<'a>(name: &[u8], records: &'a [PaRecord]) -> Option<&'a [u8]> {
    let mut best: Option<&[u8]> = None;
    for rec in records {
        let r = rec.name.as_slice();
        if name.len() > r.len()
            && name.starts_with(r)
            && name[r.len()] == b'.'
            && best.is_none_or(|b| r.len() > b.len())
        {
            best = Some(r);
        }
    }
    best
}

/// Split a full printed function name into (record name, bare method
/// name): the LONGEST known record name followed by `.`; `None` = global.
fn split_owner<'a, 'b>(
    name: &'a [u8],
    records: &'b HashMap<Vec<u8>, StringId>,
) -> (Option<&'b [u8]>, &'a [u8]) {
    let mut best: Option<&[u8]> = None;
    for rec in records.keys() {
        if name.len() > rec.len()
            && name.starts_with(rec)
            && name[rec.len()] == b'.'
            && best.is_none_or(|b| rec.len() > b.len())
        {
            best = Some(rec);
        }
    }
    match best {
        Some(rec) => (Some(rec), &name[rec.len() + 1..]),
        None => (None, name),
    }
}

/// `GetFunctionSignatureFromName`: `name:(type,type,…)`.
fn function_signature(name: &[u8], params: &[Vec<u8>]) -> Vec<u8> {
    let mut sig = name.to_vec();
    sig.extend_from_slice(b":(");
    for (i, p) in params.iter().enumerate() {
        if i > 0 {
            sig.push(b',');
        }
        sig.extend_from_slice(p);
    }
    sig.extend_from_slice(b")");
    sig
}

/// Parse a pandasm type name (field types, parameter types): the inverse
/// of the emitter's `type_pandasm_name` / `record_pandasm_name`.
fn parse_type(
    intern: &mut dyn FnMut(&[u8]) -> Result<StringId, ParseError>,
    name: &[u8],
) -> Result<Type, ParseError> {
    Ok(match name {
        b"void" => Type::Void,
        b"u1" => Type::Bool,
        b"i8" => Type::I8,
        b"u8" => Type::U8,
        b"i16" => Type::I16,
        b"u16" => Type::U16,
        b"i32" => Type::I32,
        b"u32" => Type::U32,
        b"i64" => Type::I64,
        b"u64" => Type::U64,
        b"f32" => Type::F32,
        b"f64" => Type::F64,
        b"any" => Type::Tagged,
        other => {
            // Reference type: `Foo.Bar[]` → `[[LFoo/Bar;`.
            let mut rank = 0usize;
            let mut base = other;
            while base.ends_with(b"[]") {
                rank += 1;
                base = &base[..base.len() - 2];
            }
            let mut desc = Vec::new();
            desc.resize(rank, b'[');
            let prim: Option<u8> = match base {
                b"u1" => Some(b'Z'),
                b"i8" => Some(b'B'),
                b"u8" => Some(b'H'),
                b"i16" => Some(b'S'),
                b"u16" => Some(b'C'),
                b"i32" => Some(b'I'),
                b"u32" => Some(b'U'),
                b"f32" => Some(b'F'),
                b"f64" => Some(b'D'),
                b"i64" => Some(b'J'),
                b"u64" => Some(b'Q'),
                b"void" => Some(b'V'),
                _ => None,
            };
            match prim {
                Some(p) => desc.push(p),
                None => {
                    desc.push(b'L');
                    for &b in base {
                        desc.push(if b == b'.' { b'/' } else { b });
                    }
                    desc.push(b';');
                }
            }
            Type::Reference(intern(&desc)?)
        }
    })
}

// 13.x/24.x literal-table index recovery
// ---------------------------------------------------------------------------
//
// The LITERALS key index of a 13.x/24.x array is its position in the
// emitter's libstdc++-unordered_set iteration over the collected offsets —
// a pure function of the insertion (first-appearance) order in the
// class/method/instruction walk. The pandasm text carries neither the
// method order within a class (functions print signature-sorted) nor the
// source offset an inline literal operand referenced (contents print
// inline). [`fix_literal_assignment`] recovers the assignment for the
// common case: same-content references were bound in printed index order at
// build time (the original first-appearance order usually coincides), and
// each class's methods are then sorted by the smallest printed index their
// instructions reference — method order is textually invisible (functions
// print signature-sorted), so permuting it costs nothing. Fixtures whose
// original order coincides with neither are ledgered by the corpus gate
// (scripts/pandasm-asm-divergences.json,
// `text:literal-index-order-underdetermined`).

fn fix_literal_assignment(
    classes: &mut BTreeMap<StringId, Class>,
    literal_arrays: &[LiteralArray],
    target: &[(u32, u32)],
) {
    // Method order within a class is invisible in the text (functions print
    // signature-sorted) but drives the 13.x/24.x collection order. Sort
    // each class's methods by the smallest printed index their literal
    // operands reference. (Bindings keep the build-time target-rank order.)
    let rank: HashMap<u32, u32> = target
        .iter()
        .enumerate()
        .map(|(i, (_, off))| (*off, i as u32))
        .collect();
    for class in classes.values_mut() {
        class
            .methods
            .sort_by_key(|m| method_min_literal_rank(m, literal_arrays, &rank));
    }
}

/// The smallest `rank` among the literal arrays a method's instructions
/// reference (`u32::MAX` when it references none).
fn method_min_literal_rank(
    m: &Method,
    literal_arrays: &[LiteralArray],
    rank: &HashMap<u32, u32>,
) -> u32 {
    let Some(body) = &m.body else {
        return u32::MAX;
    };
    let mut best = u32::MAX;
    let bcs = body.bytecodes();
    for bc in bcs.iter() {
        let (ops, len) = bc.entity_operands_inline();
        for &(kind, id) in &ops[..len] {
            if kind == EntityKind::LiteralarrayId
                && let Some(&EntityRef::LiteralArray(la_idx)) = body.entities.get(&(kind, id.0))
                && let Some(off) = literal_arrays
                    .get(la_idx.index())
                    .and_then(|la| la.source_offset)
                && let Some(&r) = rank.get(&off)
            {
                best = best.min(r);
            }
        }
    }
    best
}
