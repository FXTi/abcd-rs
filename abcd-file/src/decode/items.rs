//! Owned `.abc` item decoders for classes, methods, code bodies, prototypes,
//! fields, ECMAScript module records, and iterative nested annotations.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use abcd_file_sys as sys;

use crate::code::{CatchBlock, TryBlock};
use crate::debug::{ModelDebugSink, decode_method_debug_item};
use crate::error::Error;
use crate::file::{
    AbcReader, RawAnnotation, RawField, RawFieldValue, RawMethod, RawModuleRecord, StringItemCache,
};
use crate::literal::{decode_literal_array_values, walk_raw_literal_array};
use crate::model::*;
use crate::types::{AccessFlags, Dialect, FunctionKind, SourceLang, Type, TypeId};
use crate::{StringId, StringPool};

use super::{
    ABSENT, DecodeDiagnostic, DecodeDiagnostics, ES_MODULE_RECORD_DESCRIPTOR,
    ES_SCOPE_NAMES_RECORD_DESCRIPTOR, JSON_FILE_CONTENT_FIELD, MODULE_RECORD_IDX_FIELD,
    MODULE_REQUEST_PHASE_FIELD, PendingMethodOps, RawEntityOp, RawLegacyBufOp, SCOPE_NAMES_FIELD,
    TYPE_SUMMARY_OFFSET_FIELD, decode_function_kind_from_flags, decode_source_lang,
};

// Internal Item Decoders (`decode_core`)
// ---------------------------------------------------------------------------

pub(super) fn read_class_descriptor_cached(
    reader: &AbcReader<'_>,
    class_off: u32,
    str_cache: &mut StringItemCache,
    strings: &mut StringPool,
) -> Option<(StringId, String)> {
    if let Some(sid) = str_cache.intern_utf8(reader, class_off, strings) {
        let s = strings.resolve(sid).unwrap_or_default().to_owned();
        return Some((sid, s));
    }
    let raw = reader.raw_cstr_at(class_off)?;
    let text = String::from_utf8_lossy(raw).into_owned();
    let sid = strings.get_or_intern(&text);
    Some((sid, text))
}

#[expect(
    clippy::too_many_arguments,
    reason = "method decoder threads class context, lazy backing buffer, forensic diagnostics, and string cache"
)]
pub(super) fn decode_method_item(
    reader: &AbcReader<'_>,
    raw_m: &RawMethod,
    class_id: u32,
    class_source_file_off: Option<u32>,
    dialect: Dialect,
    lazy_backing: Option<&Arc<[u8]>>,
    forensic: bool,
    diagnostics: &mut DecodeDiagnostics,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache,
    ann_visiting: &mut HashSet<u32>,
) -> Result<(Method, Option<PendingMethodOps>), Error> {
    let method_off = raw_m.offset;
    let name = str_cache
        .intern_method_name(reader, raw_m.name_off, strings)
        .ok_or_else(|| Error::Malformed {
            field: "name",
            context: format!("method at offset {method_off:#x}"),
        })?;

    let function_kind = match decode_function_kind_from_flags(raw_m.access_flags) {
        Ok(k) => k,
        Err(err) => {
            if forensic {
                diagnostics.push(DecodeDiagnostic {
                    kind: "method",
                    offset: Some(method_off),
                    message: err.to_string(),
                });
                FunctionKind::None
            } else {
                return Err(err);
            }
        }
    };
    let source_lang = match decode_source_lang(raw_m.source_lang) {
        Ok(lang) => lang,
        Err(err) => {
            if forensic {
                diagnostics.push(DecodeDiagnostic {
                    kind: "method",
                    offset: Some(method_off),
                    message: err.to_string(),
                });
                SourceLang::PandaAssembly
            } else {
                return Err(err);
            }
        }
    };

    let (body, pending_ops, byte_offsets, code_byte_len) = match raw_m.code_off {
        None => (None, None, Vec::new(), 0),
        Some(code_off) => {
            match decode_code_item(
                reader,
                method_off,
                code_off,
                dialect,
                lazy_backing,
                entity_map,
                strings,
                str_cache,
            ) {
                Ok((b, ops, bo, csize)) => (Some(b), Some(ops), bo, csize),
                Err(err) => {
                    if forensic {
                        let kind = match &err {
                            Error::BytecodeDecode { .. } => "bytecode",
                            _ => "method_body",
                        };
                        diagnostics.push(DecodeDiagnostic {
                            kind,
                            offset: Some(method_off),
                            message: err.to_string(),
                        });
                        (None, None, Vec::new(), 0)
                    } else {
                        return Err(err);
                    }
                }
            }
        }
    };

    let (return_type, arg_types) = match reader.method_proto_off(raw_m) {
        None => (None, Vec::new()),
        Some(proto_off) => match decode_proto_types(reader, proto_off, entity_map) {
            Ok((rt, at)) => (Some(rt), at),
            Err(err) => {
                if forensic {
                    diagnostics.push(DecodeDiagnostic {
                        kind: "proto",
                        offset: Some(proto_off),
                        message: err.to_string(),
                    });
                    (None, Vec::new())
                } else {
                    return Err(err);
                }
            }
        },
    };

    let annotations = Annotations {
        compile_time: decode_annotation_list(
            reader,
            &raw_m.annotations,
            forensic,
            diagnostics,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        runtime: decode_annotation_list(
            reader,
            &raw_m.runtime_annotations,
            forensic,
            diagnostics,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        compile_time_type: decode_annotation_list(
            reader,
            &raw_m.type_annotations,
            forensic,
            diagnostics,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        runtime_type: decode_annotation_list(
            reader,
            &raw_m.runtime_type_annotations,
            forensic,
            diagnostics,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
    };

    let debug = match raw_m.debug_info_off {
        None => None,
        Some(debug_off) => {
            let mut sink = ModelDebugSink::new(strings);
            match decode_method_debug_item(
                reader,
                class_id,
                class_source_file_off,
                raw_m,
                code_byte_len,
                debug_off,
                &mut sink,
            ) {
                Ok(()) => Some(sink.into_debug_info(&byte_offsets)),
                Err(err) => {
                    if forensic {
                        diagnostics.push(DecodeDiagnostic {
                            kind: "debug_info",
                            offset: Some(debug_off),
                            message: err.to_string(),
                        });
                        None
                    } else {
                        return Err(err);
                    }
                }
            }
        }
    };

    // Note: `byte_offsets` is dropped immediately when `decode_method_item` returns!
    drop(byte_offsets);

    let param_annotations = decode_param_annotations(
        reader,
        raw_m,
        arg_types.len(),
        forensic,
        diagnostics,
        entity_map,
        strings,
        str_cache,
        ann_visiting,
    )?;

    Ok((
        Method {
            name,
            offset: method_off,
            access_flags: AccessFlags::from_bits_truncate(raw_m.access_flags),
            function_kind,
            source_lang,
            is_external: raw_m.is_external,
            return_type,
            arg_types,
            body,
            annotations,
            param_annotations,
            debug,
        },
        pending_ops,
    ))
}

#[expect(
    clippy::too_many_arguments,
    reason = "code decoder validates bytecodes and try/catch spans and returns transient debug byte_offsets"
)]
fn decode_code_item(
    reader: &AbcReader<'_>,
    method_off: u32,
    code_off: u32,
    dialect: Dialect,
    lazy_backing: Option<&Arc<[u8]>>,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache,
) -> Result<(MethodBody, PendingMethodOps, Vec<u32>, u32), Error> {
    let raw_code = reader
        .open_code(code_off)
        .ok_or(Error::InvalidOffset(code_off))?;
    let raw_insns = raw_code.instructions;
    let legacy = dialect == Dialect::DynamicLegacy;

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

    let insn_count = decoded.len() as u32;
    let code_byte_len = raw_insns.len() as u32;

    let mut entity_ops = Vec::new();
    let mut legacy_buf_ops = Vec::new();
    for (bc, _) in &decoded {
        let (ops, ops_len) = bc.entity_operands_inline();
        for &(kind, id) in &ops[..ops_len] {
            if matches!(
                kind,
                abcd_isa::EntityKind::StringId
                    | abcd_isa::EntityKind::MethodId
                    | abcd_isa::EntityKind::LiteralarrayId
            ) {
                entity_ops.push(RawEntityOp {
                    kind,
                    raw_id: id.0,
                    mnemonic: bc.mnemonic(),
                });
            }
        }
        if legacy {
            use abcd_isa::Bytecode as B;
            match bc {
                B::DeprecatedCreateobjectwithbuffer(abcd_isa::Imm(i))
                | B::DeprecatedCreatearraywithbuffer(abcd_isa::Imm(i))
                | B::DeprecatedCreateobjecthavingmethod(abcd_isa::Imm(i))
                | B::DeprecatedDefineclasswithbuffer(_, abcd_isa::Imm(i), _, _, _) => {
                    legacy_buf_ops.push(RawLegacyBufOp {
                        global_idx: *i,
                        mnemonic: bc.mnemonic(),
                    });
                }
                _ => {}
            }
        }
    }

    let (bytecodes_opt, byte_offsets): (Option<Vec<Bytecode>>, Vec<u32>) = if lazy_backing.is_some()
    {
        let offsets: Vec<u32> = decoded.into_iter().map(|(_, off)| off).collect();
        (None, offsets)
    } else {
        let (bcs, offsets): (Vec<_>, Vec<_>) = decoded.into_iter().unzip();
        (Some(bcs), offsets)
    };

    let exact_pc_to_index = |pc: u32, field: &'static str, label: &str| -> Result<u32, Error> {
        if pc == code_byte_len {
            return Ok(insn_count);
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

    let raw_try_blocks = raw_code.read_try_blocks().ok_or_else(|| Error::Malformed {
        field: "try_block",
        context: format!(
            "method at offset {method_off:#x}: truncated or malformed try/catch table"
        ),
    })?;

    let mut try_blocks = Vec::with_capacity(raw_try_blocks.len());
    for tb in raw_try_blocks {
        let end_pc = tb
            .start_pc
            .checked_add(tb.length)
            .ok_or_else(|| Error::Malformed {
                field: "try_block",
                context: format!("method at offset {method_off:#x}: try span overflow"),
            })?;
        let start = exact_pc_to_index(tb.start_pc, "try_block", "try start")?;
        let end = exact_pc_to_index(end_pc, "try_block", "try end")?;
        let mut catches = Vec::with_capacity(tb.catches.len());
        for cb in tb.catches {
            let type_class_off = match cb.type_idx {
                None => None,
                Some(idx) => {
                    let resolved = reader
                        .resolve_class_index(method_off, idx)
                        .ok_or(Error::InvalidOffset(u32::from(idx)))?;
                    Some(resolved)
                }
            };
            let handler_end_pc =
                cb.handler_pc
                    .checked_add(cb.code_size)
                    .ok_or_else(|| Error::Malformed {
                        field: "catch_block",
                        context: format!("method at offset {method_off:#x}: catch span overflow"),
                    })?;
            let handler = exact_pc_to_index(cb.handler_pc, "catch_block", "catch handler")?;
            let handler_end = exact_pc_to_index(handler_end_pc, "catch_block", "catch end")?;
            let type_class = match type_class_off {
                None => None,
                Some(class_off) => {
                    let sid = entity_map
                        .get(&class_off)
                        .copied()
                        .or_else(|| {
                            reader
                                .is_external(class_off)
                                .then(|| str_cache.intern_lossy(reader, class_off, strings))
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

    let code = match (lazy_backing, bytecodes_opt) {
        (Some(arc), _) => MethodCode::Span(MethodSpan {
            backing: Arc::clone(arc),
            offset: raw_code.insns_off,
            len: raw_code.code_size,
            insn_count,
            legacy,
        }),
        (None, Some(bcs)) => MethodCode::Decoded(bcs),
        (None, None) => MethodCode::Decoded(Vec::new()),
    };

    Ok((
        MethodBody {
            num_vregs: raw_code.num_vregs,
            num_args: raw_code.num_args,
            code,
            entities: MethodEntities::new(),
            try_blocks,
            ic_size: None,
        },
        PendingMethodOps {
            method_off,
            entity_ops,
            legacy_buf_ops,
        },
        byte_offsets,
        code_byte_len,
    ))
}

fn decode_proto_types(
    reader: &AbcReader<'_>,
    proto_off: u32,
    entity_map: &HashMap<u32, StringId>,
) -> Result<(Type, Vec<Type>), Error> {
    let Some(proto) = reader.open_proto(proto_off) else {
        return Err(Error::UnknownTypeId(u8::MAX));
    };
    let ref_num = proto.ref_types_sp.len() / 2;
    let mut next_ref = 0usize;
    let mut resolve = |raw: TypeId, ctx: &str| -> Result<Type, Error> {
        if raw == TypeId::Reference {
            if next_ref >= ref_num {
                return Err(Error::Malformed {
                    field: "reference_type",
                    context: ctx.to_string(),
                });
            }
            let off = proto.reference_type_off(reader, next_ref);
            next_ref += 1;
            let desc = off
                .and_then(|o| entity_map.get(&o).copied())
                .ok_or_else(|| Error::Malformed {
                    field: "reference_type",
                    context: ctx.to_string(),
                })?;
            Ok(Type::Reference(desc))
        } else {
            Type::from_raw(raw, None)
        }
    };

    let raw_ret = TypeId::try_from(proto.return_type_raw())?;
    let return_type = resolve(raw_ret, "return type")?;

    let mut arg_types = Vec::with_capacity(proto.num_args());
    for i in 0..proto.num_args() {
        let raw = TypeId::try_from(proto.arg_type_raw(i))?;
        arg_types.push(resolve(raw, &format!("arg {i}"))?);
    }
    Ok((return_type, arg_types))
}

#[expect(
    clippy::too_many_arguments,
    reason = "param annotation decoder threads forensic diagnostics, entity map, and string cache"
)]
fn decode_param_annotations(
    reader: &AbcReader<'_>,
    raw_m: &RawMethod,
    num_params: usize,
    forensic: bool,
    diagnostics: &mut DecodeDiagnostics,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache,
    ann_visiting: &mut HashSet<u32>,
) -> Result<ParamAnnotations, Error> {
    let mut result = ParamAnnotations::default();
    for (is_runtime, item_off_opt) in [
        (false, raw_m.param_annotations_off),
        (true, raw_m.runtime_param_annotations_off),
    ] {
        let Some(item_off) = item_off_opt else {
            continue;
        };
        let Some(pairs) = reader.read_param_annotations(item_off) else {
            let err = Error::Malformed {
                field: "param_annotations",
                context: format!("param annotations item at offset {item_off:#x}"),
            };
            if forensic {
                diagnostics.push(DecodeDiagnostic {
                    kind: "param_annotations",
                    offset: Some(item_off),
                    message: err.to_string(),
                });
                continue;
            }
            return Err(err);
        };
        if pairs.is_empty() {
            continue;
        }
        let bucket = if is_runtime {
            &mut result.runtime
        } else {
            &mut result.compile_time
        };
        let Some(max_end) = pairs.iter().try_fold(0usize, |acc, &(i, _)| {
            i.checked_add(1)
                .and_then(|n| usize::try_from(n).ok())
                .map(|n| acc.max(n))
        }) else {
            let err = Error::Malformed {
                field: "param_annotations",
                context: format!("param annotations item at offset {item_off:#x}"),
            };
            if forensic {
                diagnostics.push(DecodeDiagnostic {
                    kind: "param_annotations",
                    offset: Some(item_off),
                    message: err.to_string(),
                });
                continue;
            }
            return Err(err);
        };
        let len = num_params.max(max_end);
        bucket.resize(len, Vec::new());
        for (idx, off) in pairs {
            let anns = decode_annotation_list(
                reader,
                &[off],
                forensic,
                diagnostics,
                entity_map,
                strings,
                str_cache,
                ann_visiting,
            )?;
            bucket[idx as usize].extend(anns);
        }
    }
    Ok(result)
}

fn decode_module_data_at(
    reader: &AbcReader<'_>,
    offset: u32,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache,
) -> Result<ModuleData, Error> {
    if reader.get_span(offset).is_none() {
        return Err(Error::InvalidOffset(offset));
    }
    let raw = reader
        .read_module_data(offset)
        .ok_or_else(|| Error::Malformed {
            field: "module_data",
            context: format!("truncated or malformed module record blob at {offset:#x}"),
        })?;

    let mut intern_str = |off: u32, pool: &mut StringPool| -> Result<StringId, Error> {
        str_cache
            .intern_utf8(reader, off, pool)
            .ok_or(Error::InvalidString(off))
    };

    let mut requests = Vec::with_capacity(raw.request_offs.len());
    for off in raw.request_offs {
        if off == ABSENT {
            return Err(Error::InvalidString(off));
        }
        requests.push(intern_str(off, strings)?);
    }

    let mut records = Vec::with_capacity(raw.records.len());
    for rec in raw.records {
        let record = match rec {
            RawModuleRecord::RegularImport {
                local_off,
                import_off,
                req_idx,
            } => ModuleRecord::RegularImport {
                local_name: intern_str(local_off, strings)?,
                import_name: intern_str(import_off, strings)?,
                module_request_idx: req_idx,
            },
            RawModuleRecord::NamespaceImport { local_off, req_idx } => {
                ModuleRecord::NamespaceImport {
                    local_name: intern_str(local_off, strings)?,
                    module_request_idx: req_idx,
                }
            }
            RawModuleRecord::LocalExport {
                local_off,
                export_off,
            } => ModuleRecord::LocalExport {
                local_name: intern_str(local_off, strings)?,
                export_name: intern_str(export_off, strings)?,
            },
            RawModuleRecord::IndirectExport {
                export_off,
                import_off,
                req_idx,
            } => ModuleRecord::IndirectExport {
                export_name: intern_str(export_off, strings)?,
                import_name: intern_str(import_off, strings)?,
                module_request_idx: req_idx,
            },
            RawModuleRecord::StarExport { req_idx } => ModuleRecord::StarExport {
                module_request_idx: req_idx,
            },
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
    reader: &AbcReader<'_>,
    offset: u32,
) -> Result<crate::ModuleRequestPhase, Error> {
    let flags = reader.read_module_request_phase(offset).ok_or_else(|| {
        Error::ModuleData(format!(
            "module-request-phase blob at {offset:#x} is unreadable"
        ))
    })?;
    Ok(crate::ModuleRequestPhase {
        source_offset: offset,
        flags,
    })
}

#[expect(
    clippy::too_many_arguments,
    reason = "field decoder threads forensic diagnostics, discovery offset sets, and string cache"
)]
pub(super) fn decode_field_item(
    reader: &AbcReader<'_>,
    raw_f: &RawField,
    forensic: bool,
    diagnostics: &mut DecodeDiagnostics,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache,
    ann_visiting: &mut HashSet<u32>,
    class_descriptor: &str,
    module_data_offsets: &mut HashSet<u32>,
    scope_names_offsets: &mut HashSet<u32>,
    phase_blob_offsets: &mut HashSet<u32>,
) -> Result<Field, Error> {
    let field_off = raw_f.offset;
    let name = if raw_f.name_off == ABSENT {
        return Err(Error::Malformed {
            field: "name",
            context: format!("field at offset {field_off:#x}"),
        });
    } else {
        str_cache
            .intern_lossy(reader, raw_f.name_off, strings)
            .ok_or_else(|| Error::Malformed {
                field: "name",
                context: format!("field at offset {field_off:#x}"),
            })?
    };

    let type_id = raw_f.type_id;
    let field_type = if type_id == TypeId::Reference {
        let type_sid =
            entity_map
                .get(&raw_f.type_off)
                .copied()
                .ok_or_else(|| Error::Malformed {
                    field: "field_type",
                    context: format!("field {:?}", strings.resolve(name).unwrap_or("?")),
                })?;
        Type::Reference(type_sid)
    } else {
        Type::from_raw(type_id, None)?
    };

    let base_value = match (type_id, raw_f.raw_value) {
        (_, None) | (TypeId::Void, _) => Ok(None),
        (
            TypeId::U1
            | TypeId::I8
            | TypeId::U8
            | TypeId::I16
            | TypeId::U16
            | TypeId::I32
            | TypeId::U32
            | TypeId::Tagged,
            Some(rv),
        ) => Ok(Some(FieldValue::I32(rv.as_i32()))),
        (TypeId::I64 | TypeId::U64, Some(rv)) => Ok(Some(FieldValue::I64(rv.as_i64()))),
        (TypeId::F32, Some(rv)) => Ok(Some(FieldValue::F32(rv.as_f32()))),
        (TypeId::F64, Some(rv)) => Ok(Some(FieldValue::F64(rv.as_f64()))),
        (TypeId::Reference, Some(rv)) => {
            let offset = rv.as_u32();
            if offset == 0 {
                Err(Error::InvalidString(0))
            } else {
                str_cache
                    .intern_lossy(reader, offset, strings)
                    .map(|sid| Some(FieldValue::String(sid)))
                    .ok_or(Error::InvalidString(offset))
            }
        }
    };

    let initial_value_raw = match base_value {
        Ok(v) => v,
        Err(err) => {
            if forensic {
                diagnostics.push(DecodeDiagnostic {
                    kind: "field_value",
                    offset: Some(field_off),
                    message: err.to_string(),
                });
                None
            } else {
                return Err(err);
            }
        }
    };

    let resolved_u32_val: Result<Option<FieldValue>, Error> =
        match (class_descriptor, type_id, initial_value_raw) {
            (_, TypeId::U32, Some(FieldValue::I32(off)))
                if strings.resolve(name) == Some(TYPE_SUMMARY_OFFSET_FIELD) =>
            {
                let offset = off as u32;
                if offset == 0 {
                    Ok(Some(FieldValue::I32(0)))
                } else if entity_map.contains_key(&offset)
                    || walk_raw_literal_array(reader, offset, |_| Ok(())).is_err()
                {
                    Err(Error::InvalidOffset(offset))
                } else {
                    scope_names_offsets.insert(offset);
                    Ok(Some(FieldValue::LiteralArrayRef {
                        index: LiteralArrayIdx(offset),
                        source_offset: Some(offset),
                    }))
                }
            }
            (_, TypeId::U32, Some(FieldValue::I32(off)))
                if strings.resolve(name) == Some(MODULE_REQUEST_PHASE_FIELD) =>
            {
                match u32::try_from(off) {
                    Err(_) => Err(Error::ModuleData(format!(
                        "{class_descriptor} field at {field_off:#x}: negative blob offset {off}"
                    ))),
                    Ok(offset) => match decode_module_request_phase_at(reader, offset) {
                        Ok(phase) => {
                            phase_blob_offsets.insert(offset);
                            Ok(Some(FieldValue::ModuleRequestPhase(phase)))
                        }
                        Err(e) => Err(Error::ModuleData(format!(
                            "{class_descriptor} moduleRequestPhaseIdx field at {field_off:#x}: {e}"
                        ))),
                    },
                }
            }
            (desc, TypeId::U32, Some(FieldValue::I32(off)))
                if desc == ES_MODULE_RECORD_DESCRIPTOR
                    || strings.resolve(name) == Some(MODULE_RECORD_IDX_FIELD) =>
            {
                match u32::try_from(off) {
                    Err(_) => Err(Error::ModuleData(format!(
                        "{class_descriptor} field at {field_off:#x}: negative blob offset {off}"
                    ))),
                    Ok(offset) => match decode_module_data_at(reader, offset, strings, str_cache) {
                        Ok(d) => {
                            module_data_offsets.insert(offset);
                            Ok(Some(FieldValue::ModuleData(d)))
                        }
                        Err(e @ Error::Malformed { .. }) => Err(e),
                        Err(e) => Err(Error::ModuleData(format!(
                            "{class_descriptor} field at {field_off:#x}: {e}"
                        ))),
                    },
                }
            }
            (desc, TypeId::U32, Some(FieldValue::I32(off)))
                if desc == ES_SCOPE_NAMES_RECORD_DESCRIPTOR
                    || strings.resolve(name) == Some(SCOPE_NAMES_FIELD) =>
            {
                match u32::try_from(off) {
                    Err(_) => Err(Error::ModuleData(format!(
                        "{class_descriptor} field at {field_off:#x}: negative blob offset {off}"
                    ))),
                    Ok(offset) => {
                        scope_names_offsets.insert(offset);
                        Ok(Some(FieldValue::LiteralArrayRef {
                            index: LiteralArrayIdx(offset),
                            source_offset: Some(offset),
                        }))
                    }
                }
            }
            (_, TypeId::U32, Some(FieldValue::I32(off)))
                if strings.resolve(name) == Some(JSON_FILE_CONTENT_FIELD) =>
            {
                let offset = off as u32;
                if offset == 0 {
                    Err(Error::InvalidString(0))
                } else {
                    str_cache
                        .intern_lossy(reader, offset, strings)
                        .map(|content| {
                            Some(FieldValue::JsonFileContent {
                                source_offset: offset,
                                content,
                            })
                        })
                        .ok_or(Error::InvalidString(offset))
                }
            }
            (_, TypeId::U32, Some(FieldValue::I32(off)))
                if matches!(raw_f.raw_value, Some(RawFieldValue::Bits32(_))) =>
            {
                let offset = off as u32;
                if offset == 0 {
                    Err(Error::InvalidString(0))
                } else {
                    str_cache
                        .intern_lossy(reader, offset, strings)
                        .map(|sid| Some(FieldValue::String(sid)))
                        .ok_or(Error::InvalidString(offset))
                }
            }
            (_, _, value) => Ok(value),
        };

    let initial_value = match resolved_u32_val {
        Ok(v) => v,
        Err(err) => {
            if forensic {
                diagnostics.push(DecodeDiagnostic {
                    kind: "field_value",
                    offset: Some(field_off),
                    message: err.to_string(),
                });
                None
            } else {
                return Err(err);
            }
        }
    };

    let annotations = Annotations {
        compile_time: decode_annotation_list(
            reader,
            &raw_f.annotations,
            forensic,
            diagnostics,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        runtime: decode_annotation_list(
            reader,
            &raw_f.runtime_annotations,
            forensic,
            diagnostics,
            entity_map,
            strings,
            str_cache,
            ann_visiting,
        )?,
        compile_time_type: Vec::new(),
        runtime_type: Vec::new(),
    };

    Ok(Field {
        name,
        offset: field_off,
        field_type,
        access_flags: AccessFlags::from_bits_truncate(raw_f.access_flags),
        is_external: raw_f.is_external,
        initial_value,
        annotations,
    })
}

fn resolve_foreign_entity_name(
    reader: &AbcReader<'_>,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache,
    off: u32,
) -> StringId {
    if let Some(&sid) = entity_map.get(&off) {
        return sid;
    }
    let Some(name_off) = reader.foreign_item_name_off(off) else {
        return strings.get_or_intern("");
    };
    str_cache
        .intern_utf8(reader, name_off, strings)
        .unwrap_or_else(|| strings.get_or_intern(""))
}

#[expect(
    clippy::too_many_arguments,
    reason = "annotation list decoder threads forensic diagnostics, entity map, and string cache"
)]
pub(super) fn decode_annotation_list(
    reader: &AbcReader<'_>,
    offsets: &[u32],
    forensic: bool,
    diagnostics: &mut DecodeDiagnostics,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache,
    ann_visiting: &mut HashSet<u32>,
) -> Result<Vec<Annotation>, Error> {
    let mut out = Vec::with_capacity(offsets.len());
    for &off in offsets {
        match decode_annotation_at(reader, off, entity_map, strings, str_cache, ann_visiting) {
            Ok(ann) => out.push(ann),
            Err(err) => {
                if forensic {
                    diagnostics.push(DecodeDiagnostic {
                        kind: "annotation",
                        offset: Some(off),
                        message: err.to_string(),
                    });
                } else {
                    return Err(err);
                }
            }
        }
    }
    Ok(out)
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

struct AnnDecodeFrame<'a> {
    off: u32,
    ar: RawAnnotation<'a>,
    class_descriptor: StringId,
    next_idx: u16,
    elements: Vec<AnnotationElem>,
    pending: Option<PendingAnnSlot>,
}

fn open_ann_frame<'a>(
    reader: &AbcReader<'a>,
    off: u32,
    entity_map: &HashMap<u32, StringId>,
    visiting: &mut HashSet<u32>,
) -> Result<AnnDecodeFrame<'a>, Error> {
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
    let Some(class_descriptor) = entity_map.get(&ar.class_off).copied() else {
        visiting.remove(&off);
        return Err(Error::Malformed {
            field: "class_descriptor",
            context: format!("annotation at offset {off:#x}"),
        });
    };
    let max_elems = (reader.file_size().saturating_sub(off) / 9) as usize;
    Ok(AnnDecodeFrame {
        off,
        class_descriptor,
        next_idx: 0,
        elements: Vec::with_capacity(usize::from(ar.count).min(max_elems)),
        pending: None,
        ar,
    })
}

fn decode_annotation_at(
    reader: &AbcReader<'_>,
    root_off: u32,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache,
    visiting: &mut HashSet<u32>,
) -> Result<Annotation, Error> {
    use sys::AnnotationValueType as AVT;

    visiting.clear();
    let mut stack: Vec<AnnDecodeFrame<'_>> =
        vec![open_ann_frame(reader, root_off, entity_map, visiting)?];
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
                        let child = open_ann_frame(reader, next_off, entity_map, visiting)?;
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

        let mut next_child: Option<AnnDecodeFrame<'_>> = None;
        while frame.next_idx < frame.ar.count {
            let idx = frame.next_idx;
            frame.next_idx += 1;
            let off = frame.off;

            let Some((name_off, raw_tag, raw_val)) = frame.ar.element(idx) else {
                return Err(Error::Malformed {
                    field: "annotation element",
                    context: format!("annotation at offset {off:#x}, element {idx}"),
                });
            };
            let name = str_cache
                .intern_utf8(reader, name_off, strings)
                .ok_or(Error::InvalidString(name_off))?;
            let tag = AVT::try_from(raw_tag).unwrap_or(AVT::Unknown);
            let value = match tag {
                AVT::U1 => AnnotationValue::Bool(raw_val != 0),
                AVT::I8 => AnnotationValue::I8(raw_val as i8),
                AVT::U8 => AnnotationValue::U8(raw_val as u8),
                AVT::I16 => AnnotationValue::I16(raw_val as i16),
                AVT::U16 => AnnotationValue::U16(raw_val as u16),
                AVT::I32 => AnnotationValue::I32(raw_val as i32),
                AVT::U32 => AnnotationValue::U32(raw_val),
                AVT::I64 => {
                    let v = reader
                        .read_scalar_u64(raw_val)
                        .ok_or_else(|| Error::Malformed {
                            field: "annotation element value",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx} (tag {tag:?})"
                            ),
                        })?;
                    AnnotationValue::I64(v as i64)
                }
                AVT::U64 => {
                    let v = reader
                        .read_scalar_u64(raw_val)
                        .ok_or_else(|| Error::Malformed {
                            field: "annotation element value",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx} (tag {tag:?})"
                            ),
                        })?;
                    AnnotationValue::U64(v)
                }
                AVT::F32 => AnnotationValue::F32(f32::from_bits(raw_val)),
                AVT::F64 => {
                    let v = reader
                        .read_scalar_u64(raw_val)
                        .ok_or_else(|| Error::Malformed {
                            field: "annotation element value",
                            context: format!(
                                "annotation at offset {off:#x}, element {idx} (tag {tag:?})"
                            ),
                        })?;
                    AnnotationValue::F64(f64::from_bits(v))
                }
                AVT::String => {
                    let sid = str_cache
                        .intern_utf8(reader, raw_val, strings)
                        .ok_or(Error::InvalidString(raw_val))?;
                    AnnotationValue::String(sid)
                }
                AVT::Record => {
                    let sid = entity_map
                        .get(&raw_val)
                        .copied()
                        .ok_or(Error::InvalidOffset(raw_val))?;
                    AnnotationValue::Record(sid)
                }
                AVT::Method => {
                    let sid = resolve_foreign_entity_name(
                        reader, entity_map, strings, str_cache, raw_val,
                    );
                    AnnotationValue::Method {
                        name: sid,
                        method: None,
                        offset: raw_val,
                    }
                }
                AVT::Enum => {
                    let sid = resolve_foreign_entity_name(
                        reader, entity_map, strings, str_cache, raw_val,
                    );
                    AnnotationValue::Enum {
                        name: sid,
                        field: None,
                        offset: raw_val,
                    }
                }
                AVT::Annotation => {
                    frame.pending = Some(PendingAnnSlot::Scalar { name });
                    next_child = Some(open_ann_frame(reader, raw_val, entity_map, visiting)?);
                    break;
                }
                AVT::MethodHandle => {
                    let Some((ht_raw, entity_off)) = reader.read_method_handle(raw_val) else {
                        return Err(Error::Malformed {
                            field: "method_handle",
                            context: format!("annotation at offset {off:#x}, element {idx}"),
                        });
                    };
                    let ht = MethodHandleType::from_u8(ht_raw).ok_or_else(|| Error::Malformed {
                        field: "method_handle_type",
                        context: format!(
                            "annotation at offset {off:#x}, element {idx}: unknown handle type {ht_raw:#x}"
                        ),
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
                    let values = decode_literal_array_values(reader, raw_val, strings, str_cache)?;
                    AnnotationValue::LiteralArray(values)
                }
                AVT::Void => AnnotationValue::Void,
                AVT::StringNullptr => AnnotationValue::StringNullptr,
                AVT::ArrayAnnotation => {
                    let (_, raw_values) =
                        read_annotation_array_from_elem(reader, off, idx, raw_tag, raw_val)?;
                    let mut offsets_iter = raw_values
                        .into_iter()
                        .map(|v| v as u32)
                        .collect::<Vec<_>>()
                        .into_iter();
                    if let Some(first_off) = offsets_iter.next() {
                        frame.pending = Some(PendingAnnSlot::Array {
                            name,
                            tag: raw_tag,
                            decoded: Vec::with_capacity(offsets_iter.len().saturating_add(1)),
                            remaining: offsets_iter,
                        });
                        next_child = Some(open_ann_frame(reader, first_off, entity_map, visiting)?);
                        break;
                    }
                    AnnotationValue::Array {
                        tag: raw_tag,
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
                    let (avt, raw_values) =
                        read_annotation_array_from_elem(reader, off, idx, raw_tag, raw_val)?;
                    let values = convert_annotation_array_values(
                        reader, raw_tag, avt, raw_val, raw_values, entity_map, strings, str_cache,
                    )?;
                    AnnotationValue::Array {
                        tag: raw_tag,
                        values,
                    }
                }
                AVT::Unknown => {
                    return Err(Error::Malformed {
                        field: "annotation element tag",
                        context: format!(
                            "annotation at offset {off:#x}, element {idx}: unknown tag {raw_tag:#x}"
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

fn annotation_array_elem_size(
    tag: u8,
    entity_offset: u32,
) -> Result<(sys::AnnotationValueType, usize), Error> {
    use sys::AnnotationValueType as AVT;

    match AVT::try_from(tag) {
        Ok(t @ (AVT::ArrayU1 | AVT::ArrayI8 | AVT::ArrayU8)) => Ok((t, 1)),
        Ok(t @ (AVT::ArrayI16 | AVT::ArrayU16)) => Ok((t, 2)),
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
        ) => Ok((t, 4)),
        Ok(t @ (AVT::ArrayI64 | AVT::ArrayU64 | AVT::ArrayF64)) => Ok((t, 8)),
        _ => Err(Error::Malformed {
            field: "annotation array element tag",
            context: format!(
                "annotation array at offset {entity_offset:#x}: tag {tag:#x} has no defined element size"
            ),
        }),
    }
}

pub(super) fn read_annotation_array_from_elem(
    reader: &AbcReader<'_>,
    ann_off: u32,
    elem_idx: u16,
    tag: u8,
    entity_offset: u32,
) -> Result<(sys::AnnotationValueType, Vec<u64>), Error> {
    // Match `abc_annotation_get_array_element` check first: `[uleb count]` must
    // satisfy `count <= rem_bytes` inside `get_span(entity_offset)`.
    let mut check_sp = reader
        .get_span(entity_offset)
        .ok_or_else(|| Error::Malformed {
            field: "annotation array element",
            context: format!("annotation at offset {ann_off:#x}, element {elem_idx}"),
        })?;
    let declared_count =
        crate::file::read_uleb128(&mut check_sp).ok_or_else(|| Error::Malformed {
            field: "annotation array element",
            context: format!("annotation at offset {ann_off:#x}, element {elem_idx}"),
        })?;
    if (declared_count as usize) > check_sp.len() {
        return Err(Error::Malformed {
            field: "annotation array element",
            context: format!("annotation at offset {ann_off:#x}, element {elem_idx}"),
        });
    }

    let (avt, elem_size) = annotation_array_elem_size(tag, entity_offset)?;
    if declared_count == 0 {
        return Ok((avt, Vec::new()));
    }
    let raw_values = reader
        .read_annotation_array(entity_offset, elem_size)
        .ok_or_else(|| Error::Malformed {
            field: "annotation array data",
            context: format!("annotation array at offset {entity_offset:#x}"),
        })?;
    Ok((avt, raw_values))
}

#[expect(
    clippy::too_many_arguments,
    reason = "annotation array converter resolves raw element words against entity_map and StringPool"
)]
fn convert_annotation_array_values(
    reader: &AbcReader<'_>,
    tag: u8,
    avt: sys::AnnotationValueType,
    entity_offset: u32,
    raw_values: Vec<u64>,
    entity_map: &HashMap<u32, StringId>,
    strings: &mut StringPool,
    str_cache: &mut StringItemCache,
) -> Result<Vec<AnnotationValue>, Error> {
    use sys::AnnotationValueType as AVT;

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
                let sid = str_cache
                    .intern_utf8(reader, raw as u32, strings)
                    .ok_or(Error::InvalidString(raw as u32))?;
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
                let sid =
                    resolve_foreign_entity_name(reader, entity_map, strings, str_cache, raw as u32);
                AnnotationValue::Method {
                    name: sid,
                    method: None,
                    offset: raw as u32,
                }
            }
            AVT::ArrayEnum => {
                let sid =
                    resolve_foreign_entity_name(reader, entity_map, strings, str_cache, raw as u32);
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
            AVT::LiteralArray => AnnotationValue::LiteralArray(decode_literal_array_values(
                reader, raw as u32, strings, str_cache,
            )?),
            AVT::ArrayMethodHandle => {
                let Some((ht_raw, entity_off)) = reader.read_method_handle(raw as u32) else {
                    return Err(Error::Malformed {
                        field: "method_handle",
                        context: format!("annotation array at offset {entity_offset:#x}"),
                    });
                };
                let ht = MethodHandleType::from_u8(ht_raw).ok_or_else(|| Error::Malformed {
                    field: "method_handle_type",
                    context: format!(
                        "annotation array at offset {entity_offset:#x}: unknown handle type {ht_raw:#x}"
                    ),
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
