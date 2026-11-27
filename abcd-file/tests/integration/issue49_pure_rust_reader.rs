//! Comprehensive L1 & differential C++ oracle tests for Issues `#49`, `#72`, and `#77`:
//!
//! 1. Differential oracle vs. `abcd-file-sys` (`abc_file_open` C++ accessors) across
//!    API 9 (typed `ProtoItem` + dual-bucket `ParamAnnotations` + all 4 wire annotation
//!    retention tags) and API 12 (`0xFFFF` no-proto sentinel, foreign items, fields,
//!    try/catch blocks, debug info, nested literal arrays, module records + lazy-import
//!    phase flags, and lone-surrogate raw MUTF-8 strings).
//! 2. Lazy (`decode_lazy` / `MethodCode::Span`) vs. Eager (`decode` / `MethodCode::Decoded`)
//!    bit-identical `pandasm::emit_file` and `encode` output across modern (`12.x`, `24.x`)
//!    and legacy (`0.0.0.2`) containers, plus `MethodEntities` & `MethodCode` API coverage.
//! 3. `DecodeMode::Forensic` fault-tolerant recovery on corrupted Adler-32 checksums,
//!    corrupted DWARF/LNP debug streams, and invalid/truncated method bytecodes alongside
//!    healthy methods, plus `256 KiB`-stack iterative deep-nesting checks.
//! 4. Static header layouts (`0.0.0.5` 64B, `0.0.0.6` 72B count-based, `0.1.0.7` 72B/60B
//!    byte-len-based) and `0.0.0.3` 60B dynamic container classification & inspection.
//! 5. `SummaryStrings` SipHash collision resilience (`#77`) and flat-arena `StringPool`
//!    `drop_index()`, `has_index()`, `lossy_ids()`, `R2-M9`, and `u32` overflow bounds (`#72`).

use std::borrow::Cow;
use std::collections::HashMap;
use std::ffi::CStr;
use std::sync::Arc;

use abcd_file::{
    AccessFlags, AnnotationElemDefEx, AnnotationElemValue, AnnotationValue, Builder, CatchBlockDef,
    CodeEntity, DecodeMode, DecodeOptions, Dialect, ES_MODULE_RECORD_DESCRIPTOR,
    ES_SCOPE_NAMES_RECORD_DESCRIPTOR, EntityRef, Error, FieldValue, FileType, FunctionKind,
    JSON_FILE_CONTENT_FIELD, MODULE_RECORD_IDX_FIELD, MODULE_REQUEST_PHASE_FIELD, MethodCode,
    MethodEntities, ModuleRecord, ModuleRecordDef, SCOPE_NAMES_FIELD, SourceLang, StringId,
    StringPool, TYPE_SUMMARY_OFFSET_FIELD, Type, Version, adler32_abc, decode, decode_arc,
    decode_lazy, decode_with_options, encode, file_type, inspect_summary, pandasm,
    validate_checksum,
};
use abcd_file_sys as sys;
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Reg, insn};

// ===========================================================================
// 1. Differential Oracle vs. `abcd-file-sys` (`abc_file_open`)
// ===========================================================================

/// Synthesize a rich API-12 `.abc` exercising foreign + local classes, super/interfaces,
/// typed & metadata fields, nested annotations + `MethodHandle`, try/catch blocks,
/// DWARF/LNP debug info (lines, columns, locals, params, source file/code), nested
/// literal arrays, ES module records + phase flags, and lone-surrogate raw MUTF-8 strings.
fn build_rich_api12_fixture(include_foreign_call_operand: bool) -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");

    // Foreign class, method, and field.
    let foreign_cls = b.add_foreign_class("LForeignPkg/ExtBase;");
    let empty_proto = b.create_proto(Type::Tagged, &[]);
    let foreign_fn = b.add_foreign_method(
        foreign_cls,
        "extHelper",
        empty_proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
    );
    let _foreign_fld = b.add_foreign_field(foreign_cls, "extField", Type::I32);

    // Local hierarchy: LBase;, LIfc;, LDerived;.
    let base_cls = b.add_class("LBase;");
    b.class_set_source_lang(base_cls, SourceLang::EcmaScript);
    b.class_set_access_flags(base_cls, AccessFlags::PUBLIC);

    let ifc_cls = b.add_class("LIfc;");
    b.class_set_source_lang(ifc_cls, SourceLang::EcmaScript);
    b.class_set_access_flags(ifc_cls, AccessFlags::PUBLIC | AccessFlags::INTERFACE);

    let derived_cls = b.add_class("LDerived;");
    b.class_set_source_lang(derived_cls, SourceLang::EcmaScript);
    b.class_set_access_flags(derived_cls, AccessFlags::PUBLIC);
    b.class_set_super_class(derived_cls, base_cls);
    b.class_add_interface(derived_cls, ifc_cls);
    let src_file_str = b.add_string("derived.ts");
    b.class_set_source_file(derived_cls, src_file_str);

    // Typed fields on LDerived;.
    let f_i32 = b.class_add_field(derived_cls, "count", Type::I32, AccessFlags::PUBLIC);
    b.field_set_value_i32(f_i32, -42);
    let f_i64 = b.class_add_field(derived_cls, "stamp", Type::I64, AccessFlags::PUBLIC);
    b.field_set_value_i64(f_i64, 0x0123_4567_89AB_CDEF);
    let f_f32 = b.class_add_field(derived_cls, "ratio", Type::F32, AccessFlags::PUBLIC);
    b.field_set_value_f32(f_f32, 1.5);
    let f_f64 = b.class_add_field(derived_cls, "pi", Type::F64, AccessFlags::PUBLIC);
    b.field_set_value_f64(f_f64, 3.125);
    let json_str = b.add_string("{\"ok\":true}");
    let f_json = b.class_add_field(
        derived_cls,
        JSON_FILE_CONTENT_FIELD,
        Type::U32,
        AccessFlags::STATIC,
    );
    b.field_set_value_string(f_json, json_str)
        .expect("json string field");

    // Lone-surrogate raw MUTF-8 string (unpaired U+D800: ED A0 80).
    let lone_surrogate = b
        .add_string_mutf8(&[0xED, 0xA0, 0x80])
        .expect("lone surrogate MUTF-8");

    // Nested literal arrays: child_la referenced inside parent_la.
    let child_la = b.add_literal_array("child_lit");
    b.literal_array_add_integer(child_la, 777);
    b.literal_array_add_string(child_la, lone_surrogate);

    let parent_la = b.add_literal_array("parent_lit");
    b.literal_array_add_bool(parent_la, true);
    b.literal_array_add_literalarray(parent_la, child_la);

    // Type-summary literal array on L_GLOBAL;.
    let global_cls = b.add_global_class();
    b.class_set_source_lang(global_cls, SourceLang::EcmaScript);
    let ts_la = b.add_literal_array("type_summary");
    b.literal_array_add_integer(ts_la, 1);
    let f_ts = b.class_add_field(
        global_cls,
        TYPE_SUMMARY_OFFSET_FIELD,
        Type::U32,
        AccessFlags::STATIC,
    );
    b.field_set_value_literalarray(f_ts, ts_la)
        .expect("typeSummaryOffset");

    // Scope names record & ES module record + moduleRequestPhaseIdx.
    let scope_cls = b.add_class(ES_SCOPE_NAMES_RECORD_DESCRIPTOR);
    b.class_set_source_lang(scope_cls, SourceLang::EcmaScript);
    let scope_la = b.add_literal_array("scopes");
    let scope_name = b.add_string("block_scope_0");
    b.literal_array_add_string(scope_la, scope_name);
    let f_scope = b.class_add_field(scope_cls, SCOPE_NAMES_FIELD, Type::U32, AccessFlags::STATIC);
    b.field_set_value_literalarray(f_scope, scope_la)
        .expect("scopeNames");

    let mod_cls = b.add_class(ES_MODULE_RECORD_DESCRIPTOR);
    b.class_set_source_lang(mod_cls, SourceLang::EcmaScript);
    let req0 = b.add_string("./dep_a.ets");
    let req1 = b.add_string("./dep_b.ets");
    let imp_name = b.add_string("foo");
    let loc_name = b.add_string("localFoo");
    let exp_name = b.add_string("bar");
    let mod_la = b.add_literal_array("mod_data");
    b.literal_array_add_module_data(
        mod_la,
        &[req0, req1],
        &[
            ModuleRecordDef::RegularImport {
                local_name: loc_name,
                import_name: imp_name,
                module_request_idx: 0,
            },
            ModuleRecordDef::LocalExport {
                local_name: loc_name,
                export_name: exp_name,
            },
            ModuleRecordDef::StarExport {
                module_request_idx: 1,
            },
        ],
    )
    .expect("module data");
    let f_mod = b.class_add_field(
        mod_cls,
        MODULE_RECORD_IDX_FIELD,
        Type::U32,
        AccessFlags::STATIC,
    );
    b.field_set_value_literalarray(f_mod, mod_la)
        .expect("moduleRecordIdx");

    let phase_la = b.add_literal_array("mod_phase");
    b.literal_array_add_module_request_phase(phase_la, &[0, 1])
        .expect("moduleRequestPhaseIdx");
    let f_phase = b.class_add_field(
        mod_cls,
        MODULE_REQUEST_PHASE_FIELD,
        Type::U32,
        AccessFlags::STATIC,
    );
    b.field_set_value_literalarray(f_phase, phase_la)
        .expect("phase field");

    // Helper method on LDerived;.
    let helper_insns = [Bytecode::Ldai(Imm(123)), Bytecode::Return];
    let (helper_bytes, _) = abcd_isa::encode(&helper_insns).expect("encode helper");
    let helper_m = b.class_add_method(
        derived_cls,
        "compute",
        empty_proto,
        AccessFlags::PUBLIC,
        &helper_bytes,
        1,
        1,
    );
    b.method_set_source_lang(helper_m, SourceLang::EcmaScript);
    b.method_set_function_kind(helper_m, FunctionKind::Function);

    // Main method on L_GLOBAL; with entity relocations, try/catch blocks, and full LNP debug info.
    let placeholder = EntityId(0);
    let main_insns = [
        insn::LdaStr::new(placeholder),
        insn::Definefunc::new(Imm(0), placeholder, Imm(0)),
        insn::Createarraywithbuffer::new(Imm(0), placeholder),
        Bytecode::Sta(Reg(0)),
        Bytecode::Lda(Reg(0)),
        Bytecode::Return,
        Bytecode::Returnundefined,
    ];
    let (main_bytes, main_offs) = abcd_isa::encode(&main_insns).expect("encode main");
    let main_code = b.create_code(&main_bytes, 2, 3);
    // Try covers instructions [0..4), typed catch at instruction 5, catch-all at instruction 6.
    b.code_add_try_block(
        main_code,
        main_offs[0],
        main_offs[4] - main_offs[0],
        &[
            CatchBlockDef {
                type_class: Some(derived_cls),
                handler_pc: main_offs[5],
                code_size: main_offs[6] - main_offs[5],
            },
            CatchBlockDef {
                type_class: None,
                handler_pc: main_offs[6],
                code_size: main_bytes.len() as u32 - main_offs[6],
            },
        ],
    );

    let main_m = b.class_add_method(
        global_cls,
        "func_main_0",
        empty_proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &[],
        2,
        3,
    );
    b.method_set_code(main_m, main_code);
    b.method_set_source_lang(main_m, SourceLang::EcmaScript);
    b.method_set_function_kind(main_m, FunctionKind::Function);

    b.relocate_code_id(main_m, main_offs[0], 0, CodeEntity::String(lone_surrogate))
        .expect("reloc string");
    b.relocate_code_id(main_m, main_offs[1], 0, CodeEntity::Method(helper_m))
        .expect("reloc method");
    b.relocate_code_id(main_m, main_offs[2], 0, CodeEntity::LiteralArray(parent_la))
        .expect("reloc literal array");

    if include_foreign_call_operand {
        // Also add a method referencing the foreign method so foreign index fallback is exercised.
        let caller_insns = [
            insn::Definefunc::new(Imm(0), placeholder, Imm(0)),
            Bytecode::Returnundefined,
        ];
        let (caller_bytes, caller_offs) = abcd_isa::encode(&caller_insns).expect("encode caller");
        let foreign_caller_m = b.class_add_method(
            global_cls,
            "call_ext",
            empty_proto,
            AccessFlags::PUBLIC | AccessFlags::STATIC,
            &caller_bytes,
            1,
            0,
        );
        b.method_set_source_lang(foreign_caller_m, SourceLang::EcmaScript);
        b.relocate_code_id(
            foreign_caller_m,
            caller_offs[0],
            0,
            CodeEntity::Method(foreign_fn),
        )
        .expect("reloc foreign method");
    } else {
        let _ = foreign_fn;
    }

    // Full LNP debug info on `func_main_0`.
    let lnp = b.create_lnp();
    let dbg = b.create_debug_info(lnp, 10);
    let p0_name = b.add_string("funcObj");
    let p1_name = b.add_string("newTarget");
    let p2_name = b.add_string("thisVal");
    b.debug_add_param(dbg, p0_name);
    b.debug_add_param(dbg, p1_name);
    b.debug_add_param(dbg, p2_name);
    let sf_main = b.add_string("index.ets");
    let sc_main = b.add_string("export function main() { return 123; }");
    let var_name = b.add_string("tmpArr");
    let var_type = b.add_string("any");
    let var_sig = b.add_string("Lstd/core/Object;");
    b.lnp_emit_set_file(lnp, dbg, sf_main);
    b.lnp_emit_set_source_code(lnp, dbg, sc_main);
    b.lnp_emit_column(lnp, dbg, 0, 4);
    b.lnp_emit_start_local_extended(lnp, dbg, 0, var_name, var_type, var_sig);
    b.lnp_emit_special_opcode(lnp, dbg, main_offs[3], 5);
    b.lnp_emit_column(lnp, dbg, 0, 12);
    b.lnp_emit_advance_pc(lnp, dbg, main_offs[5] - main_offs[3]);
    b.lnp_emit_end_local(lnp, 0);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(main_m, dbg);

    // Rich annotations (nested scalar Annotation, ArrayAnnotation, MethodHandle, I64, F64, LiteralArray).
    let ann_cls = b.add_foreign_class("LMyAnno;");
    let k_nested = b.add_string("nested");
    let k_arr_ann = b.add_string("annArr");
    let k_mh = b.add_string("mh");
    let k_i64 = b.add_string("big");
    let k_f64 = b.add_string("flt");
    let k_la = b.add_string("lit");
    let k_leaf = b.add_string("leafVal");

    let leaf_ann = b.create_annotation_ex(
        ann_cls,
        &[AnnotationElemDefEx {
            name: k_leaf,
            tag: b'7', // U32
            value: AnnotationElemValue::Scalar(999),
        }],
    );
    let mh_item = b.create_method_handle(4, helper_m.as_raw()); // InvokeStatic = 4
    let outer_ann = b.create_annotation_ex(
        ann_cls,
        &[
            AnnotationElemDefEx {
                name: k_nested,
                tag: b'G', // Annotation
                value: AnnotationElemValue::EntityRef(leaf_ann.as_raw()),
            },
            AnnotationElemDefEx {
                name: k_arr_ann,
                tag: b'Z', // ArrayAnnotation
                value: AnnotationElemValue::EntityArray(vec![leaf_ann.as_raw()]),
            },
            AnnotationElemDefEx {
                name: k_mh,
                tag: b'J', // MethodHandle
                value: AnnotationElemValue::EntityRef(mh_item.as_raw()),
            },
            AnnotationElemDefEx {
                name: k_i64,
                tag: b'8', // I64
                value: AnnotationElemValue::Scalar64((-123_456_789_012i64) as u64),
            },
            AnnotationElemDefEx {
                name: k_f64,
                tag: b'B', // F64
                value: AnnotationElemValue::Scalar64(2.75f64.to_bits()),
            },
            AnnotationElemDefEx {
                name: k_la,
                tag: b'#', // LiteralArray
                value: AnnotationElemValue::EntityRef(child_la.as_raw()),
            },
        ],
    );
    b.class_add_annotation(derived_cls, outer_ann);

    b.finalize().expect("finalize rich API-12 fixture")
}

/// Build an API-9 `.abc` fixture with a typed `ProtoItem` (reference + primitives),
/// dual-bucket `ParamAnnotations`, and all 4 wire class annotation retention tags
/// (`RUNTIME_ANNOTATION = 2`, `ANNOTATION = 3`, `RUNTIME_TYPE_ANNOTATION = 5`,
/// `TYPE_ANNOTATION = 6`).
fn build_api9_proto_and_4bucket_fixture() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(9, "");
    let ref_cls = b.add_class("LArgRef;");
    b.class_set_source_lang(ref_cls, SourceLang::EcmaScript);
    let ret_cls = b.add_class("LRetRef;");
    b.class_set_source_lang(ret_cls, SourceLang::EcmaScript);

    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);

    let proto = b.create_proto_ex(
        &Type::Reference(StringId::new(0)),
        Some(ret_cls),
        &[Type::I32, Type::Reference(StringId::new(0)), Type::F64],
        &[None, Some(ref_cls), None],
    );
    let m = b.class_add_method(
        cls,
        "typed_entry",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &[0x65],
        4,
        3,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let p0 = b.method_add_param(m, Type::I32);
    let p1 = b.method_add_param_ex(m, Type::Reference(StringId::new(0)), Some(ref_cls));
    let _p2 = b.method_add_param(m, Type::F64);

    let k_val = b.add_string("v");
    let ann_p0 = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name: k_val,
            tag: b'7',
            value: AnnotationElemValue::Scalar(101),
        }],
    );
    b.method_param_add_annotation(m, p0, ann_p0);
    b.method_seal_param_annotations(m, false)
        .expect("seal compile-time param anns");

    let ann_p1 = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name: k_val,
            tag: b'7',
            value: AnnotationElemValue::Scalar(202),
        }],
    );
    b.method_param_add_runtime_annotation(m, p1, ann_p1);
    b.method_seal_param_annotations(m, true)
        .expect("seal runtime param anns");

    // Attach 4 distinct annotations to `cls`, then patch their ClassTag bytes
    // to exercise all 4 wire retention buckets (`2`, `3`, `5`, `6`).
    for tag_val in [1001u32, 1002, 1003, 1004] {
        let ann = b.create_annotation_ex(
            cls,
            &[AnnotationElemDefEx {
                name: k_val,
                tag: b'7',
                value: AnnotationElemValue::Scalar(tag_val),
            }],
        );
        b.class_add_annotation(cls, ann);
    }

    let mut bytes = b.finalize().expect("finalize API-9 fixture");

    // Locate L_GLOBAL;'s 4 consecutive `[0x03 (ClassTag::ANNOTATION)][u32 off]`
    // tagged values via C++ `abc_class_enumerate_annotations` and rewrite tags
    // to `[2 (RUNTIME), 3 (ANNOTATION), 5 (RUNTIME_TYPE), 6 (TYPE)]` + recompute checksum!
    let mut ann_offs: Vec<u32> = Vec::new();
    unsafe extern "C" fn collect_ann_off(off: u32, ctx: *mut std::ffi::c_void) -> std::ffi::c_int {
        // SAFETY: `ctx` points to `ann_offs` on our stack for this synchronous callback.
        unsafe { (&mut *(ctx as *mut Vec<u32>)).push(off) };
        0
    }
    // SAFETY: `bytes` is a valid finalized `.abc` slice; handles are closed before mutation.
    unsafe {
        let f = sys::abc_file_open(bytes.as_ptr(), bytes.len());
        assert!(!f.is_null());
        let cls_off = sys::abc_file_get_class_id(f, c"L_GLOBAL;".as_ptr().cast());
        assert_ne!(cls_off, u32::MAX);
        let ca = sys::abc_class_open(f, cls_off);
        assert!(!ca.is_null());
        assert_eq!(
            sys::abc_class_enumerate_annotations(
                ca,
                Some(collect_ann_off),
                (&mut ann_offs as *mut Vec<u32>).cast(),
            ),
            0
        );
        sys::abc_class_close(ca);
        sys::abc_file_close(f);
    }
    assert_eq!(ann_offs.len(), 4);
    let desired_tags = [3u8, 4u8, 5u8, 6u8];
    for (&off, &new_tag) in ann_offs.iter().zip(desired_tags.iter()) {
        let mut needle = [0u8; 5];
        needle[0] = 4; // ClassTag::ANNOTATION
        needle[1..5].copy_from_slice(&off.to_le_bytes());
        let hits: Vec<usize> = bytes
            .windows(5)
            .enumerate()
            .filter_map(|(i, w)| (w == needle).then_some(i))
            .collect();
        assert_eq!(hits.len(), 1, "unique ClassTag::ANNOTATION entry for {off}");
        bytes[hits[0]] = new_tag;
    }
    let csum = adler32_abc(&bytes[12..]);
    bytes[8..12].copy_from_slice(&csum.to_le_bytes());
    bytes
}

#[test]
fn differential_oracle_matches_cpp_libpandafile_accessors() {
    // --- Part A: Rich API-12 container ---
    let data = build_rich_api12_fixture(true);
    assert!(validate_checksum(&data));
    assert_eq!(file_type(&data), FileType::Dynamic);

    let rust_eager = decode(&data).expect("pure-Rust decode");
    let rust_lazy = decode_lazy(Arc::from(data.as_slice())).expect("pure-Rust decode_lazy");
    let summary = inspect_summary(&data, true).expect("pure-Rust inspect_summary");

    // SAFETY: `data` outlives `cpp_file` and all C++ child accessors opened below.
    unsafe {
        let cpp_typ = sys::abc_file_get_type(data.as_ptr(), data.len() as i32);
        assert_eq!(FileType::try_from(cpp_typ).unwrap(), file_type(&data));

        let cpp_file = sys::abc_file_open(data.as_ptr(), data.len());
        assert!(!cpp_file.is_null(), "C++ abc_file_open must succeed");
        assert_eq!(sys::abc_file_validate_checksum(cpp_file), 1);
        assert_eq!(sys::abc_file_checksum(cpp_file), rust_eager.checksum);
        assert_eq!(sys::abc_file_size(cpp_file), rust_eager.size);

        let mut raw_ver = [0u8; 4];
        sys::abc_file_version(cpp_file, raw_ver.as_mut_ptr());
        assert_eq!(Version::from(raw_ver), rust_eager.version);

        let cpp_num_classes = sys::abc_file_num_classes(cpp_file);
        assert_eq!(cpp_num_classes as usize, rust_eager.classes.len());
        assert_eq!(cpp_num_classes as usize, rust_lazy.classes.len());
        assert_eq!(cpp_num_classes as usize, summary.classes);

        // Compare every class header, flags, super_class, interfaces, methods, and fields!
        for idx in 0..cpp_num_classes {
            let cls_off = sys::abc_file_class_offset(cpp_file, idx);
            let is_ext = sys::abc_file_is_external(cpp_file, cls_off) != 0;
            if is_ext {
                let mut len_buf = [0u8; 128];
                let n = sys::abc_file_get_string(
                    cpp_file,
                    cls_off,
                    len_buf.as_mut_ptr().cast(),
                    len_buf.len(),
                );
                let desc = std::str::from_utf8(&len_buf[..n]).expect("ascii foreign desc");
                let r_cls = rust_eager
                    .class_by_str(desc)
                    .expect("foreign class in Rust");
                assert!(r_cls.is_external);
                continue;
            }

            let ca = sys::abc_class_open(cpp_file, cls_off);
            assert!(!ca.is_null());
            let desc_ptr = sys::abc_class_get_descriptor(ca);
            let desc_cstr = CStr::from_ptr(desc_ptr.cast());
            let desc_str = desc_cstr.to_str().expect("class descriptor utf8");
            let r_cls = rust_eager
                .class_by_str(desc_str)
                .unwrap_or_else(|| panic!("missing class {desc_str}"));
            assert!(!r_cls.is_external);
            assert_eq!(r_cls.access_flags.bits(), sys::abc_class_access_flags(ca));
            assert_eq!(
                sys::abc_class_get_ifaces_number(ca) as usize,
                r_cls.interfaces.len()
            );

            let mut cpp_method_offs: Vec<u32> = Vec::new();
            unsafe extern "C" fn push_u32(off: u32, ctx: *mut std::ffi::c_void) {
                // SAFETY: `ctx` points to `Vec<u32>` for this synchronous call.
                unsafe { (&mut *(ctx as *mut Vec<u32>)).push(off) };
            }
            assert_eq!(
                sys::abc_class_enumerate_methods(
                    ca,
                    Some(push_u32),
                    (&mut cpp_method_offs as *mut Vec<u32>).cast(),
                ),
                0
            );
            assert_eq!(cpp_method_offs.len(), r_cls.methods.len());
            for (&m_off, r_m) in cpp_method_offs.iter().zip(r_cls.methods.iter()) {
                assert_eq!(r_m.offset, m_off);
                let ma = sys::abc_method_open(cpp_file, m_off);
                assert!(!ma.is_null());
                assert_eq!(r_m.access_flags.bits(), sys::abc_method_access_flags(ma));
                let code_off = sys::abc_method_code_off(ma);
                if code_off != u32::MAX {
                    let body = r_m.body.as_ref().expect("Rust method body");
                    let code_acc = sys::abc_code_open(cpp_file, code_off);
                    assert!(!code_acc.is_null());
                    assert_eq!(body.num_vregs, sys::abc_code_num_vregs(code_acc));
                    assert_eq!(body.num_args, sys::abc_code_num_args(code_acc));
                    assert_eq!(
                        body.try_blocks.len(),
                        sys::abc_code_tries_size(code_acc) as usize
                    );
                    sys::abc_code_close(code_acc);
                }
                sys::abc_method_close(ma);
            }

            let mut cpp_field_offs: Vec<u32> = Vec::new();
            assert_eq!(
                sys::abc_class_enumerate_fields(
                    ca,
                    Some(push_u32),
                    (&mut cpp_field_offs as *mut Vec<u32>).cast(),
                ),
                0
            );
            assert_eq!(cpp_field_offs.len(), r_cls.fields.len());
            for (&f_off, r_f) in cpp_field_offs.iter().zip(r_cls.fields.iter()) {
                assert_eq!(r_f.offset, f_off);
                let fa = sys::abc_field_open(cpp_file, f_off);
                assert!(!fa.is_null());
                assert_eq!(r_f.access_flags.bits(), sys::abc_field_access_flags(fa));
                match r_f.initial_value {
                    Some(FieldValue::I32(v)) => {
                        let mut out = 0i32;
                        assert_eq!(sys::abc_field_get_value_i32(fa, &mut out), 1);
                        assert_eq!(out, v);
                    }
                    Some(FieldValue::I64(v)) => {
                        let mut out = 0i64;
                        assert_eq!(sys::abc_field_get_value_i64(fa, &mut out), 1);
                        assert_eq!(out, v);
                    }
                    Some(FieldValue::F32(v)) => {
                        let mut out = 0f32;
                        assert_eq!(sys::abc_field_get_value_f32(fa, &mut out), 1);
                        assert_eq!(out.to_bits(), v.to_bits());
                    }
                    Some(FieldValue::F64(v)) => {
                        let mut out = 0f64;
                        assert_eq!(sys::abc_field_get_value_f64(fa, &mut out), 1);
                        assert_eq!(out.to_bits(), v.to_bits());
                    }
                    _ => {}
                }
                sys::abc_field_close(fa);
            }
            sys::abc_class_close(ca);
        }

        // Compare C++ DebugInfoExtractor on `func_main_0` against pure-Rust `MethodDebugInfo`.
        let g_cls = rust_eager.class_by_str("L_GLOBAL;").unwrap();
        let r_main = g_cls
            .methods
            .iter()
            .find(|m| rust_eager.strings.resolve(m.name) == Some("func_main_0"))
            .unwrap();
        let r_dbg = r_main.debug.as_ref().expect("Rust MethodDebugInfo");
        let cpp_dbg = sys::abc_debug_info_open(cpp_file);
        assert!(!cpp_dbg.is_null());
        let cpp_sf = CStr::from_ptr(sys::abc_debug_get_source_file(cpp_dbg, r_main.offset))
            .to_str()
            .unwrap();
        let cpp_sc = CStr::from_ptr(sys::abc_debug_get_source_code(cpp_dbg, r_main.offset))
            .to_str()
            .unwrap();
        assert_eq!(
            r_dbg
                .source_file
                .and_then(|s| rust_eager.strings.resolve(s)),
            Some(cpp_sf)
        );
        assert_eq!(
            r_dbg
                .source_code
                .and_then(|s| rust_eager.strings.resolve(s)),
            Some(cpp_sc)
        );

        let mut cpp_lines: Vec<(u32, u32)> = Vec::new();
        unsafe extern "C" fn push_line(
            entry: *const sys::AbcLineEntry,
            ctx: *mut std::ffi::c_void,
        ) -> std::ffi::c_int {
            // SAFETY: `entry` and `ctx` are valid for this synchronous callback.
            unsafe {
                let e = &*entry;
                (&mut *(ctx as *mut Vec<(u32, u32)>)).push((e.offset, e.line));
            }
            0
        }
        sys::abc_debug_get_line_table(
            cpp_dbg,
            r_main.offset,
            Some(push_line),
            (&mut cpp_lines as *mut Vec<(u32, u32)>).cast(),
        );
        assert_eq!(cpp_lines.len(), r_dbg.line_table.len());
        for ((_, cpp_line), r_row) in cpp_lines.iter().zip(r_dbg.line_table.iter()) {
            assert_eq!(r_row.line, *cpp_line);
        }

        let mut cpp_cols: Vec<(u32, u32)> = Vec::new();
        unsafe extern "C" fn push_col(
            entry: *const sys::AbcColumnEntry,
            ctx: *mut std::ffi::c_void,
        ) -> std::ffi::c_int {
            // SAFETY: `entry` and `ctx` are valid for this synchronous callback.
            unsafe {
                let e = &*entry;
                (&mut *(ctx as *mut Vec<(u32, u32)>)).push((e.offset, e.column));
            }
            0
        }
        sys::abc_debug_get_column_table(
            cpp_dbg,
            r_main.offset,
            Some(push_col),
            (&mut cpp_cols as *mut Vec<(u32, u32)>).cast(),
        );
        assert_eq!(cpp_cols.len(), r_dbg.column_table.len());
        for ((_, cpp_col), r_row) in cpp_cols.iter().zip(r_dbg.column_table.iter()) {
            assert_eq!(r_row.column, *cpp_col);
        }

        sys::abc_debug_info_close(cpp_dbg);
        sys::abc_file_close(cpp_file);
    }

    // Verify semantic contents decoded by pure Rust on the rich API-12 fixture:
    // - Lone-surrogate string preserved losslessly (`lossy_count == 1`).
    assert_eq!(rust_eager.strings.lossy_count(), 1);
    assert_eq!(summary.lossy_strings, 1);
    let mod_cls = rust_eager
        .class_by_str(ES_MODULE_RECORD_DESCRIPTOR)
        .expect("module record class");
    let mod_fld = mod_cls
        .fields
        .iter()
        .find(|f| rust_eager.strings.resolve(f.name) == Some(MODULE_RECORD_IDX_FIELD))
        .unwrap();
    let Some(FieldValue::ModuleData(mod_data)) = &mod_fld.initial_value else {
        panic!("expected FieldValue::ModuleData");
    };
    assert_eq!(mod_data.requests.len(), 2);
    assert!(matches!(
        mod_data.records.as_slice(),
        [
            ModuleRecord::RegularImport { .. },
            ModuleRecord::LocalExport { .. },
            ModuleRecord::StarExport {
                module_request_idx: 1
            },
        ]
    ));
    let phase_fld = mod_cls
        .fields
        .iter()
        .find(|f| rust_eager.strings.resolve(f.name) == Some(MODULE_REQUEST_PHASE_FIELD))
        .unwrap();
    assert!(matches!(
        &phase_fld.initial_value,
        Some(FieldValue::ModuleRequestPhase(p)) if p.flags == [0, 1]
    ));

    // --- Part B: API-9 typed Proto + ParamAnnotations + all 4 wire annotation buckets ---
    let api9 = build_api9_proto_and_4bucket_fixture();
    let f9 = decode(&api9).expect("pure-Rust decode API-9");
    let g9 = f9.class_by_str("L_GLOBAL;").expect("L_GLOBAL;");

    // Verify all 4 wire retention buckets matched C++ enumeration!
    assert_eq!(g9.annotations.runtime.len(), 1);
    assert_eq!(g9.annotations.compile_time.len(), 1);
    assert_eq!(g9.annotations.runtime_type.len(), 1);
    assert_eq!(g9.annotations.compile_time_type.len(), 1);
    assert_eq!(
        g9.annotations.runtime[0].elements[0].value,
        AnnotationValue::U32(1001)
    );
    assert_eq!(
        g9.annotations.compile_time[0].elements[0].value,
        AnnotationValue::U32(1002)
    );
    assert_eq!(
        g9.annotations.runtime_type[0].elements[0].value,
        AnnotationValue::U32(1003)
    );
    assert_eq!(
        g9.annotations.compile_time_type[0].elements[0].value,
        AnnotationValue::U32(1004)
    );

    let m9 = &g9.methods[0];
    assert!(matches!(
        m9.return_type,
        Some(Type::Reference(sid)) if f9.strings.resolve(sid) == Some("LRetRef;")
    ));
    assert_eq!(m9.arg_types.len(), 3);
    assert_eq!(m9.arg_types[0], Type::I32);
    assert!(matches!(
        m9.arg_types[1],
        Type::Reference(sid) if f9.strings.resolve(sid) == Some("LArgRef;")
    ));
    assert_eq!(m9.arg_types[2], Type::F64);
    assert_eq!(m9.param_annotations.compile_time[0].len(), 1);
    assert_eq!(m9.param_annotations.runtime[1].len(), 1);

    // Verify C++ proto & 4-bucket enumerators agree on `api9`!
    // SAFETY: `api9` outlives `cpp_f9` and its child accessors.
    unsafe {
        let cpp_f9 = sys::abc_file_open(api9.as_ptr(), api9.len());
        assert!(!cpp_f9.is_null());
        let cls_off = sys::abc_file_get_class_id(cpp_f9, c"L_GLOBAL;".as_ptr().cast());
        let ca = sys::abc_class_open(cpp_f9, cls_off);
        assert!(!ca.is_null());

        unsafe extern "C" fn count_ann(_off: u32, ctx: *mut std::ffi::c_void) -> std::ffi::c_int {
            // SAFETY: `ctx` points to a stack `usize`.
            unsafe { *(ctx as *mut usize) += 1 };
            0
        }
        let (mut c_ct, mut c_rt, mut c_ty, mut c_rty) = (0usize, 0usize, 0usize, 0usize);
        sys::abc_class_enumerate_annotations(ca, Some(count_ann), (&mut c_ct as *mut usize).cast());
        sys::abc_class_enumerate_runtime_annotations(
            ca,
            Some(count_ann),
            (&mut c_rt as *mut usize).cast(),
        );
        sys::abc_class_enumerate_type_annotations(
            ca,
            Some(count_ann),
            (&mut c_ty as *mut usize).cast(),
        );
        sys::abc_class_enumerate_runtime_type_annotations(
            ca,
            Some(count_ann),
            (&mut c_rty as *mut usize).cast(),
        );
        assert_eq!((c_ct, c_rt, c_ty, c_rty), (1, 1, 1, 1));

        let ma = sys::abc_method_open(cpp_f9, m9.offset);
        assert_eq!(sys::abc_method_has_valid_proto(ma), 1);
        let pa = sys::abc_proto_open(cpp_f9, sys::abc_method_get_proto_id(ma));
        assert_eq!(sys::abc_proto_num_args(pa), 3);
        assert_eq!(sys::abc_proto_get_ref_num(pa), 2);
        sys::abc_proto_close(pa);
        sys::abc_method_close(ma);
        sys::abc_class_close(ca);
        sys::abc_file_close(cpp_f9);
    }
}

// ===========================================================================
// 2. Lazy (`decode_lazy`) vs. Eager (`decode` / `decode_arc`) Bit-Identity
// ===========================================================================

#[test]
fn lazy_and_eager_decode_produce_bit_identical_pandasm_and_encode() {
    let modern_12_ext = build_rich_api12_fixture(true);
    let modern_12 = build_rich_api12_fixture(false);

    // Also verify `pandasm::emit_file` lazy vs. eager parity on external-method operands too.
    assert_eq!(
        pandasm::emit_file(&decode(&modern_12_ext).unwrap(), "ext.abc"),
        pandasm::emit_file(
            &decode_lazy(Arc::from(modern_12_ext.as_slice())).unwrap(),
            "ext.abc"
        )
    );

    // Also build a 24.0.0.0 container (no header literal-array table: `u32::MAX` sentinel).
    let mut b24 = Builder::new();
    b24.set_file_version(Version::new(24, 0, 0, 0))
        .expect("set 24.0.0.0");
    let g24 = b24.add_global_class();
    b24.class_set_source_lang(g24, SourceLang::EcmaScript);
    let p24 = b24.create_proto(Type::Tagged, &[]);
    let la24 = b24.add_literal_array("v24_lit");
    b24.literal_array_add_integer(la24, 2026);
    let s24 = b24.add_string("hello_v24");
    let (code24, offs24) = abcd_isa::encode(&[
        insn::LdaStr::new(EntityId(0)),
        insn::Createarraywithbuffer::new(Imm(0), EntityId(0)),
        Bytecode::Return,
    ])
    .unwrap();
    let m24 = b24.class_add_method(
        g24,
        "func_main_0",
        p24,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &code24,
        1,
        0,
    );
    b24.method_set_source_lang(m24, SourceLang::EcmaScript);
    b24.relocate_code_id(m24, offs24[0], 0, CodeEntity::String(s24))
        .unwrap();
    b24.relocate_code_id(m24, offs24[1], 0, CodeEntity::LiteralArray(la24))
        .unwrap();
    let modern_24 = b24.finalize().expect("finalize 24.0.0.0");

    for (label, bytes) in [("12.x", &modern_12), ("24.x", &modern_24)] {
        let arc_bytes: Arc<[u8]> = Arc::from(bytes.as_slice());
        let eager = decode(bytes).expect("eager decode");
        let eager_arc = decode_arc(Arc::clone(&arc_bytes)).expect("decode_arc");
        let lazy = decode_lazy(Arc::clone(&arc_bytes)).expect("decode_lazy");

        let assert_pools_eq = |lhs: &StringPool, rhs: &StringPool, msg: &str| {
            assert_eq!(lhs.len(), rhs.len(), "{msg}: len");
            assert_eq!(lhs.lossy_count(), rhs.lossy_count(), "{msg}: lossy_count");
            for (i, ((lid, ls), (rid, rs))) in lhs.iter().zip(rhs.iter()).enumerate() {
                assert_eq!(lid, rid, "{msg}: StringId at {i}");
                assert_eq!(ls, rs, "{msg}: UTF-8 text at {i}");
                assert_eq!(
                    lhs.to_mutf8_bytes(lid),
                    rhs.to_mutf8_bytes(rid),
                    "{msg}: MUTF-8 bytes at {i}"
                );
            }
        };
        assert_pools_eq(
            &eager.strings,
            &eager_arc.strings,
            &format!("{label}: decode_arc pool"),
        );
        assert_pools_eq(
            &eager.strings,
            &lazy.strings,
            &format!("{label}: lazy StringPool"),
        );
        assert_eq!(
            eager.literal_arrays, lazy.literal_arrays,
            "{label}: lazy literal_arrays must match eager"
        );

        for ((_, em), (_, lm)) in eager.all_methods().zip(lazy.all_methods()) {
            match (&em.body, &lm.body) {
                (Some(eb), Some(lb)) => {
                    assert!(matches!(eb.code, MethodCode::Decoded(_)));
                    assert!(matches!(lb.code, MethodCode::Span(_)));
                    assert!(matches!(eb.code.decode_cow(), Cow::Borrowed(_)));
                    assert!(matches!(lb.code.decode_cow(), Cow::Owned(_)));
                    assert_eq!(eb.insn_count(), lb.insn_count());
                    assert_eq!(eb.code.len(), lb.code.len());
                    assert_eq!(eb.code.is_empty(), lb.code.is_empty());
                    assert_eq!(eb.bytecodes().as_ref(), lb.bytecodes().as_ref());
                    assert_eq!(eb.entities, lb.entities);
                    assert_eq!(eb.try_blocks, lb.try_blocks);
                    assert_eq!(lb.code.clone().into_vec(), eb.bytecodes().as_ref());
                }
                (None, None) => {}
                _ => panic!("{label}: body presence mismatch"),
            }
        }

        let pa_eager = pandasm::emit_file(&eager, "test.abc");
        let pa_lazy = pandasm::emit_file(&lazy, "test.abc");
        assert_eq!(
            pa_eager, pa_lazy,
            "{label}: pandasm::emit_file must be 100% byte-identical on decode_lazy"
        );

        let enc_eager = encode(&eager).expect("encode eager");
        let enc_lazy = encode(&lazy).expect("encode lazy");
        assert_eq!(
            enc_eager, enc_lazy,
            "{label}: encode(&lazy) must be 100% byte-identical to encode(&eager)"
        );
    }

    // Legacy 0.0.0.2 container lazy vs. eager parity.
    let mut legacy = {
        let mut bl = Builder::new();
        bl.set_api(12, "beta1");
        let cls = bl.add_global_class();
        bl.class_set_source_lang(cls, SourceLang::EcmaScript);
        let pr = bl.create_proto(Type::Tagged, &[]);
        // 6 bytes padded so we can overwrite with legacy `ldai.dyn 42; return.dyn` (`[0xa4, 42, 0, 0, 0, 0xa6]`).
        let m = bl.class_add_method(
            cls,
            "legacy_fn",
            pr,
            AccessFlags::PUBLIC,
            &[0x62, 0x2a, 0x00, 0x00, 0x00, 0x64],
            1,
            0,
        );
        bl.method_set_source_lang(m, SourceLang::EcmaScript);
        bl.finalize().unwrap()
    };
    let modern_pat = [0x62u8, 0x2a, 0x00, 0x00, 0x00, 0x64];
    let code_pos = legacy
        .windows(modern_pat.len())
        .position(|w| w == modern_pat)
        .expect("locate code");
    legacy[code_pos..code_pos + 6].copy_from_slice(&[0xa4, 0x2a, 0x00, 0x00, 0x00, 0xa6]);
    legacy[12..16].copy_from_slice(&[0, 0, 0, 2]);
    let legacy_csum = adler32_abc(&legacy[12..]);
    legacy[8..12].copy_from_slice(&legacy_csum.to_le_bytes());

    let leg_eager = decode(&legacy).expect("legacy eager");
    let leg_lazy = decode_lazy(Arc::from(legacy.as_slice())).expect("legacy lazy");
    let leg_body = leg_lazy
        .all_methods()
        .next()
        .unwrap()
        .1
        .body
        .as_ref()
        .unwrap();
    assert!(matches!(leg_body.code, MethodCode::Span(ref s) if s.legacy));
    assert_eq!(
        pandasm::emit_file(&leg_eager, "leg.abc"),
        pandasm::emit_file(&leg_lazy, "leg.abc")
    );
}

#[test]
fn method_entities_sorted_map_operations_are_deterministic() {
    let mut sp = StringPool::new();
    let s0 = sp.get_or_intern("alpha");
    let s1 = sp.get_or_intern("beta");

    let mut hm = HashMap::new();
    hm.insert((EntityKind::LiteralarrayId, 3), EntityRef::string(s1));
    hm.insert((EntityKind::StringId, 10), EntityRef::string(s0));
    hm.insert((EntityKind::MethodId, 1), EntityRef::string(s1));

    let mut me = MethodEntities::from(hm);
    assert_eq!(me.len(), 3);
    assert!(!me.is_empty());
    assert!(me.contains_key(&(EntityKind::StringId, 10)));
    assert_eq!(me[&(EntityKind::StringId, 10)], EntityRef::string(s0));

    // Keys must be strictly ordered by `(kind as u8, raw_id)` regardless of HashMap hash order!
    let keys: Vec<(EntityKind, u32)> = me.keys().copied().collect();
    assert_eq!(
        keys,
        vec![
            (EntityKind::LiteralarrayId, 3),
            (EntityKind::MethodId, 1),
            (EntityKind::StringId, 10),
        ]
    );

    // Replace + get_mut + remove + iter/IntoIterator + clear.
    let prev = me.insert((EntityKind::StringId, 10), EntityRef::string(s1));
    assert_eq!(prev, Some(EntityRef::string(s0)));
    if let Some(v) = me.get_mut(&(EntityKind::MethodId, 1)) {
        *v = EntityRef::string(s0);
    }
    assert_eq!(
        me.remove(&(EntityKind::LiteralarrayId, 3)),
        Some(EntityRef::string(s1))
    );
    assert_eq!(me.len(), 2);
    assert_eq!(me.values().count(), 2);
    assert_eq!(me.values_mut().count(), 2);

    let rebuilt: MethodEntities = me.clone().into_iter().collect();
    assert_eq!(rebuilt, me);
    me.clear();
    assert!(me.is_empty());
}

// ===========================================================================
// 3. `DecodeMode::Forensic` Recovery & 256 KiB Iterative Stack Gate
// ===========================================================================

#[test]
fn forensic_mode_recovers_healthy_methods_and_records_diagnostics() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);

    // 1. Healthy method with string + literal array.
    let ok_str = b.add_string("recovered_ok_payload");
    let ok_la = b.add_literal_array("recovered_lit");
    b.literal_array_add_integer(ok_la, 0xCAFE);
    let (healthy_code, healthy_offs) = abcd_isa::encode(&[
        insn::LdaStr::new(EntityId(0)),
        insn::Createarraywithbuffer::new(Imm(0), EntityId(0)),
        Bytecode::Return,
    ])
    .unwrap();
    let m_healthy = b.class_add_method(
        cls,
        "healthy_fn",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &healthy_code,
        1,
        0,
    );
    b.method_set_source_lang(m_healthy, SourceLang::EcmaScript);
    b.relocate_code_id(m_healthy, healthy_offs[0], 0, CodeEntity::String(ok_str))
        .unwrap();
    b.relocate_code_id(
        m_healthy,
        healthy_offs[1],
        0,
        CodeEntity::LiteralArray(ok_la),
    )
    .unwrap();

    // 2. Decoy method with distinctive bytecode marker `[0x62, 0x78, 0x56, 0x34, 0x12, 0x64]`
    //    and its own LNP debug program.
    let decoy_marker = [0x62u8, 0x78, 0x56, 0x34, 0x12, 0x64];
    let m_decoy = b.class_add_method(
        cls,
        "decoy_corrupt_fn",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &decoy_marker,
        1,
        0,
    );
    b.method_set_source_lang(m_decoy, SourceLang::EcmaScript);
    let lnp = b.create_lnp();
    let dbg = b.create_debug_info(lnp, 20);
    let decoy_sf = b.add_string("decoy_source.ts");
    b.lnp_emit_set_file(lnp, dbg, decoy_sf);
    b.lnp_emit_advance_line(lnp, dbg, 4);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m_decoy, dbg);

    let mut corrupted = b.finalize().expect("finalize 2-method container");
    assert!(validate_checksum(&corrupted));

    // Locate `decoy_corrupt_fn`'s debug_info_off and LNP offset before corruption.
    let lnp_off = {
        // SAFETY: `corrupted` is a valid finalized buffer during this query.
        unsafe {
            let f = sys::abc_file_open(corrupted.as_ptr(), corrupted.len());
            assert!(!f.is_null());
            let c_off = sys::abc_file_get_class_id(f, c"L_GLOBAL;".as_ptr().cast());
            let ca = sys::abc_class_open(f, c_off);
            let mut m_offs = Vec::new();
            unsafe extern "C" fn push_m(off: u32, ctx: *mut std::ffi::c_void) {
                // SAFETY: `ctx` points to `m_offs`.
                unsafe { (&mut *(ctx as *mut Vec<u32>)).push(off) };
            }
            sys::abc_class_enumerate_methods(
                ca,
                Some(push_m),
                (&mut m_offs as *mut Vec<u32>).cast(),
            );
            let mut found_dbg = u32::MAX;
            for mo in m_offs {
                let ma = sys::abc_method_open(f, mo);
                let d_off = sys::abc_method_debug_info_off(ma);
                if d_off != u32::MAX {
                    found_dbg = d_off;
                }
                sys::abc_method_close(ma);
            }
            sys::abc_class_close(ca);
            sys::abc_file_close(f);
            assert_ne!(found_dbg, u32::MAX);
            // `DebugInfoItem` starts with `[ULEB line_start][ULEB num_params]...[ULEB const_pool_size][bytes][ULEB lnp_idx]`.
            // Header's `lnp_idx_off` (`+40..44`) has 1 entry (`num_lnps == 1`) pointing directly to the LNP item!
            let num_lnps = u32::from_le_bytes(corrupted[36..40].try_into().unwrap());
            assert_eq!(num_lnps, 1);
            let lnp_idx_off = u32::from_le_bytes(corrupted[40..44].try_into().unwrap()) as usize;
            u32::from_le_bytes(corrupted[lnp_idx_off..lnp_idx_off + 4].try_into().unwrap()) as usize
        }
    };

    // Injection 1: Corrupt LNP program opcode to `DW_LNS_SET_FILE (0x04)` when constant pool is exhausted!
    corrupted[lnp_off] = 0x04;
    corrupted[lnp_off + 1] = 0x04;

    // Injection 2: Corrupt `decoy_corrupt_fn`'s bytecode stream with a truncated `0xfe` throw prefix at end!
    let code_pos = corrupted
        .windows(decoy_marker.len())
        .position(|w| w == decoy_marker)
        .expect("locate decoy_marker");
    corrupted[code_pos..code_pos + 6].copy_from_slice(&[0x65, 0x65, 0x65, 0x65, 0x65, 0xfe]);

    // Injection 3: Corrupt header Adler-32 checksum (`8..12`).
    corrupted[8] ^= 0xFF;
    assert!(!validate_checksum(&corrupted));

    // Strict mode MUST reject loudly on both eager and lazy decode!
    assert!(decode(&corrupted).is_err());
    assert!(decode_lazy(Arc::from(corrupted.as_slice())).is_err());

    // Forensic mode MUST succeed on both eager and lazy decode, recovering `healthy_fn`
    // and reporting structured diagnostics for checksum, bytecode, and debug_info!
    for lazy_code in [false, true] {
        let opts = DecodeOptions {
            mode: DecodeMode::Forensic,
            lazy_code,
        };
        let (recovered, diags) =
            decode_with_options(Arc::from(corrupted.as_slice()), &opts).expect("forensic decode");

        let kinds: Vec<&str> = diags.iter().map(|d| d.kind).collect();
        assert!(
            kinds.contains(&"checksum"),
            "expected checksum diagnostic, got: {diags:?}"
        );
        assert!(
            kinds.contains(&"bytecode"),
            "expected bytecode diagnostic, got: {diags:?}"
        );
        assert!(
            kinds.contains(&"debug_info"),
            "expected debug_info diagnostic, got: {diags:?}"
        );
        assert_eq!(
            diags.iter().find(|d| d.kind == "checksum").unwrap().offset,
            Some(8)
        );

        // `healthy_fn` must be 100% intact!
        let m_ok = recovered
            .all_methods()
            .find(|(_, m)| recovered.strings.resolve(m.name) == Some("healthy_fn"))
            .expect("healthy_fn must survive forensic decode")
            .1;
        let ok_body = m_ok.body.as_ref().expect("healthy_fn body");
        assert_eq!(ok_body.insn_count(), 3);
        let (_, str_op) = ok_body.bytecodes()[0].entity_operands()[0];
        let EntityRef::String { id: sid, .. } = ok_body.entities[&(EntityKind::StringId, str_op.0)]
        else {
            panic!("expected string entity on healthy_fn");
        };
        assert_eq!(recovered.strings.resolve(sid), Some("recovered_ok_payload"));
    }
}

#[test]
fn deep_nested_annotations_and_literal_arrays_pass_on_256kib_stack() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let ann_cls = b.add_foreign_class("LDeepAnn;");
    let k_next = b.add_string("next");

    // Iterative chain of 400 nested scalar `Annotation` items + 400 nested `LiteralArray` items.
    let mut cur_ann = b.create_annotation_ex(
        ann_cls,
        &[AnnotationElemDefEx {
            name: k_next,
            tag: b'7',
            value: AnnotationElemValue::Scalar(0),
        }],
    );
    for _ in 0..400 {
        cur_ann = b.create_annotation_ex(
            ann_cls,
            &[AnnotationElemDefEx {
                name: k_next,
                tag: b'G',
                value: AnnotationElemValue::EntityRef(cur_ann.as_raw()),
            }],
        );
    }
    b.class_add_annotation(cls, cur_ann);

    let mut cur_la = b.add_literal_array("la_0");
    b.literal_array_add_integer(cur_la, 1);
    for depth in 1..=400 {
        let parent = b.add_literal_array(&format!("la_{depth}"));
        b.literal_array_add_literalarray(parent, cur_la);
        cur_la = parent;
    }

    let proto = b.create_proto(Type::Tagged, &[]);
    let (code, offs) = abcd_isa::encode(&[
        insn::Createarraywithbuffer::new(Imm(0), EntityId(0)),
        Bytecode::Return,
    ])
    .unwrap();
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &code,
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.relocate_code_id(m, offs[0], 0, CodeEntity::LiteralArray(cur_la))
        .unwrap();
    let bytes = b.finalize().expect("finalize deep container");

    let handle = std::thread::Builder::new()
        .name("issue49-256k".to_owned())
        .stack_size(256 * 1024)
        .spawn(move || {
            let summary = inspect_summary(&bytes, true).expect("256 KiB summary");
            assert_eq!(summary.literal_arrays, 401);
            let file = decode(&bytes).expect("256 KiB decode");
            assert_eq!(file.literal_arrays.len(), 401);
            drop(file);
        })
        .expect("spawn 256 KiB thread");
    handle.join().expect("256 KiB thread must not overflow");
}

// ===========================================================================
// 4. Static Header Layouts (`0.0.0.5` 64B, `0.0.0.6` 72B, `0.1.0.7` 72B) & `0.0.0.3`
// ===========================================================================

/// Synthesize a valid container with arbitrary header layout (`60`, `64`, or `72` bytes),
/// 1 foreign class `"LExt;"`, 1 valid 40-byte `IndexHeader`, and optional `ETSGLOBAL`
/// export-table bytes (`72`-byte static headers).
fn synth_container_header(
    version: [u8; 4],
    header_size: usize,
    ets_raw_field: u32,
    ets_payload_bytes: usize,
) -> Vec<u8> {
    let mut buf = vec![0u8; header_size];
    buf[0..8].copy_from_slice(b"PANDA\0\0\0");
    buf[12..16].copy_from_slice(&version);

    // Class index table (`num_classes = 1`) sits immediately after the header
    // (`offset == header_size`) so item offsets satisfy `EntityId::IsValid()` (`> header_size`).
    let class_idx_off = buf.len() as u32;
    buf.extend_from_slice(&0u32.to_le_bytes()); // backfilled below

    // Foreign region: 1 foreign class string `"LExt;"`: ULEB((5 << 1) | 1 = 11) + b"LExt;\0" (7 bytes), padded to 4B align.
    let foreign_off = buf.len() as u32;
    let ext_cls_off = foreign_off;
    buf[class_idx_off as usize..class_idx_off as usize + 4]
        .copy_from_slice(&ext_cls_off.to_le_bytes());
    buf.push((5u8 << 1) | 1);
    buf.extend_from_slice(b"LExt;\0");
    while !buf.len().is_multiple_of(4) {
        buf.push(0);
    }
    let foreign_size = (buf.len() as u32) - foreign_off;

    // Optional ETSGLOBAL table (`72`-byte static headers).
    let ets_off = if ets_payload_bytes > 0 {
        let off = buf.len() as u32;
        buf.resize(buf.len() + ets_payload_bytes, 0);
        off
    } else {
        0
    };

    // Index section (`num_indexes = 1`, 40-byte `IndexHeader` + 1 `class_idx` entry).
    let index_section_off = buf.len() as u32;
    let ih_class_off = index_section_off + 40;
    buf.extend_from_slice(&0u32.to_le_bytes()); // start
    buf.extend_from_slice(&u32::MAX.to_le_bytes()); // end
    buf.extend_from_slice(&1u32.to_le_bytes()); // class_idx_size
    buf.extend_from_slice(&ih_class_off.to_le_bytes()); // class_idx_off
    for _ in 0..6 {
        buf.extend_from_slice(&u32::MAX.to_le_bytes()); // method/field/proto sizes=0? Wait: sizes must be 0!
    }
    // Fix sizes/offs in IndexHeader: `[method_size=0, method_off=MAX, field_size=0, field_off=MAX, proto_size=0, proto_off=MAX]`.
    let ih_base = index_section_off as usize;
    for pair in 0..3usize {
        let base = ih_base + 16 + pair * 8;
        buf[base..base + 4].copy_from_slice(&0u32.to_le_bytes());
        buf[base + 4..base + 8].copy_from_slice(&u32::MAX.to_le_bytes());
    }
    buf.extend_from_slice(&ext_cls_off.to_le_bytes());

    let file_size = buf.len() as u32;
    buf[16..20].copy_from_slice(&file_size.to_le_bytes());
    buf[20..24].copy_from_slice(&foreign_off.to_le_bytes());
    buf[24..28].copy_from_slice(&foreign_size.to_le_bytes());

    match header_size {
        60 => {
            buf[28..32].copy_from_slice(&1u32.to_le_bytes()); // num_classes
            buf[32..36].copy_from_slice(&class_idx_off.to_le_bytes());
            buf[36..40].copy_from_slice(&0u32.to_le_bytes()); // num_lnps
            buf[40..44].copy_from_slice(&0u32.to_le_bytes());
            buf[44..48].copy_from_slice(&0u32.to_le_bytes()); // num_literalarrays
            buf[48..52].copy_from_slice(&0u32.to_le_bytes());
            buf[52..56].copy_from_slice(&1u32.to_le_bytes()); // num_indexes
            buf[56..60].copy_from_slice(&index_section_off.to_le_bytes());
        }
        64 => {
            buf[28..32].copy_from_slice(&0u32.to_le_bytes()); // +0x1c static v5 slot
            buf[32..36].copy_from_slice(&1u32.to_le_bytes()); // num_classes
            buf[36..40].copy_from_slice(&class_idx_off.to_le_bytes());
            buf[40..44].copy_from_slice(&0u32.to_le_bytes()); // num_lnps
            buf[44..48].copy_from_slice(&0u32.to_le_bytes());
            buf[48..52].copy_from_slice(&u32::MAX.to_le_bytes()); // num_literalarrays sentinel
            buf[52..56].copy_from_slice(&u32::MAX.to_le_bytes());
            buf[56..60].copy_from_slice(&1u32.to_le_bytes()); // num_indexes
            buf[60..64].copy_from_slice(&index_section_off.to_le_bytes());
        }
        72 => {
            buf[28..32].copy_from_slice(&0u32.to_le_bytes()); // +0x1c slot
            buf[32..36].copy_from_slice(&1u32.to_le_bytes()); // num_classes
            buf[36..40].copy_from_slice(&class_idx_off.to_le_bytes());
            buf[40..44].copy_from_slice(&ets_raw_field.to_le_bytes()); // +0x28 ETSGLOBAL count or byte len
            buf[44..48].copy_from_slice(&ets_off.to_le_bytes()); // +0x2c ETSGLOBAL off
            buf[48..52].copy_from_slice(&0u32.to_le_bytes()); // num_lnps
            buf[52..56].copy_from_slice(&0u32.to_le_bytes());
            buf[56..60].copy_from_slice(&u32::MAX.to_le_bytes()); // num_literalarrays
            buf[60..64].copy_from_slice(&u32::MAX.to_le_bytes());
            buf[64..68].copy_from_slice(&1u32.to_le_bytes()); // num_indexes
            buf[68..72].copy_from_slice(&index_section_off.to_le_bytes());
        }
        _ => unreachable!(),
    }

    let csum = adler32_abc(&buf[12..]);
    buf[8..12].copy_from_slice(&csum.to_le_bytes());
    buf
}

#[test]
fn static_headers_v0005_v0006_v0107_and_dynamic_v0003_classify_accurately() {
    // 1. Dynamic `0.0.0.3` (60B header) — dynamic modern, NOT static!
    let dyn_v3 = synth_container_header([0, 0, 0, 3], 60, 0, 0);
    assert_eq!(file_type(&dyn_v3), FileType::Dynamic);
    assert!(validate_checksum(&dyn_v3));
    let sum_v3 = inspect_summary(&dyn_v3, false).expect("0.0.0.3 summary");
    assert_eq!(sum_v3.dialect(), Some(Dialect::DynamicModern));
    assert_eq!(sum_v3.classes, 1);
    assert_eq!(sum_v3.external_classes, 1);
    let dec_v3 = decode(&dyn_v3).expect("0.0.0.3 decode");
    assert_eq!(dec_v3.dialect(), Some(Dialect::DynamicModern));
    assert_eq!(dec_v3.classes.len(), 1);

    // 2. Static `0.0.0.5` (HarmonyOS 6.0, 64B header).
    let st_v5 = synth_container_header([0, 0, 0, 5], 64, 0, 0);
    assert_eq!(file_type(&st_v5), FileType::Static);
    assert!(validate_checksum(&st_v5));
    let sum_v5 = inspect_summary(&st_v5, false).expect("0.0.0.5 summary");
    assert_eq!(sum_v5.file_type, FileType::Static);
    assert_eq!(sum_v5.dialect(), Some(Dialect::Static));
    assert_eq!(sum_v5.classes, 1);
    assert_eq!(sum_v5.external_classes, 1);
    assert!(matches!(
        decode(&st_v5),
        Err(Error::Malformed {
            field: "file_type",
            ..
        })
    ));
    assert!(matches!(
        inspect_summary(&st_v5, true),
        Err(Error::Malformed {
            field: "file_type",
            ..
        })
    ));

    // 3. Static `0.0.0.6` (HarmonyOS 6.1, 72B header, `+0x28` = entry count `2` -> `8` bytes).
    let st_v6 = synth_container_header([0, 0, 0, 6], 72, 2, 8);
    assert_eq!(file_type(&st_v6), FileType::Static);
    let sum_v6 = inspect_summary(&st_v6, false).expect("0.0.0.6 summary");
    assert_eq!(sum_v6.dialect(), Some(Dialect::Static));
    assert_eq!(sum_v6.classes, 1);
    // Out-of-bounds `ets_count` on `0.0.0.6` must report Invalid / Err!
    let mut bad_v6 = st_v6.clone();
    bad_v6[40..44].copy_from_slice(&1000u32.to_le_bytes());
    assert_eq!(file_type(&bad_v6), FileType::Invalid);

    // 4. Static `0.1.0.7` (HarmonyOS 7.0, 72B header, `+0x28` = byte length `8`).
    let st_v7 = synth_container_header([0, 1, 0, 7], 72, 8, 8);
    assert_eq!(file_type(&st_v7), FileType::Static);
    let sum_v7 = inspect_summary(&st_v7, false).expect("0.1.0.7 72B summary");
    assert_eq!(sum_v7.dialect(), Some(Dialect::Static));
    assert_eq!(sum_v7.classes, 1);
    // Non-multiple-of-4 `ets_byte_len` on `0.1.0.7` must report Invalid!
    let mut bad_v7 = st_v7;
    bad_v7[40..44].copy_from_slice(&6u32.to_le_bytes());
    assert_eq!(file_type(&bad_v7), FileType::Invalid);
}

// ===========================================================================
// 5. `SummaryStrings` SipHash DoS Resilience (`#77`) & `StringPool` (`#72`)
// ===========================================================================

#[test]
fn summary_strings_siphash_and_string_pool_drop_index_parity() {
    // Build a container with 300 distinct equal-length strings, astral CESU-8,
    // embedded NULs, empty string `""`, UTF-8 `U+FFFD`, and two distinct lone surrogates.
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let la = b.add_literal_array("str_stress");

    let s_empty = b.add_string("");
    let s_fffd = b.add_string("\u{FFFD}");
    let s_nul = b.add_string("a\0b");
    let s_emoji = b.add_string("ark🚀🔥");
    let s_surr0 = b.add_string_mutf8(&[0xED, 0xA0, 0x80]).unwrap();
    let s_surr1 = b.add_string_mutf8(&[0xED, 0xA0, 0x81]).unwrap();
    for h in [s_empty, s_fffd, s_nul, s_emoji, s_surr0, s_surr1] {
        b.literal_array_add_string(la, h);
    }
    for i in 0..300u32 {
        let s = b.add_string(&format!("collision_probe_key_{i:06x}"));
        b.literal_array_add_string(la, s);
        // Add duplicate reference to verify dedup parity in SummaryStrings!
        b.literal_array_add_string(la, s);
    }

    let proto = b.create_proto(Type::Tagged, &[]);
    let (code, offs) = abcd_isa::encode(&[
        insn::Createarraywithbuffer::new(Imm(0), EntityId(0)),
        Bytecode::Return,
    ])
    .unwrap();
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &code,
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.relocate_code_id(m, offs[0], 0, CodeEntity::LiteralArray(la))
        .unwrap();
    let bytes = b.finalize().expect("finalize string stress container");

    let summary = inspect_summary(&bytes, true).expect("inspect_summary");
    let mut file = decode(&bytes).expect("decode");
    assert_eq!(summary.strings, file.strings.len());
    assert_eq!(summary.lossy_strings, file.strings.lossy_count());
    assert_eq!(file.strings.lossy_count(), 2);

    // Exercise `drop_index()` on a live decoded `File` and verify `get`, `get_raw_mutf8`,
    // `lossy_ids()`, `pandasm::emit_file`, and `encode` all remain 100% identical!
    let pa_before = pandasm::emit_file(&file, "stress.abc");
    let enc_before = encode(&file).expect("encode before drop_index");

    assert!(file.strings.has_index());
    let lossy_vec: Vec<_> = file.strings.lossy_ids().collect();
    assert_eq!(lossy_vec.len(), 2);

    file.strings.drop_index();
    assert!(!file.strings.has_index());

    // Read-only lookups after `drop_index()` must succeed via linear length-prefiltered scan
    // without mutating or rebuilding the index!
    assert!(file.strings.get("").is_some());
    assert!(file.strings.get("\u{FFFD}").is_some());
    assert!(file.strings.get("a\0b").is_some());
    assert!(file.strings.get("ark🚀🔥").is_some());
    assert!(file.strings.get("collision_probe_key_00012b").is_some());
    assert_eq!(
        file.strings.get("collision_probe_key_ffffff"),
        None,
        "same-length absent probe must return None"
    );
    assert!(file.strings.get_raw_mutf8(&[0xED, 0xA0, 0x80]).is_some());
    assert!(file.strings.get_raw_mutf8(&[0xED, 0xA0, 0x81]).is_some());
    assert_eq!(file.strings.get_raw_mutf8(&[0xED, 0xA0, 0x82]), None);
    assert!(!file.strings.has_index());

    assert_eq!(pandasm::emit_file(&file, "stress.abc"), pa_before);
    assert_eq!(encode(&file).expect("encode after drop_index"), enc_before);

    // Cloning and mutating after `drop_index()` rebuilds the index on the mutated clone only.
    let frozen_clone = file.strings.clone();
    let new_id = file.strings.try_get_or_intern("rebuilt_entry").unwrap();
    assert!(file.strings.has_index());
    assert!(!frozen_clone.has_index());
    assert_eq!(file.strings.resolve(new_id), Some("rebuilt_entry"));
    assert_eq!(frozen_clone.get("rebuilt_entry"), None);
}
