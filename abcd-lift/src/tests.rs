//! Unit tests for the top-level `abcd-lift` orchestration pipeline:
//! arena capacity shrinking, `O(1)` `StringId → Sym` memoization (including
//! lone surrogates), parallel vs. sequential structural equivalence on `256 KiB`
//! worker stacks, deterministic lowest-method error selection, and `decode_lazy`
//! `MethodSpan` parity.

use std::collections::HashMap;
use std::sync::Arc;

use abcd_file::{
    AccessFlags, Annotation as FileAnnotation, AnnotationElem, AnnotationValue, Builder,
    CatchBlock, CatchBlockDef, ColumnEntry, EntityRef, Field, FieldValue, File, FileType,
    FunctionKind as FileFunctionKind, LineEntry, LiteralArray, LiteralArrayIdx, LiteralValue,
    LocalVarInfo, Method, MethodBody, MethodCode, MethodDebugInfo, MethodEntities, MethodIdx,
    ModuleData, ModuleRecord, ModuleRequestPhase, ParamInfo, SourceLang as FileSourceLang,
    StringPool, TryBlock, Type, Version, decode, decode_lazy,
};
use abcd_ir::modules_structurally_eq;
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Label, Reg, encode as encode_bytecodes};

use super::{
    LiftError, LiftOptions, Lifter, lift_file, lift_file_forced_parallel, lift_file_with_options,
};

#[test]
fn lift_file_shrinks_arena_and_per_function_capacities() {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    for idx in 0..8 {
        let (insns, offsets) = encode_bytecodes(&[
            Bytecode::Lda(Reg(0)),
            Bytecode::Return,
            Bytecode::Sta(Reg(1)),
            Bytecode::Lda(Reg(1)),
            Bytecode::Return,
        ])
        .unwrap();
        let code = b.create_code(&insns, 2, 3);
        b.code_add_try_block(
            code,
            offsets[0],
            offsets[2] - offsets[0],
            &[CatchBlockDef {
                type_class: None,
                handler_pc: offsets[2],
                code_size: insns.len() as u32 - offsets[2],
            }],
        );
        let m = b.class_add_method(
            cls,
            &format!("f{idx}"),
            proto,
            AccessFlags::STATIC,
            &[],
            0,
            0,
        );
        b.method_set_code(m, code);
    }
    let file = decode(&b.finalize().unwrap()).unwrap();
    let m = lift_file(&file).unwrap();
    assert!(abcd_ir::verify_module(&m).errors.is_empty());

    assert_eq!(m.classes.capacity(), m.classes.len());
    assert_eq!(m.functions.capacity(), m.functions.len());
    assert_eq!(m.blocks.capacity(), m.blocks.len());
    assert_eq!(m.insts.capacity(), m.insts.len());
    assert_eq!(m.values.capacity(), m.values.len());
    assert_eq!(m.imports.capacity(), m.imports.len());
    assert_eq!(m.exports.capacity(), m.exports.len());
    assert_eq!(m.module_requests.capacity(), m.module_requests.len());

    for c in &m.classes {
        assert_eq!(c.interfaces.capacity(), c.interfaces.len());
        assert_eq!(c.fields.capacity(), c.fields.len());
        assert_eq!(c.methods.capacity(), c.methods.len());
        assert_eq!(c.annotations.capacity(), c.annotations.len());
        if let Some(es) = &c.es_module {
            assert_eq!(es.imports.capacity(), es.imports.len());
            assert_eq!(es.exports.capacity(), es.exports.len());
            assert_eq!(es.module_requests.capacity(), es.module_requests.len());
        }
    }
    for f in &m.functions {
        assert_eq!(f.params.capacity(), f.params.len());
        assert_eq!(f.frame_init_consts.capacity(), f.frame_init_consts.len());
        assert_eq!(f.blocks.capacity(), f.blocks.len());
        assert_eq!(f.try_regions.capacity(), f.try_regions.len());
        assert_eq!(f.annotations.capacity(), f.annotations.len());
        for r in &f.try_regions {
            assert_eq!(r.protected.capacity(), r.protected.len());
            assert_eq!(r.catches.capacity(), r.catches.len());
        }
        if let Some(dbg) = &f.debug {
            assert_eq!(dbg.line_table.capacity(), dbg.line_table.len());
            assert_eq!(dbg.column_table.capacity(), dbg.column_table.len());
            assert_eq!(dbg.local_names.capacity(), dbg.local_names.len());
            assert_eq!(dbg.param_names.capacity(), dbg.param_names.len());
        }
    }
    for blk in &m.blocks {
        assert_eq!(blk.insts.capacity(), blk.insts.len());
        assert_eq!(blk.preds.capacity(), blk.preds.len());
    }
}

#[test]
fn sid_to_sym_memo_preserves_lone_surrogates_and_rejects_dangling_ids() {
    let mut strings = StringPool::new();
    let utf8_sid = strings.get_or_intern("alpha");
    let fffd_sid = strings.get_or_intern("\u{FFFD}\u{FFFD}\u{FFFD}");
    let hi_sid = strings.intern_mutf8(&[0xED, 0xA0, 0xB4]);
    let lo_sid = strings.intern_mutf8(&[0xED, 0xBC, 0x86]);

    let mut other = StringPool::new();
    for i in 0..8 {
        other.get_or_intern(format!("pad_{i}"));
    }
    let dangling = other.get_or_intern("dangling");

    let file = File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: Default::default(),
        literal_arrays: Vec::new(),
        literal_array_header_offsets: Vec::new(),
    };
    let mut lf = Lifter::new(&file);
    assert_eq!(lf.sid_to_sym, vec![u32::MAX; 4]);

    let s_hi = lf.sym_of_file_sid(hi_sid).unwrap();
    let s_fffd = lf.sym_of_file_sid(fffd_sid).unwrap();
    let s_lo = lf.sym_of_file_sid(lo_sid).unwrap();
    let s_utf8 = lf.sym_of_file_sid(utf8_sid).unwrap();
    assert_eq!(lf.sym_of_file_sid(dangling), None);

    // Cached O(1) hits return identical symbols even after dropping SymbolTable index.
    lf.module.sym.drop_index();
    assert_eq!(lf.sym_of_file_sid(hi_sid), Some(s_hi));
    assert_eq!(lf.sym_of_file_sid(fffd_sid), Some(s_fffd));
    assert_eq!(lf.sym_of_file_sid(lo_sid), Some(s_lo));
    assert_eq!(lf.sym_of_file_sid(utf8_sid), Some(s_utf8));
    assert!(
        !lf.module.sym.has_index(),
        "O(1) sid_to_sym hit must not touch SymbolTable"
    );

    assert_ne!(s_hi, s_fffd);
    assert_ne!(s_hi, s_lo);
    assert_eq!(lf.module.sym.raw_mutf8(s_hi), Some(&[0xED, 0xA0, 0xB4][..]));
    assert_eq!(lf.module.sym.raw_mutf8(s_lo), Some(&[0xED, 0xBC, 0x86][..]));
    assert_eq!(
        lf.module.sym.as_str(s_fffd),
        Some("\u{FFFD}\u{FFFD}\u{FFFD}")
    );
}

/// Build a rich multi-class synthetic `File` exercising every global-table
/// side effect across method boundaries:
/// - Shared & nested literal arrays (`PlainArray` and `BufferRef`, shared
///   between methods in different classes)
/// - Foreign catch `type_class` descriptors & foreign annotations (including
///   foreign `L_ESCallTypeAnnotation;` shifting `this` to `params[1]`)
/// - Annotation `LiteralArray` with a failing element (`Const::Null` degrade)
/// - Lone-surrogate MUTF-8 strings + colliding lossless `U+FFFD` strings
/// - `--merge-abc` `EsModule` + `scopeNames` AND legacy `0.0.0.2` module-var
///   opcodes (both matched slots and fallback `Sym.0` patches)
/// - Shared `Arc<str>` debug `source_code`, local var foreign `Type::Reference`,
///   and a body-less `is_external` native declaration.
fn build_rich_parallel_fixture() -> File {
    let mut s = StringPool::new();
    let cls_a_desc = s.get_or_intern("Lpkg/Alpha;");
    let cls_b_desc = s.get_or_intern("Lpkg/Beta;");
    let cls_c_desc = s.get_or_intern("Lpkg/NativeDecl;");

    let mod_field = s.get_or_intern(abcd_file::MODULE_RECORD_IDX_FIELD);
    let phase_field = s.get_or_intern(abcd_file::MODULE_REQUEST_PHASE_FIELD);
    let scope_field = s.get_or_intern(abcd_file::SCOPE_NAMES_FIELD);

    let req_dep = s.get_or_intern("./dep");
    let imp_local = s.get_or_intern("impVal");
    let exp_local = s.get_or_intern("expVal");
    let scope_str = s.get_or_intern("lexScope0");

    // Strings intentionally NOT referenced in Pass 1 / Pass 2a so Pass 2b
    // interns them for the first time across different worker threads!
    let foreign_exc_1 = s.get_or_intern("Lforeign/CustomError;");
    let foreign_exc_2 = s.get_or_intern("Lforeign/IoError;");
    let foreign_call_ann = s.get_or_intern("L_ESCallTypeAnnotation;");
    let call_type_key = s.get_or_intern("callType");
    let foreign_tag_ann = s.get_or_intern("Lforeign/TagAnn;");
    let tag_elem_key = s.get_or_intern("payload");
    let foreign_local_ty = s.get_or_intern("Lforeign/LocalWidget;");
    let lone_hi = s.intern_mutf8(&[0xED, 0xA0, 0x81]);
    let lone_lo = s.intern_mutf8(&[0xED, 0xBF, 0xBF]);
    let fffd_str = s.get_or_intern("\u{FFFD}\u{FFFD}\u{FFFD}");
    let lit_str_0 = s.get_or_intern("shared_lit_zero");
    let lit_str_1 = s.get_or_intern("nested_lit_one");
    let unmapped_modvar = s.get_or_intern("unmapped_legacy_mod_sym");
    let src_file_a = s.get_or_intern("alpha.ts");
    let src_file_b = s.get_or_intern("beta.ts");
    let shared_src_code = s.get_or_intern("export function run(x) { return x + 1; }\n");
    let param_x = s.get_or_intern("x");
    let local_tmp = s.get_or_intern("tmpWidget");

    let m_a0_name = s.get_or_intern("a0_first_lit_and_catch");
    let m_a1_name = s.get_or_intern("a1_calltype_this_and_lone");
    let m_a2_name = s.get_or_intern("a2_esm_slots");
    let m_b0_name = s.get_or_intern("b0_reuses_shared_lit_and_catch");
    let m_b1_name = s.get_or_intern("b1_legacy_modvar_fallback_and_homeobj");
    let m_c0_name = s.get_or_intern("c0_external_native");

    let mut other_pool = StringPool::new();
    for i in 0..64 {
        other_pool.get_or_intern(format!("pad_{i}"));
    }
    let ghost_sid = other_pool.get_or_intern("ghost");

    // Literal arrays:
    // [0] scopeNames for Alpha (resolved in Pass 2a)
    // [1] nested child array `[lit_str_1, lone_lo]`
    // [2] shared parent array `[lit_str_0, LiteralArray(1), LiteralBufferIndex(1), Method(0)]`
    let lit_arrays = vec![
        LiteralArray::new(vec![LiteralValue::String(scope_str)]),
        LiteralArray::new(vec![
            LiteralValue::String(lit_str_1),
            LiteralValue::String(lone_lo),
        ]),
        LiteralArray::new(vec![
            LiteralValue::String(lit_str_0),
            LiteralValue::LiteralArray(LiteralArrayIdx(1)),
            LiteralValue::LiteralBufferIndex(LiteralArrayIdx(1)),
            LiteralValue::Method(MethodIdx(0)),
        ]),
    ];

    // Method A0: references shared literal array 2, foreign catch `foreign_exc_1`,
    // shared debug `source_code`, and foreign local var type `foreign_local_ty`.
    let m_a0 = Method {
        name: m_a0_name,
        offset: 0x100,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::Function,
        source_lang: FileSourceLang::TypeScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 2,
            num_args: 3,
            code: MethodCode::Decoded(vec![
                Bytecode::Createarraywithbuffer(Imm(0), EntityId(0)), // 0 (try)
                Bytecode::Sta(Reg(0)),                                // 1
                Bytecode::Lda(Reg(0)),                                // 2
                Bytecode::Return,                                     // 3
                Bytecode::Sta(Reg(1)),                                // 4 (catch)
                Bytecode::Lda(Reg(1)),                                // 5
                Bytecode::Return,                                     // 6
            ]),
            entities: HashMap::from([(
                (EntityKind::LiteralarrayId, 0),
                EntityRef::LiteralArray(LiteralArrayIdx(2)),
            )])
            .into(),
            try_blocks: vec![TryBlock {
                start: 0,
                len: 4,
                catches: vec![CatchBlock {
                    type_class: Some(foreign_exc_1),
                    handler: 4,
                    len: 3,
                }],
            }],
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: Some(MethodDebugInfo {
            source_file: Some(src_file_a),
            source_code: Some(shared_src_code),
            line_table: vec![LineEntry { index: 0, line: 10 }],
            column_table: vec![ColumnEntry {
                index: 0,
                column: 4,
            }],
            local_vars: vec![LocalVarInfo {
                name: local_tmp,
                type_name: foreign_local_ty,
                type_signature: foreign_local_ty,
                reg_number: 0,
                start: 0,
                end: 3,
            }],
            params: vec![ParamInfo {
                name: param_x,
                signature: foreign_local_ty,
            }],
        }),
    };

    // Method A1: carries foreign `L_ESCallTypeAnnotation;` (`callType = 0b1001` ->
    // `this` at `params[1]`), foreign `TagAnn` with partial-failing `LiteralArray`,
    // lone-surrogate `LdaStr`, and `Ldthis`.
    let m_a1 = Method {
        name: m_a1_name,
        offset: 0x200,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::Function,
        source_lang: FileSourceLang::TypeScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 2,
            num_args: 2,
            code: MethodCode::Decoded(vec![
                Bytecode::Ldthis,               // 0 -> params[1] via callType 0b1001
                Bytecode::Sta(Reg(0)),          // 1
                Bytecode::LdaStr(EntityId(0)),  // 2 -> lone_hi
                Bytecode::Sta(Reg(1)),          // 3
                Bytecode::LdaStr(EntityId(1)),  // 4 -> fffd_str
                Bytecode::Add2(Imm(0), Reg(0)), // 5
                Bytecode::Add2(Imm(1), Reg(1)), // 6
                Bytecode::Return,               // 7
            ]),
            entities: HashMap::from([
                ((EntityKind::StringId, 0), EntityRef::string(lone_hi)),
                ((EntityKind::StringId, 1), EntityRef::string(fffd_str)),
            ])
            .into(),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: abcd_file::Annotations {
            compile_time: vec![
                FileAnnotation {
                    class_descriptor: foreign_call_ann,
                    elements: vec![AnnotationElem {
                        name: call_type_key,
                        value: AnnotationValue::U32(0b1001),
                    }],
                },
                FileAnnotation {
                    class_descriptor: foreign_tag_ann,
                    elements: vec![AnnotationElem {
                        name: tag_elem_key,
                        value: AnnotationValue::LiteralArray(vec![
                            LiteralValue::LiteralArray(LiteralArrayIdx(1)),
                            LiteralValue::String(ghost_sid), // degrades to Const::Null
                        ]),
                    }],
                },
            ],
            ..Default::default()
        },
        param_annotations: Default::default(),
        debug: Some(MethodDebugInfo {
            source_file: Some(src_file_a),
            source_code: Some(shared_src_code),
            line_table: vec![LineEntry { index: 0, line: 20 }],
            column_table: Vec::new(),
            local_vars: Vec::new(),
            params: Vec::new(),
        }),
    };

    // Method A2: resolves legacy `0.0.0.2` module-var strings against Alpha's `--merge-abc` EsModule.
    let m_a2 = Method {
        name: m_a2_name,
        offset: 0x300,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::Function,
        source_lang: FileSourceLang::TypeScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 1,
            num_args: 3,
            code: MethodCode::Decoded(vec![
                Bytecode::DeprecatedLdmodulevar(EntityId(0), Imm(0)),
                Bytecode::DeprecatedStmodulevar(EntityId(1)),
                Bytecode::DeprecatedGetmodulenamespace(EntityId(2)),
                Bytecode::Return,
            ]),
            entities: HashMap::from([
                ((EntityKind::StringId, 0), EntityRef::string(imp_local)),
                ((EntityKind::StringId, 1), EntityRef::string(exp_local)),
                ((EntityKind::StringId, 2), EntityRef::string(req_dep)),
            ])
            .into(),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };

    // Method B0 (in Beta, which has NO EsModule!): reuses shared literal array 2,
    // reuses `foreign_exc_1`, introduces `foreign_exc_2`, and shares `shared_src_code`.
    let m_b0 = Method {
        name: m_b0_name,
        offset: 0x400,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::Function,
        source_lang: FileSourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 2,
            num_args: 3,
            code: MethodCode::Decoded(vec![
                Bytecode::Createarraywithbuffer(Imm(0), EntityId(0)), // 0 (try)
                Bytecode::Jnez(Label(3)),                             // 1
                Bytecode::Createemptyobject,                          // 2
                Bytecode::Return,                                     // 3
                Bytecode::Return,                                     // 4 (catch 1)
                Bytecode::Returnundefined,                            // 5 (catch 2)
            ]),
            entities: HashMap::from([(
                (EntityKind::LiteralarrayId, 0),
                EntityRef::LiteralArray(LiteralArrayIdx(2)),
            )])
            .into(),
            try_blocks: vec![TryBlock {
                start: 0,
                len: 3,
                catches: vec![
                    CatchBlock {
                        type_class: Some(foreign_exc_1),
                        handler: 4,
                        len: 1,
                    },
                    CatchBlock {
                        type_class: Some(foreign_exc_2),
                        handler: 5,
                        len: 1,
                    },
                ],
            }],
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: Some(MethodDebugInfo {
            source_file: Some(src_file_b),
            source_code: Some(shared_src_code),
            line_table: vec![LineEntry { index: 0, line: 5 }],
            column_table: Vec::new(),
            local_vars: Vec::new(),
            params: Vec::new(),
        }),
    };

    // Method B1 (in Beta, NO EsModule): exercises `DeprecatedLdmodulevar` /
    // `DeprecatedStmodulevar` / `DeprecatedGetmodulenamespace` fallback onto a
    // newly interned method-local symbol (`legacy_modvar_patches`) + `DeprecatedLdhomeobject`!
    let m_b1 = Method {
        name: m_b1_name,
        offset: 0x500,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::Function,
        source_lang: FileSourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 1,
            num_args: 3,
            code: MethodCode::Decoded(vec![
                Bytecode::DeprecatedLdhomeobject,
                Bytecode::Sta(Reg(0)),
                Bytecode::DeprecatedLdmodulevar(EntityId(0), Imm(0)),
                Bytecode::DeprecatedStmodulevar(EntityId(0)),
                Bytecode::DeprecatedGetmodulenamespace(EntityId(0)),
                Bytecode::Add2(Imm(0), Reg(0)),
                Bytecode::Return,
            ]),
            entities: HashMap::from([(
                (EntityKind::StringId, 0),
                EntityRef::string(unmapped_modvar),
            )])
            .into(),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };

    // Method C0: body-less external declaration with foreign Reference param type.
    let m_c0 = Method {
        name: m_c0_name,
        offset: 0x600,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::None,
        source_lang: FileSourceLang::ArkTs,
        is_external: true,
        return_type: Some(Type::I32),
        arg_types: vec![Type::Reference(foreign_local_ty), Type::F64],
        body: None,
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };

    let cls_a = abcd_file::Class {
        descriptor: cls_a_desc,
        name: cls_a_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::TypeScript,
        source_file: Some(src_file_a),
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: vec![m_a0, m_a1, m_a2],
        fields: vec![
            Field {
                name: mod_field,
                offset: 0,
                field_type: Type::U32,
                access_flags: AccessFlags::STATIC,
                is_external: false,
                initial_value: Some(FieldValue::ModuleData(ModuleData {
                    source_offset: 0,
                    requests: vec![req_dep],
                    records: vec![
                        ModuleRecord::RegularImport {
                            local_name: imp_local,
                            import_name: imp_local,
                            module_request_idx: 0,
                        },
                        ModuleRecord::LocalExport {
                            local_name: exp_local,
                            export_name: exp_local,
                        },
                    ],
                })),
                annotations: Default::default(),
            },
            Field {
                name: phase_field,
                offset: 4,
                field_type: Type::U32,
                access_flags: AccessFlags::STATIC,
                is_external: false,
                initial_value: Some(FieldValue::ModuleRequestPhase(ModuleRequestPhase {
                    source_offset: 0,
                    flags: vec![1],
                })),
                annotations: Default::default(),
            },
            Field {
                name: scope_field,
                offset: 8,
                field_type: Type::U32,
                access_flags: AccessFlags::STATIC,
                is_external: false,
                initial_value: Some(FieldValue::literal_array_ref(LiteralArrayIdx(0))),
                annotations: Default::default(),
            },
        ],
        annotations: Default::default(),
    };

    let cls_b = abcd_file::Class {
        descriptor: cls_b_desc,
        name: cls_b_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: Some(src_file_b),
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: vec![m_b0, m_b1],
        fields: Vec::new(),
        annotations: Default::default(),
    };

    let cls_c = abcd_file::Class {
        descriptor: cls_c_desc,
        name: cls_c_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::ArkTs,
        source_file: None,
        is_external: true,
        super_class: None,
        interfaces: Vec::new(),
        methods: vec![m_c0],
        fields: Vec::new(),
        annotations: Default::default(),
    };

    File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings: s,
        classes: [
            (cls_a_desc, cls_a),
            (cls_b_desc, cls_b),
            (cls_c_desc, cls_c),
        ]
        .into_iter()
        .collect(),
        literal_arrays: lit_arrays,
        literal_array_header_offsets: Vec::new(),
    }
}

#[test]
fn forced_parallel_lifting_matches_sequential_across_thread_counts_on_256k_stacks() {
    let file = build_rich_parallel_fixture();
    let seq = lift_file_with_options(
        &file,
        &LiftOptions {
            retain_tail_capacity: false,
            parallel: false,
        },
    )
    .expect("sequential lift succeeds");
    assert!(abcd_ir::verify_module(&seq).errors.is_empty());

    for threads in [1usize, 2, 4] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .stack_size(256 * 1024)
            .build()
            .unwrap();
        let par = pool
            .install(|| lift_file_forced_parallel(&file, false))
            .expect("forced-parallel lift succeeds");
        assert!(abcd_ir::verify_module(&par).errors.is_empty());
        assert_eq!(
            modules_structurally_eq(&seq, &par),
            Ok(()),
            "parallel lift with {threads} Rayon threads diverged from sequential"
        );

        // Verify shared `Arc<str>` source_code deduplication survives Pass 2c merge!
        let sc_a0 = par.functions[0]
            .debug
            .as_ref()
            .and_then(|d| d.source_code.as_ref())
            .expect("a0 source_code");
        let sc_a1 = par.functions[1]
            .debug
            .as_ref()
            .and_then(|d| d.source_code.as_ref())
            .expect("a1 source_code");
        let sc_b0 = par.functions[3]
            .debug
            .as_ref()
            .and_then(|d| d.source_code.as_ref())
            .expect("b0 source_code");
        assert!(Arc::ptr_eq(sc_a0, sc_a1));
        assert!(Arc::ptr_eq(sc_a0, sc_b0));
    }
}

#[test]
fn forced_parallel_lifting_returns_lowest_method_error_deterministically() {
    let mut file = build_rich_parallel_fixture();
    // Inject distinct errors into methods 1 (`InvalidRegister`), 3 (`LiteralArrayOutOfRange`),
    // and 4 (`EmptyBytecode`) — both sequential and parallel MUST return Method 1's error!
    let classes: Vec<_> = file.classes.keys().copied().collect();
    let cls_a = file.classes.get_mut(&classes[0]).unwrap();
    cls_a.methods[1].body = Some(MethodBody {
        num_vregs: 1,
        num_args: 1,
        code: MethodCode::Decoded(vec![Bytecode::Lda(Reg(9)), Bytecode::Return]),
        entities: MethodEntities::new(),
        try_blocks: Vec::new(),
        ic_size: None,
    });
    let cls_b = file.classes.get_mut(&classes[1]).unwrap();
    cls_b.methods[0].body = Some(MethodBody {
        num_vregs: 0,
        num_args: 0,
        code: MethodCode::Decoded(vec![
            Bytecode::DeprecatedCreatearraywithbuffer(Imm(99)),
            Bytecode::Return,
        ]),
        entities: MethodEntities::new(),
        try_blocks: Vec::new(),
        ic_size: None,
    });
    cls_b.methods[1].body = Some(MethodBody {
        num_vregs: 0,
        num_args: 0,
        code: MethodCode::Decoded(Vec::new()),
        entities: MethodEntities::new(),
        try_blocks: Vec::new(),
        ic_size: None,
    });

    let seq_err = lift_file_with_options(
        &file,
        &LiftOptions {
            retain_tail_capacity: false,
            parallel: false,
        },
    )
    .expect_err("sequential must fail on method 1");
    assert!(matches!(
        seq_err,
        LiftError::InvalidRegister {
            reg: 9,
            frame_limit: 2
        }
    ));

    for threads in [1usize, 2, 4] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .stack_size(256 * 1024)
            .build()
            .unwrap();
        let par_err = pool
            .install(|| lift_file_forced_parallel(&file, false))
            .expect_err("parallel must fail on lowest failing method");
        assert!(
            matches!(
                par_err,
                LiftError::InvalidRegister {
                    reg: 9,
                    frame_limit: 2
                }
            ),
            "threads={threads}: expected lowest-method InvalidRegister, got {par_err:?}"
        );
    }
}

#[test]
fn decode_lazy_method_spans_lift_identically_to_eager_decode() {
    let mut b = Builder::new();
    b.set_api(12, "");
    let g = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    for idx in 0..6 {
        let (insns, _) = encode_bytecodes(&[
            Bytecode::Ldai(Imm(idx)),
            Bytecode::Add2(Imm(0), Reg(0)),
            Bytecode::Return,
        ])
        .unwrap();
        b.class_add_method(
            g,
            &format!("fn_{idx}"),
            proto,
            AccessFlags::STATIC,
            &insns,
            0,
            3,
        );
    }
    let raw_abc: Arc<[u8]> = b.finalize().unwrap().into();
    let eager_file = decode(&raw_abc).unwrap();
    let lazy_file = decode_lazy(Arc::clone(&raw_abc)).unwrap();
    assert!(
        lazy_file
            .all_methods()
            .all(|(_, m)| matches!(m.body.as_ref().map(|b| &b.code), Some(MethodCode::Span(_))))
    );

    let m_eager = lift_file(&eager_file).unwrap();
    let m_lazy_seq = lift_file_with_options(
        &lazy_file,
        &LiftOptions {
            retain_tail_capacity: false,
            parallel: false,
        },
    )
    .unwrap();
    let m_lazy_par = lift_file_forced_parallel(&lazy_file, false).unwrap();

    assert_eq!(modules_structurally_eq(&m_eager, &m_lazy_seq), Ok(()));
    assert_eq!(modules_structurally_eq(&m_eager, &m_lazy_par), Ok(()));
}

#[test]
fn legacy_module_slots_scope_names_and_local_vars_seq_vs_parallel_parity() {
    // Exercises `#103` pre-indexed tables across sequential and Rayon parallel paths:
    // 1. Standalone `_ESModuleRecord` + `_ESScopeNamesRecord` (including duplicate
    //    `source_file` field names where first-occurrence wins!).
    // 2. Class with `--merge-abc` `EsModule` shared across multiple methods (testing
    //    concurrent `OnceLock<Box<LegacyModuleSlotIndex>>` initialization + hits).
    // 3. Class with an EMPTY `--merge-abc` `EsModule` (`requests: [], records: []`)
    //    which MUST NOT fall back to standalone `_ESModuleRecord` slots!
    // 4. `debug.local_vars` with duplicate `(name, ty, scope)` entries AND same-`name`
    //    entries carrying distinct `scope` / `ty` (`O(L)` `HashSet` deduplication).
    let mut s = StringPool::new();
    let esm_rec_desc = s.get_or_intern(abcd_file::ES_MODULE_RECORD_DESCRIPTOR);
    let scope_rec_desc = s.get_or_intern(abcd_file::ES_SCOPE_NAMES_RECORD_DESCRIPTOR);
    let cls_standalone_desc = s.get_or_intern("Lpkg/UsesStandalone;");
    let cls_merged_desc = s.get_or_intern("Lpkg/UsesMerged;");
    let cls_empty_esm_desc = s.get_or_intern("Lpkg/UsesEmptyEsm;");

    let mod_field = s.get_or_intern(abcd_file::MODULE_RECORD_IDX_FIELD);
    let standalone_mod_field = s.get_or_intern("standalone.js");
    let sf_one = s.get_or_intern("standalone_one.ts");
    let sf_two = s.get_or_intern("standalone_two.ts");
    let scope_s0 = s.get_or_intern("scopeZero");
    let scope_s1 = s.get_or_intern("scopeOneShadow");
    let scope_s2 = s.get_or_intern("scopeTwo");

    let st_req = s.get_or_intern("./standalone_dep");
    let st_imp_local = s.get_or_intern("stImpLocal");
    let st_imp_pub = s.get_or_intern("stImpPub");
    let st_exp_local = s.get_or_intern("stExpLocal");
    let st_exp_pub = s.get_or_intern("stExpPub");

    let mg_req0 = s.get_or_intern("./mg0");
    let mg_req1 = s.get_or_intern("./mg1");
    let mg_ns1 = s.get_or_intern("mgNs1");
    let mg_imp0 = s.get_or_intern("mgImp0");
    let mg_collide = s.get_or_intern("mgCollide"); // imp0 import_name (0) AND imp1 local_name (1); exp0 export_name (0) AND exp1 local_name (1)
    let mg_other = s.get_or_intern("mgOther");
    let mg_exp0 = s.get_or_intern("mgExp0");

    let fn0 = s.get_or_intern("f0");
    let fn1 = s.get_or_intern("f1");
    let loc_x = s.get_or_intern("x");
    let i32_sig = s.get_or_intern("i32");
    let f64_sig = s.get_or_intern("f64");

    let lit_arrays = vec![
        LiteralArray::new(vec![LiteralValue::String(scope_s0)]),
        LiteralArray::new(vec![LiteralValue::String(scope_s1)]),
        LiteralArray::new(vec![LiteralValue::String(scope_s2)]),
    ];

    let esm_rec_cls = abcd_file::Class {
        descriptor: esm_rec_desc,
        name: esm_rec_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: vec![Field {
            name: standalone_mod_field,
            offset: 0,
            field_type: Type::U32,
            access_flags: AccessFlags::STATIC,
            is_external: false,
            initial_value: Some(FieldValue::ModuleData(ModuleData {
                source_offset: 0,
                requests: vec![st_req],
                records: vec![
                    ModuleRecord::RegularImport {
                        local_name: st_imp_local,
                        import_name: st_imp_pub,
                        module_request_idx: 0,
                    },
                    ModuleRecord::LocalExport {
                        local_name: st_exp_local,
                        export_name: st_exp_pub,
                    },
                ],
            })),
            annotations: Default::default(),
        }],
        annotations: Default::default(),
    };

    // Standalone `_ESScopeNamesRecord` with duplicate `sf_one` field (`lit[0]` must beat `lit[1]`).
    let scope_rec_cls = abcd_file::Class {
        descriptor: scope_rec_desc,
        name: scope_rec_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: Vec::new(),
        fields: vec![
            Field {
                name: sf_one,
                offset: 0,
                field_type: Type::U32,
                access_flags: AccessFlags::STATIC,
                is_external: false,
                initial_value: Some(FieldValue::literal_array_ref(LiteralArrayIdx(0))),
                annotations: Default::default(),
            },
            Field {
                name: sf_one,
                offset: 4,
                field_type: Type::U32,
                access_flags: AccessFlags::STATIC,
                is_external: false,
                initial_value: Some(FieldValue::literal_array_ref(LiteralArrayIdx(1))),
                annotations: Default::default(),
            },
            Field {
                name: sf_two,
                offset: 8,
                field_type: Type::U32,
                access_flags: AccessFlags::STATIC,
                is_external: false,
                initial_value: Some(FieldValue::literal_array_ref(LiteralArrayIdx(2))),
                annotations: Default::default(),
            },
        ],
        annotations: Default::default(),
    };

    // Method in `cls_standalone` resolving `stImpPub` (`import_name` fallback -> 0),
    // `stExpPub` (`export_name` fallback -> 0), `st_req` (0), standalone `sf_one` scope,
    // and deduplicating `debug.local_vars`.
    let m_st_0 = Method {
        name: fn0,
        offset: 0x100,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::Function,
        source_lang: FileSourceLang::TypeScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 1,
            num_args: 0,
            code: MethodCode::Decoded(vec![
                Bytecode::DeprecatedLdmodulevar(EntityId(0), Imm(0)), // 0
                Bytecode::DeprecatedStmodulevar(EntityId(1)),         // 1
                Bytecode::DeprecatedGetmodulenamespace(EntityId(2)),  // 2
                Bytecode::Return,                                     // 3
            ]),
            entities: HashMap::from([
                ((EntityKind::StringId, 0), EntityRef::string(st_imp_pub)),
                ((EntityKind::StringId, 1), EntityRef::string(st_exp_pub)),
                ((EntityKind::StringId, 2), EntityRef::string(st_req)),
            ])
            .into(),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: Some(MethodDebugInfo {
            source_file: Some(sf_one),
            source_code: None,
            line_table: vec![LineEntry { index: 0, line: 1 }],
            column_table: Vec::new(),
            local_vars: vec![
                // [0] `x: i32` over `[0..1]`
                LocalVarInfo {
                    name: loc_x,
                    type_name: i32_sig,
                    type_signature: i32_sig,
                    reg_number: 0,
                    start: 0,
                    end: 1,
                },
                // [1] Exact duplicate of [0] -> deduplicated!
                LocalVarInfo {
                    name: loc_x,
                    type_name: i32_sig,
                    type_signature: i32_sig,
                    reg_number: 0,
                    start: 0,
                    end: 1,
                },
                // [2] Same name `x` & type `i32`, DIFFERENT scope `[2..3]` -> preserved!
                LocalVarInfo {
                    name: loc_x,
                    type_name: i32_sig,
                    type_signature: i32_sig,
                    reg_number: 0,
                    start: 2,
                    end: 3,
                },
                // [3] Same name `x` & scope `[0..1]`, DIFFERENT type `f64` -> preserved!
                LocalVarInfo {
                    name: loc_x,
                    type_name: f64_sig,
                    type_signature: f64_sig,
                    reg_number: 0,
                    start: 0,
                    end: 1,
                },
            ],
            params: Vec::new(),
        }),
    };

    let m_st_1 = Method {
        name: fn1,
        offset: 0x180,
        debug: Some(MethodDebugInfo {
            source_file: Some(sf_two),
            source_code: None,
            line_table: vec![LineEntry { index: 0, line: 2 }],
            column_table: Vec::new(),
            local_vars: Vec::new(),
            params: Vec::new(),
        }),
        ..m_st_0.clone()
    };

    let cls_standalone = abcd_file::Class {
        descriptor: cls_standalone_desc,
        name: cls_standalone_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::TypeScript,
        source_file: Some(sf_one),
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: vec![m_st_0, m_st_1],
        fields: Vec::new(),
        annotations: Default::default(),
    };

    let make_merged_method = |name, off| Method {
        name,
        offset: off,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::Function,
        source_lang: FileSourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 0,
            num_args: 0,
            code: MethodCode::Decoded(vec![
                Bytecode::DeprecatedLdmodulevar(EntityId(0), Imm(0)), // External `mgCollide` -> slot 1
                Bytecode::DeprecatedLdmodulevar(EntityId(0), Imm(1)), // Local `mgCollide` -> slot 1
                Bytecode::DeprecatedStmodulevar(EntityId(0)),         // Store `mgCollide` -> slot 1
                Bytecode::DeprecatedGetmodulenamespace(EntityId(1)),  // Namespace `mgNs1` -> slot 1
                Bytecode::Return,
            ]),
            entities: HashMap::from([
                ((EntityKind::StringId, 0), EntityRef::string(mg_collide)),
                ((EntityKind::StringId, 1), EntityRef::string(mg_ns1)),
            ])
            .into(),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };

    let cls_merged = abcd_file::Class {
        descriptor: cls_merged_desc,
        name: cls_merged_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: vec![
            make_merged_method(fn0, 0x200),
            make_merged_method(fn1, 0x280),
        ],
        fields: vec![Field {
            name: mod_field,
            offset: 0,
            field_type: Type::U32,
            access_flags: AccessFlags::STATIC,
            is_external: false,
            initial_value: Some(FieldValue::ModuleData(ModuleData {
                source_offset: 0,
                requests: vec![mg_req0, mg_req1],
                records: vec![
                    ModuleRecord::RegularImport {
                        local_name: mg_imp0,
                        import_name: mg_collide,
                        module_request_idx: 0,
                    },
                    ModuleRecord::NamespaceImport {
                        local_name: mg_ns1,
                        module_request_idx: 1,
                    },
                    ModuleRecord::RegularImport {
                        local_name: mg_collide,
                        import_name: mg_other,
                        module_request_idx: 1,
                    },
                    ModuleRecord::LocalExport {
                        local_name: mg_exp0,
                        export_name: mg_collide,
                    },
                    ModuleRecord::LocalExport {
                        local_name: mg_collide,
                        export_name: mg_other,
                    },
                ],
            })),
            annotations: Default::default(),
        }],
        annotations: Default::default(),
    };

    // Empty `EsModule` class: `stImpLocal` MUST NOT fall back to standalone `_ESModuleRecord`!
    let cls_empty_esm = abcd_file::Class {
        descriptor: cls_empty_esm_desc,
        name: cls_empty_esm_desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: vec![Method {
            name: fn0,
            offset: 0x300,
            access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
            function_kind: FileFunctionKind::Function,
            source_lang: FileSourceLang::EcmaScript,
            is_external: false,
            return_type: None,
            arg_types: Vec::new(),
            body: Some(MethodBody {
                num_vregs: 0,
                num_args: 0,
                code: MethodCode::Decoded(vec![
                    Bytecode::DeprecatedLdmodulevar(EntityId(0), Imm(0)),
                    Bytecode::Return,
                ]),
                entities: HashMap::from([(
                    (EntityKind::StringId, 0),
                    EntityRef::string(st_imp_local),
                )])
                .into(),
                try_blocks: Vec::new(),
                ic_size: None,
            }),
            annotations: Default::default(),
            param_annotations: Default::default(),
            debug: None,
        }],
        fields: vec![Field {
            name: mod_field,
            offset: 0,
            field_type: Type::U32,
            access_flags: AccessFlags::STATIC,
            is_external: false,
            initial_value: Some(FieldValue::ModuleData(ModuleData {
                source_offset: 0,
                requests: Vec::new(),
                records: Vec::new(),
            })),
            annotations: Default::default(),
        }],
        annotations: Default::default(),
    };

    let file = File {
        version: Version::new(0, 0, 0, 2),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings: s,
        classes: [
            (esm_rec_desc, esm_rec_cls),
            (scope_rec_desc, scope_rec_cls),
            (cls_standalone_desc, cls_standalone),
            (cls_merged_desc, cls_merged),
            (cls_empty_esm_desc, cls_empty_esm),
        ]
        .into_iter()
        .collect(),
        literal_arrays: lit_arrays,
        literal_array_header_offsets: Vec::new(),
    };

    let seq = lift_file_with_options(
        &file,
        &LiftOptions {
            retain_tail_capacity: false,
            parallel: false,
        },
    )
    .expect("sequential lift succeeds");
    assert!(abcd_ir::verify_module(&seq).errors.is_empty());

    // Check local_vars deduplication on `m_st_0` (`functions[0]`): 3 distinct `LocalName`s!
    let dbg0 = seq.functions[0].debug.as_ref().expect("m_st_0 debug");
    assert_eq!(dbg0.local_names.len(), 3);
    assert_ne!(dbg0.local_names[0].scope, dbg0.local_names[1].scope);
    assert_ne!(dbg0.local_names[0].ty, dbg0.local_names[2].ty);

    // Check first-wins standalone `_ESScopeNamesRecord` lookup (`scopeZero`, not `scopeOneShadow`).
    let scope_cid = dbg0.scope_names.expect("standalone scope_names");
    let s0_sym = seq.sym.get("scopeZero").expect("scopeZero interned");
    let s0_const = seq.consts.lookup(&abcd_ir::Const::String(s0_sym)).unwrap();
    assert_eq!(
        seq.consts.get(scope_cid),
        Some(&abcd_ir::Const::ArrayLiteral(vec![s0_const]))
    );

    // Check empty `EsModule` isolation (`functions[4]` falls back to `stImpLocal` Sym.0, NOT 0!).
    let st_imp_sym = seq.sym.get("stImpLocal").expect("stImpLocal interned");
    assert_ne!(st_imp_sym.raw(), 0);
    let empty_esm_op =
        &seq.insts[seq.blocks[seq.functions[4].blocks[0].index()].insts[0].index()].op;
    assert!(matches!(
        empty_esm_op,
        abcd_ir::Op::LoadModuleVar { index, kind: abcd_ir::ModuleVarKind::External }
            if *index == st_imp_sym.raw()
    ));

    for threads in [1usize, 2, 4] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .stack_size(256 * 1024)
            .build()
            .unwrap();
        let par = pool
            .install(|| lift_file_forced_parallel(&file, false))
            .expect("forced-parallel lift succeeds");
        assert!(abcd_ir::verify_module(&par).errors.is_empty());
        assert_eq!(modules_structurally_eq(&seq, &par), Ok(()));
    }
}
