//! #32 regression tests: on-demand pre-entry trampoline synthesis when
//! bytecode offset `0` (`leader 0`) carries incoming edges (loop
//! back-edges, self-loops at 0, or catch handlers at 0), Sendable class
//! member-attribute extraction across trailing field-layout buffers, and
//! full `lift_file` + `verify_module` validation on the commercial
//! `modules.abc` corpus when present locally.

use std::collections::HashMap;
use std::path::Path;

use abcd_file::{
    AccessFlags, CatchBlock, FileType, FunctionKind as FileFunctionKind, LiteralArrayIdx,
    LiteralValue, MethodBody, SourceLang as FileSourceLang, TryBlock, Version, decode,
};
use abcd_ir::module::FunctionKind;
use abcd_ir::op::MemberAttrs;
use abcd_ir::{Edge, EdgeKind, FuncId, Module, Op, ValueDef};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Label, Reg};
use abcd_lift::lift_file;

fn verify_clean(m: &Module) {
    let report = abcd_ir::verify_module(m);
    assert!(
        report.errors.is_empty(),
        "verifier errors ({} total): {:?}",
        report.errors.len(),
        &report.errors[..report.errors.len().min(10)]
    );
}

fn single_method_file(
    num_vregs: u32,
    num_args: u32,
    bytecodes: Vec<Bytecode>,
    try_blocks: Vec<TryBlock>,
) -> abcd_file::File {
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LLoop0;");
    let mname = strings.get_or_intern("f");
    let method = abcd_file::Method {
        name: mname,
        offset: 100,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::None,
        source_lang: FileSourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs,
            num_args,
            code: abcd_file::MethodCode::Decoded(bytecodes),
            entities: abcd_file::MethodEntities::new(),
            try_blocks,
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };
    let class = abcd_file::Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: vec![method],
        fields: Vec::new(),
        annotations: Default::default(),
    };
    abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(desc, class)].into_iter().collect(),
        literal_arrays: Vec::new(),
        literal_array_header_offsets: Vec::new(),
    }
}

#[test]
fn loop_backedge_to_offset_zero_synthesizes_pre_entry_and_param_phi() {
    // Frame: num_vregs = 1 (v0), num_args = 1 (a0 = Reg(1)).
    // [0] lda a0          ┐ header0 (raw block 0)
    // [1] jeqz 5          ┘
    // [2] inc 0           ┐ latch   (raw block 1) → mutates a0 and jumps to 0
    // [3] sta a0          │
    // [4] jmp 0           ┘
    // [5] lda a0          ┐ exit    (raw block 2)
    // [6] return          ┘
    let file = single_method_file(
        1,
        1,
        vec![
            Bytecode::Lda(Reg(1)),
            Bytecode::Jeqz(Label(5)),
            Bytecode::Inc(Imm(0)),
            Bytecode::Sta(Reg(1)),
            Bytecode::Jmp(Label(0)),
            Bytecode::Lda(Reg(1)),
            Bytecode::Return,
        ],
        Vec::new(),
    );

    let m = lift_file(&file).expect("lift loop to offset 0");
    verify_clean(&m);

    let f = &m.functions[0];
    assert_eq!(
        f.blocks.len(),
        4,
        "pre_entry + 3 raw blocks (header0, latch, exit)"
    );
    let pre_entry = f.blocks[0];
    let header0 = f.blocks[1];
    let latch = f.blocks[2];
    let exit = f.blocks[3];

    // Entry block is pure: zero predecessors and a single Branch to header0.
    assert!(m.blocks[pre_entry.index()].preds.is_empty());
    assert_eq!(m.blocks[pre_entry.index()].insts.len(), 1);
    let pre_term = &m.insts[m.blocks[pre_entry.index()].insts[0].index()];
    assert!(matches!(pre_term.op, Op::Branch { dest } if dest == header0));
    assert!(pre_term.loc.is_none());

    // header0 receives Normal edges from pre_entry and latch, and opens with
    // a Phi joining Param(0) (from pre_entry) with the incremented value (from latch).
    assert_eq!(
        m.blocks[header0.index()].preds,
        vec![
            Edge {
                from: pre_entry,
                kind: EdgeKind::Normal,
            },
            Edge {
                from: latch,
                kind: EdgeKind::Normal,
            },
        ]
    );
    let first_header_inst = &m.insts[m.blocks[header0.index()].insts[0].index()];
    let Op::Phi { entries } = &first_header_inst.op else {
        panic!(
            "expected leading Phi on header0, got {:?}",
            first_header_inst.op
        );
    };
    assert_eq!(entries.len(), 2);
    let param0 = f.params[0];
    assert_eq!(
        entries[0],
        (
            Edge {
                from: pre_entry,
                kind: EdgeKind::Normal,
            },
            param0
        )
    );
    let latch_val = entries[1].1;
    assert_ne!(
        latch_val, param0,
        "back-edge carries updated parameter value"
    );
    assert!(matches!(m.values[latch_val.index()].def, ValueDef::Inst(_)));

    // Exit returns the header0 phi value.
    let phi_res = first_header_inst.result.expect("phi result");
    let exit_last = *m.blocks[exit.index()]
        .insts
        .last()
        .expect("exit terminator");
    assert!(matches!(
        m.insts[exit_last.index()].op,
        Op::Return { value: Some(v) } if v == phi_res
    ));
}

#[test]
fn single_block_self_loop_at_offset_zero_preserves_loop_phi() {
    // [0] lda a0; [1] inc 0; [2] sta a0; [3] jnez 0; [4] lda a0; [5] return
    let file = single_method_file(
        0,
        1,
        vec![
            Bytecode::Lda(Reg(0)),
            Bytecode::Inc(Imm(0)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Jnez(Label(0)),
            Bytecode::Lda(Reg(0)),
            Bytecode::Return,
        ],
        Vec::new(),
    );

    let m = lift_file(&file).expect("lift self-loop at offset 0");
    verify_clean(&m);

    let f = &m.functions[0];
    assert_eq!(f.blocks.len(), 3, "pre_entry + self-loop header0 + exit");
    let pre_entry = f.blocks[0];
    let header0 = f.blocks[1];
    assert!(m.blocks[pre_entry.index()].preds.is_empty());
    let first_inst = &m.insts[m.blocks[header0.index()].insts[0].index()];
    let Op::Phi { entries } = &first_inst.op else {
        panic!("expected Phi on self-loop header0, got {:?}", first_inst.op);
    };
    assert_eq!(entries.len(), 2);
    assert_eq!(entries[0].1, f.params[0]);
    assert_ne!(entries[1].1, f.params[0]);
}

#[test]
fn non_loop_entry_does_not_allocate_extra_pre_entry_block() {
    // Loop starts at instruction 2, NOT instruction 0 → zero drift.
    let file = single_method_file(
        1,
        0,
        vec![
            Bytecode::Ldai(Imm(0)),    // 0 (entry)
            Bytecode::Sta(Reg(0)),     // 1
            Bytecode::Lda(Reg(0)),     // 2 (loop header)
            Bytecode::Jnez(Label(2)),  // 3
            Bytecode::Returnundefined, // 4
        ],
        Vec::new(),
    );
    let m = lift_file(&file).expect("lift normal loop");
    verify_clean(&m);
    assert_eq!(
        m.functions[0].blocks.len(),
        3,
        "only the 3 raw blocks (0..2, 2..4, 4..5), no synthetic pre-entry"
    );
}

#[test]
fn try_protecting_offset_zero_and_catch_at_offset_zero_verify_cleanly() {
    // Case A: try covers [0..3) while latch at [3..4) jumps back to 0,
    // and catch handler is at 4. Synthetic pre_entry must NOT be in
    // TryRegion.protected, while header0 MUST be protected.
    let file_try_at_zero = single_method_file(
        1,
        1,
        vec![
            Bytecode::Lda(Reg(1)),    // 0 (try start & loop header)
            Bytecode::Inc(Imm(0)),    // 1
            Bytecode::Jeqz(Label(3)), // 2 (try end)
            Bytecode::Sta(Reg(1)),    // 3 (latch)
            Bytecode::Jmp(Label(0)),  // 4 (jumps back to 0)
            Bytecode::Sta(Reg(0)),    // 5 (catch handler)
            Bytecode::Lda(Reg(0)),    // 6
            Bytecode::Return,         // 7
        ],
        vec![TryBlock {
            start: 0,
            len: 3,
            catches: vec![CatchBlock {
                type_class: None,
                handler: 5,
                len: 3,
            }],
        }],
    );
    let m_a = lift_file(&file_try_at_zero).expect("lift try at 0 with backedge");
    verify_clean(&m_a);
    let f_a = &m_a.functions[0];
    let pre_a = f_a.blocks[0];
    let header0_a = f_a.blocks[1];
    assert!(m_a.blocks[pre_a.index()].preds.is_empty());
    assert_eq!(f_a.try_regions.len(), 1);
    assert!(!f_a.try_regions[0].protected.contains(&pre_a));
    assert!(f_a.try_regions[0].protected.contains(&header0_a));

    // Case B: catch handler itself sits at bytecode offset 0!
    // [0] sta v0; [1] jeqz 2; [2] ldundefined; [3] throw; [4] lda v0; [5] return
    // TryBlock covers [2..4) and dispatches to handler = 0.
    let file_catch_at_zero = single_method_file(
        1,
        0,
        vec![
            Bytecode::Sta(Reg(0)),    // 0 (handler == 0 & normal entry target)
            Bytecode::Jeqz(Label(4)), // 1
            Bytecode::Ldundefined,    // 2 (try [2..4))
            Bytecode::Throw,          // 3
            Bytecode::Lda(Reg(0)),    // 4
            Bytecode::Return,         // 5
        ],
        vec![TryBlock {
            start: 2,
            len: 2,
            catches: vec![CatchBlock {
                type_class: None,
                handler: 0,
                len: 2,
            }],
        }],
    );
    let m_b = lift_file(&file_catch_at_zero).expect("lift catch handler at offset 0");
    verify_clean(&m_b);
    let f_b = &m_b.functions[0];
    let pre_b = f_b.blocks[0];
    let header0_b = f_b.blocks[1];
    assert!(m_b.blocks[pre_b.index()].preds.is_empty());
    assert_eq!(f_b.try_regions[0].catches[0].handler, header0_b);
    assert_eq!(
        m_b.values[f_b.try_regions[0].catches[0].exception.index()].def,
        ValueDef::ExceptionParam(header0_b)
    );
}

#[test]
fn sendable_class_with_trailing_field_layout_lifts_member_attrs() {
    // Vendor sendable class buffer shape:
    // [ string:"rule", getter:m0, method_affiliate:0,
    //   string:"defaultType", getter:m1, method_affiliate:0,
    //   i32:1, lit_offset:field_types ]
    let mut strings = abcd_file::StringPool::default();
    let desc = strings.get_or_intern("LSendable;");
    let ctor_name = strings.get_or_intern("SortRuleString");
    let rule_name = strings.get_or_intern("rule");
    let def_name = strings.get_or_intern("defaultType");
    let field_name = strings.get_or_intern("formatStr");
    let main_name = strings.get_or_intern("func_main_0");

    let empty_method = |name, offset| abcd_file::Method {
        name,
        offset,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::SendableFunction,
        source_lang: FileSourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 0,
            num_args: 3,
            code: abcd_file::MethodCode::Decoded(vec![Bytecode::Returnundefined]),
            entities: abcd_file::MethodEntities::new(),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };

    let ctor = empty_method(ctor_name, 100);
    let m_rule = empty_method(rule_name, 200);
    let m_def = empty_method(def_name, 300);
    let main = abcd_file::Method {
        name: main_name,
        offset: 400,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::Function,
        source_lang: FileSourceLang::EcmaScript,
        is_external: false,
        return_type: None,
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 1,
            num_args: 3,
            code: abcd_file::MethodCode::Decoded(vec![
                Bytecode::CallruntimeDefinesendableclass(
                    Imm(0),
                    EntityId(1),
                    EntityId(2),
                    Imm(2),
                    Reg(0),
                ),
                Bytecode::Return,
            ]),
            entities: HashMap::from([
                (
                    (EntityKind::MethodId, 1),
                    abcd_file::EntityRef::Method(abcd_file::MethodIdx(0)),
                ),
                (
                    (EntityKind::LiteralarrayId, 2),
                    abcd_file::EntityRef::LiteralArray(LiteralArrayIdx(0)),
                ),
            ])
            .into(),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };

    let class = abcd_file::Class {
        descriptor: desc,
        name: desc,
        access_flags: AccessFlags::PUBLIC,
        source_lang: FileSourceLang::EcmaScript,
        source_file: None,
        is_external: false,
        super_class: None,
        interfaces: Vec::new(),
        methods: vec![ctor, m_rule, m_def, main],
        fields: Vec::new(),
        annotations: Default::default(),
    };
    let member_buf = abcd_file::LiteralArray::new(vec![
        LiteralValue::String(rule_name),
        LiteralValue::Getter(abcd_file::MethodIdx(1)),
        LiteralValue::MethodAffiliate(0),
        LiteralValue::String(def_name),
        LiteralValue::Getter(abcd_file::MethodIdx(2)),
        LiteralValue::MethodAffiliate(0),
        LiteralValue::Integer(1),
        LiteralValue::LiteralArray(LiteralArrayIdx(1)),
    ]);
    let field_buf = abcd_file::LiteralArray::new(vec![
        LiteralValue::String(field_name),
        LiteralValue::Integer(2),
        LiteralValue::Integer(1),
    ]);
    let file = abcd_file::File {
        version: Version::new(12, 0, 6, 0),
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes: [(desc, class)].into_iter().collect(),
        literal_arrays: vec![member_buf, field_buf],
        literal_array_header_offsets: Vec::new(),
    };

    let m = lift_file(&file).expect("lift definesendableclass");
    verify_clean(&m);
    let attrs = m
        .insts
        .iter()
        .find_map(|inst| match &inst.op {
            Op::DefineSendableClass(data) => Some(data.member_attrs.clone()),
            _ => None,
        })
        .expect("DefineSendableClass emitted");
    assert_eq!(
        attrs,
        vec![
            MemberAttrs {
                is_static: false,
                kind: FunctionKind::Getter,
            },
            MemberAttrs {
                is_static: true,
                kind: FunctionKind::Getter,
            },
        ]
    );
}

#[test]
#[ignore = "requires local-only modules.abc (gitignored)"]
fn commercial_modules_abc_lifts_and_verifies_zero_errors() {
    let abc_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../modules.abc");
    if !abc_path.exists() {
        return;
    }

    let bytes = std::fs::read(&abc_path).expect("read modules.abc");
    let file = decode(&bytes).expect("decode modules.abc");
    let module = lift_file(&file).expect("lift modules.abc");

    assert_eq!(module.functions.len(), 58_699, "commercial function count");
    verify_clean(&module);

    // Explicitly verify the 5 offset-0 back-edge functions that previously
    // triggered EntryHasPred now start with a pure 0-pred pre-entry block.
    for raw_fid in [27_285u32, 46_771, 55_058, 55_421, 56_759] {
        let f = &module.functions[FuncId::new(raw_fid).index()];
        assert!(
            f.blocks.len() >= 2,
            "FuncId({raw_fid}) has pre_entry + body"
        );
        let pre_entry = f.blocks[0];
        let header0 = f.blocks[1];
        assert!(
            module.blocks[pre_entry.index()].preds.is_empty(),
            "FuncId({raw_fid}) entry block must have zero predecessors"
        );
        assert!(
            matches!(
                module.insts[module.blocks[pre_entry.index()].insts[0].index()].op,
                Op::Branch { dest } if dest == header0
            ),
            "FuncId({raw_fid}) pre_entry must branch directly to header0"
        );
        assert!(
            module.blocks[header0.index()].preds.len() >= 2,
            "FuncId({raw_fid}) header0 joins pre_entry + loop back-edge"
        );
    }

    // Verify all 6 commercial DefineSendableClass sites lift cleanly and the
    // 4 method-bearing sendable classes recover their exact member_attrs.
    let sendable_attrs: Vec<usize> = module
        .insts
        .iter()
        .filter_map(|i| match &i.op {
            Op::DefineSendableClass(data) => Some(data.member_attrs.len()),
            _ => None,
        })
        .collect();
    assert_eq!(sendable_attrs, vec![4, 0, 16, 8, 1, 0]);
}
