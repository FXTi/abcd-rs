//! Round 3 cross-crate conformance & regression gates (`#50`, `#55`–`#58`,
//! `#60`, `#61`):
//!
//! 1. **`R3-A8` / `R3-A9` (`#55`)**: Table-driven `decode → lift → verify →
//!    [opt] → rewrite_file → encode → decode` opcode identity & `acc`
//!    input/output preservation across all Round 3 split/fixed opcodes.
//! 2. **`R3-X1`–`R3-X5` (`#61`)**:
//!    - Raw `jeqz` / `jnez` (`ldnull; jeqz` vs `ldnan; jnez`) round-trip and
//!      non-boolean `CondBranch` (`Istrue` normalization before `Jnez`).
//!    - 2-slot IC allocation (`Instanceof`, `Typeof`, `Createregexpwithliteral`)
//!      and `0xff` (`INVALID_IC_SLOT`) boundary skip.
//!    - Competing nested catch-handler phis over a shared protected block (`R3-X3`)
//!      and multi-`ExceptionParam` shared handler (`R3-X4`).
//!    - `*PropIdx` `>= 2^32` / negative / `-0.0` `*byvalue` lowering (`R3-X5`).
//! 3. **`R3-H7`–`R3-H9` (`#57`)**:
//!    - `wide.*` instruction selection (`WideLdlexvar`, `WideStlexvar`,
//!      `WideNewlexenv`, `WideCopyrestargs`, `WideLdobjbyindex`).
//!    - `MethodDebugInfo` post-layout reconstruction (`line_table`, `column_table`,
//!      cleared stale `local_vars`).
//!    - Lossless `LiteralArray` tag preservation without cross-tag deduplication.

use std::collections::{BTreeMap, HashMap};

use abcd_file::{
    AccessFlags, CatchBlock, Class, ColumnEntry, EntityRef, File, FileType, FunctionKind,
    LineEntry, LiteralArray, LiteralArrayIdx, LiteralValue, LocalVarInfo, Method, MethodBody,
    MethodDebugInfo, MethodIdx, SourceLang, StringPool, TryBlock, Type, Version, decode, encode,
};
use abcd_ir::verify_module;
use abcd_isa::{Bytecode, BytecodeFlags, EntityId, EntityKind, Imm, Label, Reg};
use abcd_lift::lift_file;
use abcd_lower::{LowerOptions, rewrite_file};
use abcd_opt::optimize_module;

const V12: Version = Version::new(12, 0, 6, 0);

type EntityEntries = Vec<((EntityKind, u32), EntityRef)>;

/// Build a single-class `File` with `func_main_0` and optional helper method `helper_fn`.
#[expect(
    clippy::too_many_arguments,
    reason = "synthetic File fixture builder takes explicit per-method tables"
)]
fn build_test_file(
    bytecodes: Vec<Bytecode>,
    entities: EntityEntries,
    literal_arrays: Vec<LiteralArray>,
    strings: StringPool,
    num_vregs: u32,
    num_args: u32,
    try_blocks: Vec<TryBlock>,
    debug: Option<MethodDebugInfo>,
) -> File {
    let mut strings = strings;
    let desc = strings.get_or_intern("L_GLOBAL;");
    let main_name = strings.get_or_intern("func_main_0");
    let helper_name = strings.get_or_intern("helper_fn");

    let main_method = Method {
        name: main_name,
        offset: 0,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FunctionKind::Function,
        source_lang: SourceLang::EcmaScript,
        is_external: false,
        return_type: Some(Type::Tagged),
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs,
            num_args,
            bytecodes,
            entities: entities.into_iter().collect(),
            try_blocks,
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug,
    };

    let helper_method = Method {
        name: helper_name,
        offset: 0,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FunctionKind::Function,
        source_lang: SourceLang::EcmaScript,
        is_external: false,
        return_type: Some(Type::Tagged),
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 0,
            num_args: 3,
            bytecodes: vec![Bytecode::Returnundefined],
            entities: HashMap::new(),
            try_blocks: Vec::new(),
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    };

    let mut classes = BTreeMap::new();
    classes.insert(
        desc,
        Class {
            descriptor: desc,
            name: desc,
            access_flags: AccessFlags::PUBLIC,
            source_lang: SourceLang::EcmaScript,
            source_file: None,
            is_external: false,
            super_class: None,
            interfaces: Vec::new(),
            methods: vec![main_method, helper_method],
            fields: Vec::new(),
            annotations: Default::default(),
        },
    );

    File {
        version: V12,
        checksum: 0,
        size: 0,
        file_type: FileType::Dynamic,
        strings,
        classes,
        literal_arrays,
        literal_array_header_offsets: Vec::new(),
    }
}

/// Run `encode -> decode -> lift -> verify -> [opt -> verify] -> rewrite_file -> encode -> decode`
/// and return the re-decoded `func_main_0` method + owning `File`.
fn roundtrip_main(file: &File, optimize: bool) -> (File, MethodBody) {
    let raw = encode(file).expect("initial encode");
    let decoded = decode(&raw).expect("initial decode");
    let mut module = lift_file(&decoded).expect("lift_file");
    let rep = verify_module(&module);
    assert!(rep.is_ok(), "pre-opt verify failed: {:?}", rep.errors);

    if optimize {
        optimize_module(&mut module);
        let rep_opt = verify_module(&module);
        assert!(
            rep_opt.is_ok(),
            "post-opt verify failed: {:?}",
            rep_opt.errors
        );
    }

    let rewritten = rewrite_file(&module, &decoded, LowerOptions::default()).expect("rewrite_file");
    let out_bytes = encode(&rewritten).expect("re-encode");
    let redecoded = decode(&out_bytes).expect("re-decode");
    let (_, m0) = redecoded
        .all_methods()
        .find(|(_, m)| redecoded.strings.resolve(m.name) == Some("func_main_0"))
        .expect("func_main_0");
    let body = m0.body.clone().expect("func_main_0 body");
    assert_valid_ic_layout(&body);
    (redecoded, body)
}

/// Verify that every IC-carrying instruction in `body` has non-overlapping
/// `[slot, slot + width)` below `ic_size` (excluding `0xff` sentinel) and
/// never lands on or straddles `0xff` unless degraded to `0xff` as `eight_bit_ic`.
fn assert_valid_ic_layout(body: &MethodBody) {
    let mut occupied = HashMap::<u32, &'static str>::new();
    for bc in &body.bytecodes {
        let has_ic = bc.has_flag(BytecodeFlags::IC_SLOT) || bc.has_flag(BytecodeFlags::JIT_IC_SLOT);
        if !has_ic {
            continue;
        }
        let width: u32 = if bc.has_flag(BytecodeFlags::ONE_SLOT) {
            1
        } else {
            2
        };
        let slot = extract_ic_imm(bc).expect("IC instruction must expose immediate") as u32;
        if slot == 0xFF && bc.has_flag(BytecodeFlags::EIGHT_BIT_IC) {
            continue;
        }
        assert_ne!(
            slot,
            0xFF,
            "non-degraded IC instruction {} must never use reserved slot 0xFF",
            bc.mnemonic()
        );
        if width == 2 {
            assert_ne!(
                slot,
                0xFE,
                "2-slot IC instruction {} must never straddle 0xFE..=0xFF",
                bc.mnemonic()
            );
        }
        if let Some(ic_size) = body.ic_size {
            assert!(
                slot + width <= ic_size,
                "{} slot {}..{} exceeds ic_size {}",
                bc.mnemonic(),
                slot,
                slot + width,
                ic_size
            );
        }
        for s in slot..(slot + width) {
            if let Some(prev) = occupied.insert(s, bc.mnemonic()) {
                panic!(
                    "IC slot {s} overlapped between {prev} and {}",
                    bc.mnemonic()
                );
            }
        }
    }
}

fn extract_ic_imm(bc: &Bytecode) -> Option<i64> {
    use Bytecode::*;
    Some(match bc {
        Instanceof(i, _)
        | Isin(i, _)
        | Eq(i, _)
        | Noteq(i, _)
        | Stricteq(i, _)
        | Strictnoteq(i, _)
        | Less(i, _)
        | Lesseq(i, _)
        | Greater(i, _)
        | Greatereq(i, _)
        | Add2(i, _)
        | Sub2(i, _)
        | Mul2(i, _)
        | Div2(i, _)
        | Mod2(i, _)
        | Exp(i, _)
        | Shl2(i, _)
        | Shr2(i, _)
        | Ashr2(i, _)
        | And2(i, _)
        | Or2(i, _)
        | Xor2(i, _) => i.0,
        Typeof(i) | Neg(i) | Not(i) | Inc(i) | Dec(i) | Tonumber(i) | Tonumeric(i) => i.0,
        Createregexpwithliteral(i, ..)
        | Createobjectwithbuffer(i, _)
        | Createarraywithbuffer(i, _)
        | Definefunc(i, ..)
        | Definemethod(i, ..)
        | Defineclasswithbuffer(i, ..)
        | CallruntimeDefinesendableclass(i, ..) => i.0,
        Createemptyarray(i) | Gettemplateobject(i) | Getiterator(i) | Getasynciterator(i)
        | Callarg0(i) => i.0,
        Ldobjbyname(i, _)
        | Ldobjbyvalue(i, _)
        | Ldobjbyindex(i, _)
        | Ldsuperbyname(i, _)
        | Ldsuperbyvalue(i, _)
        | Stobjbyname(i, ..)
        | Stobjbyvalue(i, ..)
        | Stobjbyindex(i, ..)
        | Stownbyname(i, ..)
        | Stownbynamewithnameset(i, ..)
        | Stownbyvalue(i, ..)
        | Stownbyvaluewithnameset(i, ..)
        | Stownbyindex(i, ..)
        | Definefieldbyname(i, ..)
        | Definepropertybyname(i, ..)
        | CallruntimeDefinefieldbyvalue(i, ..)
        | CallruntimeDefinefieldbyindex(i, ..)
        | Stsuperbyname(i, ..)
        | Stsuperbyvalue(i, ..)
        | Ldglobalvar(i, _)
        | Tryldglobalbyname(i, _)
        | Stglobalvar(i, _)
        | Sttoglobalrecord(i, _)
        | Stconsttoglobalrecord(i, _)
        | Trystglobalbyname(i, _)
        | Ldprivateproperty(i, ..)
        | Stprivateproperty(i, ..)
        | CallruntimeDefineprivateproperty(i, ..)
        | Testin(i, ..)
        | Setobjectwithproto(i, _)
        | Closeiterator(i, _) => i.0,
        Callarg1(i, _)
        | Callargs2(i, ..)
        | Callargs3(i, ..)
        | Callthis0(i, _)
        | Callthis1(i, ..)
        | Callthis2(i, ..)
        | Callthis3(i, ..)
        | Callrange(i, ..)
        | Callthisrange(i, ..)
        | Supercallthisrange(i, ..)
        | Supercallarrowrange(i, ..)
        | Supercallspread(i, _)
        | Newobjrange(i, ..)
        | Newobjapply(i, _)
        | Apply(i, ..)
        | CallruntimeCallinit(i, _) => i.0,
        _ => return None,
    })
}

#[test]
fn r3_c1_to_h4_table_driven_opcode_identity_and_acc_roundtrip() {
    let mut sp = StringPool::new();
    let s_prop = sp.get_or_intern("propName");
    let s_pat = sp.get_or_intern("ab+c");

    // Table of `(case_name, bytecodes, entities, expected_mnemonic)`.
    // Every case feeds non-constant parameter registers (`Reg(3)`, `Reg(4)`, `Reg(5)`)
    // so `--optimize` cannot fold the instruction away unless an operand was
    // buggy/dropped (catching R3-H2 `definegettersetterbyvalue` ADCE bugs!).
    let cases: Vec<(&str, Vec<Bytecode>, EntityEntries, &str)> = vec![
        (
            "R3-C1 newobjapply",
            vec![
                Bytecode::Lda(Reg(4)),
                Bytecode::Newobjapply(Imm(0), Reg(3)),
                Bytecode::Return,
            ],
            vec![],
            "newobjapply",
        ),
        (
            "R3-C2 createasyncgeneratorobj + setgeneratorstate + asyncgeneratorresolve",
            vec![
                Bytecode::Createasyncgeneratorobj(Reg(3)),
                Bytecode::Sta(Reg(0)),
                Bytecode::Setgeneratorstate(Imm(2)),
                Bytecode::Asyncgeneratorresolve(Reg(0), Reg(4), Reg(5)),
                Bytecode::Return,
            ],
            vec![],
            "asyncgeneratorresolve",
        ),
        (
            "R3-C2 asyncgeneratorreject",
            vec![
                Bytecode::Lda(Reg(4)),
                Bytecode::Asyncgeneratorreject(Reg(3)),
                Bytecode::Return,
            ],
            vec![],
            "asyncgeneratorreject",
        ),
        (
            "R3-C3 sendable lex env",
            vec![
                Bytecode::CallruntimeNewsendableenv(Imm(2)),
                Bytecode::Lda(Reg(3)),
                Bytecode::CallruntimeStsendablevar(Imm(0), Imm(1)),
                Bytecode::CallruntimeLdsendablevar(Imm(0), Imm(1)),
                Bytecode::Return,
            ],
            vec![],
            "callruntime.ldsendablevar",
        ),
        (
            "R3-C3 wide patch var",
            vec![
                Bytecode::Lda(Reg(3)),
                Bytecode::WideStpatchvar(Imm(7)),
                Bytecode::WideLdpatchvar(Imm(7)),
                Bytecode::Return,
            ],
            vec![],
            "wide.ldpatchvar",
        ),
        (
            "R3-C4 notifyconcurrentresult",
            vec![
                Bytecode::Lda(Reg(3)),
                Bytecode::CallruntimeNotifyconcurrentresult,
                Bytecode::Returnundefined,
            ],
            vec![],
            "callruntime.notifyconcurrentresult",
        ),
        (
            "R3-C4 topropertykey",
            vec![
                Bytecode::Lda(Reg(3)),
                Bytecode::CallruntimeTopropertykey,
                Bytecode::Return,
            ],
            vec![],
            "callruntime.topropertykey",
        ),
        (
            "R3-C5 supercallarrowrange",
            vec![
                Bytecode::Mov(Reg(0), Reg(4)),
                Bytecode::Lda(Reg(3)),
                Bytecode::Supercallarrowrange(Imm(0), Imm(1), Reg(0)),
                Bytecode::Return,
            ],
            vec![],
            "supercallarrowrange",
        ),
        (
            "R3-C6 createobjectwithexcludedkeys imm=0 (1 key)",
            vec![
                Bytecode::Mov(Reg(0), Reg(4)),
                Bytecode::Createobjectwithexcludedkeys(Imm(0), Reg(3), Reg(0)),
                Bytecode::Return,
            ],
            vec![],
            "createobjectwithexcludedkeys",
        ),
        (
            "R3-C7 callruntime.callinit",
            vec![
                Bytecode::Lda(Reg(3)),
                Bytecode::CallruntimeCallinit(Imm(0), Reg(4)),
                Bytecode::Return,
            ],
            vec![],
            "callruntime.callinit",
        ),
        (
            "R3-H1 ldsuperbyname with explicit acc receiver",
            vec![
                Bytecode::Lda(Reg(4)),
                Bytecode::Ldsuperbyname(Imm(0), EntityId(0)),
                Bytecode::Return,
            ],
            vec![((EntityKind::StringId, 0), EntityRef::string(s_prop))],
            "ldsuperbyname",
        ),
        (
            "R3-H2 definegettersetterbyvalue preserving set_name in acc under opt",
            vec![
                Bytecode::Ldtrue,
                Bytecode::Definegettersetterbyvalue(Reg(3), Reg(4), Reg(5), Reg(5)),
                Bytecode::Return,
            ],
            vec![],
            "definegettersetterbyvalue",
        ),
        (
            "R3-H3 stownbynamewithnameset",
            vec![
                Bytecode::Lda(Reg(4)),
                Bytecode::Stownbynamewithnameset(Imm(0), EntityId(0), Reg(3)),
                Bytecode::Return,
            ],
            vec![((EntityKind::StringId, 0), EntityRef::string(s_prop))],
            "stownbynamewithnameset",
        ),
        (
            "R3-H3 definefieldbyname",
            vec![
                Bytecode::Lda(Reg(4)),
                Bytecode::Definefieldbyname(Imm(0), EntityId(0), Reg(3)),
                Bytecode::Return,
            ],
            vec![((EntityKind::StringId, 0), EntityRef::string(s_prop))],
            "definefieldbyname",
        ),
        (
            "R3-H3 definepropertybyname",
            vec![
                Bytecode::Lda(Reg(4)),
                Bytecode::Definepropertybyname(Imm(0), EntityId(0), Reg(3)),
                Bytecode::Return,
            ],
            vec![((EntityKind::StringId, 0), EntityRef::string(s_prop))],
            "definepropertybyname",
        ),
        (
            "R3-H3 callruntime.definefieldbyvalue",
            vec![
                Bytecode::Lda(Reg(5)),
                Bytecode::CallruntimeDefinefieldbyvalue(Imm(0), Reg(4), Reg(3)),
                Bytecode::Return,
            ],
            vec![],
            "callruntime.definefieldbyvalue",
        ),
        (
            "R3-H3 callruntime.definefieldbyindex",
            vec![
                Bytecode::Lda(Reg(4)),
                Bytecode::CallruntimeDefinefieldbyindex(Imm(0), Imm(7), Reg(3)),
                Bytecode::Return,
            ],
            vec![],
            "callruntime.definefieldbyindex",
        ),
        (
            "R3-H4 ldsymbol",
            vec![Bytecode::Ldsymbol, Bytecode::Return],
            vec![],
            "ldsymbol",
        ),
        (
            "R3-X2 instanceof + typeof + createregexpwithliteral 2-slot ICs",
            vec![
                Bytecode::Lda(Reg(3)),
                Bytecode::Instanceof(Imm(0), Reg(4)),
                Bytecode::Typeof(Imm(2)),
                Bytecode::Sta(Reg(0)),
                Bytecode::Createregexpwithliteral(Imm(4), EntityId(0), Imm(0)),
                Bytecode::Add2(Imm(6), Reg(0)),
                Bytecode::Return,
            ],
            vec![((EntityKind::StringId, 0), EntityRef::string(s_pat))],
            "createregexpwithliteral",
        ),
    ];

    for (label, bcs, ents, expected_mnem) in cases {
        let file = build_test_file(bcs, ents, Vec::new(), sp.clone(), 3, 6, Vec::new(), None);
        for opt in [false, true] {
            let (_, body) = roundtrip_main(&file, opt);
            let mnems: Vec<&str> = body.bytecodes.iter().map(Bytecode::mnemonic).collect();
            assert!(
                mnems.contains(&expected_mnem),
                "{label} (opt={opt}): expected `{expected_mnem}` in {mnems:?}"
            );
            if label.starts_with("R3-C6") {
                let has_imm0 = body
                    .bytecodes
                    .iter()
                    .any(|bc| matches!(bc, Bytecode::Createobjectwithexcludedkeys(Imm(0), _, _)));
                assert!(
                    has_imm0,
                    "{label} (opt={opt}): expected imm=0 for 1 excluded key, got {:?}",
                    body.bytecodes
                );
            }
            if label.starts_with("R3-H2") && opt {
                let has_ldtrue = body
                    .bytecodes
                    .iter()
                    .any(|bc| matches!(bc, Bytecode::Ldtrue));
                assert!(
                    has_ldtrue,
                    "{label}: `Ldtrue` feeding `definegettersetterbyvalue` must survive `--optimize`!"
                );
            }
        }
    }
}

#[test]
fn r3_x1_raw_jeqz_jnez_semantics_preserved_across_opt() {
    // 1. `ldnull; jeqz target`: in Ark VM `jeqz` ONLY branches on `false` or `±0`,
    //    so `ldnull; jeqz` MUST fall through to `Ldai(11)` (NOT jump to `Ldai(99)`!).
    let file_null = build_test_file(
        vec![
            Bytecode::Ldnull,
            Bytecode::Jeqz(Label(4)),
            Bytecode::Ldai(Imm(11)),
            Bytecode::Return,
            Bytecode::Ldai(Imm(99)),
            Bytecode::Return,
        ],
        vec![],
        vec![],
        StringPool::new(),
        1,
        3,
        vec![],
        None,
    );
    let (_, body_null_opt) = roundtrip_main(&file_null, true);
    assert!(
        body_null_opt
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldai(Imm(11)))),
        "`ldnull; jeqz` must fold to fallthrough `Ldai(11)`, got {:?}",
        body_null_opt.bytecodes
    );
    assert!(
        !body_null_opt
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldai(Imm(99)))),
        "`ldnull; jeqz` must NOT take branch `Ldai(99)`, got {:?}",
        body_null_opt.bytecodes
    );

    // 2. `ldnan; jnez target`: in Ark VM `jnez` branches on `double != 0.0`, which is
    //    TRUE for `NaN`! Must fold to branch target `Ldai(77)` (NOT `Ldai(22)`!).
    let file_nan = build_test_file(
        vec![
            Bytecode::Ldnan,
            Bytecode::Jnez(Label(4)),
            Bytecode::Ldai(Imm(22)),
            Bytecode::Return,
            Bytecode::Ldai(Imm(77)),
            Bytecode::Return,
        ],
        vec![],
        vec![],
        StringPool::new(),
        1,
        3,
        vec![],
        None,
    );
    let (_, body_nan_opt) = roundtrip_main(&file_nan, true);
    assert!(
        body_nan_opt
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldai(Imm(77)))),
        "`ldnan; jnez` must fold to branch target `Ldai(77)`, got {:?}",
        body_nan_opt.bytecodes
    );
    assert!(
        !body_nan_opt
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldai(Imm(22)))),
        "`ldnan; jnez` must NOT fall through to `Ldai(22)`, got {:?}",
        body_nan_opt.bytecodes
    );
}

#[test]
fn r3_x5_out_of_u32_and_neg_zero_prop_idx_never_wraps_to_byindex() {
    // Construct `obj[4294967296.0]` (`2^32`) and `obj[-0.0]` via `Fldai + Ldobjbyvalue`:
    // Lifting turns numeric constant keys into `LoadPropIdx`, and lowering MUST keep
    // `Ldobjbyvalue` (NEVER truncating `4294967296.0 as u32 == 0` into `Ldobjbyindex(0)`!).
    let file = build_test_file(
        vec![
            Bytecode::Fldai(Imm((4_294_967_296.0_f64).to_bits() as i64)),
            Bytecode::Ldobjbyvalue(Imm(0), Reg(3)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Fldai(Imm((-0.0_f64).to_bits() as i64)),
            Bytecode::Ldobjbyvalue(Imm(2), Reg(3)),
            Bytecode::Add2(Imm(4), Reg(0)),
            Bytecode::Return,
        ],
        vec![],
        vec![],
        StringPool::new(),
        2,
        4,
        vec![],
        None,
    );
    for opt in [false, true] {
        let (_, body) = roundtrip_main(&file, opt);
        let has_byindex = body.bytecodes.iter().any(|bc| {
            matches!(
                bc,
                Bytecode::Ldobjbyindex(..) | Bytecode::WideLdobjbyindex(..)
            )
        });
        assert!(
            !has_byindex,
            "opt={opt}: `2^32` and `-0.0` keys must lower via `ldobjbyvalue`, never `*byindex`: {:?}",
            body.bytecodes
        );
    }
}

#[test]
fn r3_h7_h8_h9_wide_isel_debug_rebuild_and_literal_tag_isolation() {
    let mut sp = StringPool::new();
    let s_file = sp.get_or_intern("entry.ts");
    let s_code = sp.get_or_intern("export function f() { return 1; }");
    let s_var = sp.get_or_intern("oldVregLocal");
    let s_t = sp.get_or_intern("any");
    let s_k = sp.get_or_intern("slotKey");

    // Two distinct literal arrays with IDENTICAL numeric values (`0`) under DIFFERENT tags
    // (`Integer(0)` vs `Accessor(0)`), plus `Method(1)` vs `Getter(1)`.
    let la_int = LiteralArray::new(vec![
        LiteralValue::String(s_k),
        LiteralValue::Integer(0),
        LiteralValue::Method(MethodIdx(1)),
    ]);
    let la_acc = LiteralArray::new(vec![
        LiteralValue::String(s_k),
        LiteralValue::Accessor(0),
        LiteralValue::Getter(MethodIdx(1)),
    ]);

    let debug = MethodDebugInfo {
        source_file: Some(s_file),
        source_code: Some(s_code),
        line_table: vec![
            LineEntry { index: 0, line: 10 },
            LineEntry { index: 4, line: 20 },
        ],
        column_table: vec![ColumnEntry {
            index: 0,
            column: 4,
        }],
        local_vars: vec![LocalVarInfo {
            name: s_var,
            type_name: s_t,
            type_signature: s_t,
            reg_number: 0,
            start: 0,
            end: 6,
        }],
        params: Vec::new(),
    };

    let file = build_test_file(
        vec![
            Bytecode::WideNewlexenv(Imm(300)),
            Bytecode::Lda(Reg(3)),
            Bytecode::WideStlexvar(Imm(0), Imm(299)),
            Bytecode::WideLdlexvar(Imm(0), Imm(299)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Createarraywithbuffer(Imm(0), EntityId(0)),
            Bytecode::Sta(Reg(1)),
            Bytecode::Createobjectwithbuffer(Imm(1), EntityId(1)),
            Bytecode::Add2(Imm(2), Reg(1)),
            Bytecode::Add2(Imm(3), Reg(0)),
            Bytecode::WideLdobjbyindex(Imm(70_000)),
            Bytecode::Return,
        ],
        vec![
            (
                (EntityKind::LiteralarrayId, 0),
                EntityRef::LiteralArray(LiteralArrayIdx(0)),
            ),
            (
                (EntityKind::LiteralarrayId, 1),
                EntityRef::LiteralArray(LiteralArrayIdx(1)),
            ),
        ],
        vec![la_int.clone(), la_acc.clone()],
        sp,
        3,
        4,
        vec![],
        Some(debug),
    );

    let (redecoded, body) = roundtrip_main(&file, true);
    let mnems: Vec<&str> = body.bytecodes.iter().map(Bytecode::mnemonic).collect();
    assert!(mnems.contains(&"wide.newlexenv"), "{mnems:?}");
    assert!(mnems.contains(&"wide.stlexvar"), "{mnems:?}");
    assert!(mnems.contains(&"wide.ldlexvar"), "{mnems:?}");
    assert!(mnems.contains(&"wide.ldobjbyindex"), "{mnems:?}");

    // Verify `R3-H8`: debug `line_table` offsets are strictly in-bounds and stale `local_vars` cleared!
    let (_, m0) = redecoded
        .all_methods()
        .find(|(_, m)| redecoded.strings.resolve(m.name) == Some("func_main_0"))
        .unwrap();
    let dbg = m0.debug.as_ref().expect("reconstructed MethodDebugInfo");
    assert!(
        dbg.local_vars.is_empty(),
        "stale vreg local_vars must be cleared on rewrite: {:?}",
        dbg.local_vars
    );
    assert!(
        !dbg.line_table.is_empty(),
        "line_table must be reconstructed"
    );
    for le in &dbg.line_table {
        assert!(
            (le.index as usize) < body.bytecodes.len(),
            "line_table index {} >= bytecode count {}",
            le.index,
            body.bytecodes.len()
        );
    }

    // Verify `R3-H9`: `Integer(0)` + `Method` vs `Accessor(0)` + `Getter` stayed distinct!
    let mut lit_refs = Vec::new();
    for (&(kind, _), &er) in &body.entities {
        if kind == EntityKind::LiteralarrayId
            && let EntityRef::LiteralArray(idx) = er
        {
            lit_refs.push(idx);
        }
    }
    lit_refs.sort_unstable();
    lit_refs.dedup();
    assert_eq!(
        lit_refs.len(),
        2,
        "differently tagged literal arrays must NOT deduplicate into 1: {lit_refs:?}"
    );
}

#[test]
fn r3_x3_competing_nested_catch_handler_phis_do_not_clobber() {
    // Protected block [2..5) is covered by BOTH inner handler [5..7) and outer handler [7..9),
    // and both handlers merge `v0` / `v1` from entry + protected block via handler phis!
    let mut sp = StringPool::new();
    let err_a = sp.get_or_intern("LTypeError;");
    let mut file = build_test_file(
        vec![
            Bytecode::Mov(Reg(0), Reg(3)), // [0] entry: v0 = a0
            Bytecode::Mov(Reg(1), Reg(4)), // [1] entry: v1 = a1
            Bytecode::Mov(Reg(0), Reg(4)), // [2] protected: v0 = a1
            Bytecode::Mov(Reg(1), Reg(5)), // [3] protected: v1 = a2
            Bytecode::Callarg0(Imm(0)),    // [4] may_throw!
            Bytecode::Lda(Reg(0)),         // [5] H1 (typed catch): uses v0 phi!
            Bytecode::Return,              // [6]
            Bytecode::Lda(Reg(1)),         // [7] H2 (catch-all): uses v1 phi!
            Bytecode::Return,              // [8]
        ],
        vec![],
        vec![],
        sp,
        2,
        6,
        vec![TryBlock {
            start: 2,
            len: 3,
            catches: vec![
                CatchBlock {
                    type_class: Some(err_a),
                    handler: 5,
                    len: 2,
                },
                CatchBlock {
                    type_class: None,
                    handler: 7,
                    len: 2,
                },
            ],
        }],
        None,
    );
    // Add external `LTypeError;` class so `.catch LTypeError;` encodes cleanly.
    file.classes.insert(
        err_a,
        Class {
            descriptor: err_a,
            name: err_a,
            access_flags: AccessFlags::PUBLIC,
            source_lang: SourceLang::EcmaScript,
            source_file: None,
            is_external: true,
            super_class: None,
            interfaces: Vec::new(),
            methods: Vec::new(),
            fields: Vec::new(),
            annotations: Default::default(),
        },
    );

    let (_, body) = roundtrip_main(&file, false);
    assert_eq!(body.try_blocks.len(), 1);
    assert_eq!(body.try_blocks[0].catches.len(), 2);
    let c0 = body.try_blocks[0].catches[0];
    let c1 = body.try_blocks[0].catches[1];
    assert!(
        c0.type_class.is_some(),
        "typed catch must preserve type_class"
    );
    assert!(c1.type_class.is_none(), "catch-all must keep None");

    // Extract the `Lda(reg)` read by H1 and H2: they MUST read distinct registers!
    let h1_lda = body.bytecodes[c0.handler as usize..(c0.handler + c0.len) as usize]
        .iter()
        .find_map(|bc| match bc {
            Bytecode::Lda(r) => Some(*r),
            _ => None,
        })
        .expect("H1 Lda");
    let h2_lda = body.bytecodes[c1.handler as usize..(c1.handler + c1.len) as usize]
        .iter()
        .find_map(|bc| match bc {
            Bytecode::Lda(r) => Some(*r),
            _ => None,
        })
        .expect("H2 Lda");
    assert_ne!(
        h1_lda, h2_lda,
        "competing handler phis H1 ({h1_lda:?}) and H2 ({h2_lda:?}) must NEVER share a register!"
    );
}

#[test]
fn r3_definefieldbyvalue_preserves_key_obj_operand_order() {
    let mut sp = StringPool::new();
    let val_sid = sp.get_or_intern("a\\nb");
    let file = build_test_file(
        vec![
            Bytecode::Createemptyarray(Imm(0)),
            Bytecode::Sta(Reg(0)),         // v0 = array object
            Bytecode::Mov(Reg(1), Reg(4)), // v1 = a2 (dynamic key param 2)
            Bytecode::LdaStr(EntityId(0)),
            Bytecode::CallruntimeDefinefieldbyvalue(Imm(1), Reg(1), Reg(0)),
            Bytecode::Lda(Reg(0)),
            Bytecode::Return,
        ],
        vec![((EntityKind::StringId, 0), EntityRef::string(val_sid))],
        vec![],
        sp,
        2,
        3,
        vec![],
        None,
    );

    for opt in [false, true] {
        let (redecoded, body) = roundtrip_main(&file, opt);
        assert!(
            body.bytecodes
                .iter()
                .any(|bc| matches!(bc, Bytecode::CallruntimeDefinefieldbyvalue(..))),
            "opt={opt}: expected CallruntimeDefinefieldbyvalue in {:?}",
            body.bytecodes
        );
        let relifted = lift_file(&redecoded).expect("re-lift");
        let f0 = relifted
            .functions
            .iter()
            .find(|f| relifted.sym.as_str(f.name) == Some("func_main_0"))
            .expect("func_main_0 in relifted");
        let mut saw_store = false;
        for &bb in &f0.blocks {
            for &iid in &relifted.blocks[bb.index()].insts {
                if let abcd_ir::Op::StoreOwnPropDyn {
                    object,
                    key,
                    kind: abcd_ir::OwnStoreKind::ClassField,
                    ..
                } = &relifted.insts[iid.index()].op
                {
                    saw_store = true;
                    let abcd_ir::ValueDef::Inst(obj_def) = relifted.values[object.index()].def
                    else {
                        panic!("opt={opt}: expected object to come from AllocArray");
                    };
                    assert!(
                        matches!(
                            relifted.insts[obj_def.index()].op,
                            abcd_ir::Op::AllocArray { .. }
                        ),
                        "opt={opt}: object must remain AllocArray (not swapped with key): {:?}",
                        relifted.insts[obj_def.index()].op
                    );
                    assert!(
                        matches!(
                            relifted.values[key.index()].def,
                            abcd_ir::ValueDef::Param(2)
                        ),
                        "opt={opt}: key must remain Param(2), got {:?}",
                        relifted.values[key.index()].def
                    );
                }
            }
        }
        assert!(saw_store, "opt={opt}: expected re-lifted StoreOwnPropDyn");
    }
}

#[test]
fn r3_supercallthisrange_suppresses_ldfunction_in_v2lift_and_v2opt() {
    let file = build_test_file(
        vec![
            Bytecode::Lda(Reg(5)),                                // [0] a3 (cond)
            Bytecode::Jeqz(Label(6)),                             // [1] if falsy -> else
            Bytecode::Ldai(Imm(1)),                               // [2] then: arg = 1
            Bytecode::Sta(Reg(0)),                                // [3]
            Bytecode::Supercallthisrange(Imm(0), Imm(1), Reg(0)), // [4]
            Bytecode::Return,                                     // [5]
            Bytecode::Ldai(Imm(2)),                               // [6] else: arg = 2
            Bytecode::Sta(Reg(0)),                                // [7]
            Bytecode::Supercallthisrange(Imm(2), Imm(1), Reg(0)), // [8]
            Bytecode::Return,                                     // [9]
        ],
        vec![],
        vec![],
        StringPool::new(),
        2,
        4,
        vec![],
        None,
    );

    for opt in [false, true] {
        let (_, body) = roundtrip_main(&file, opt);
        assert!(
            !body
                .bytecodes
                .iter()
                .any(|bc| matches!(bc, Bytecode::Ldfunction)),
            "opt={opt}: Supercallthisrange must NEVER emit Bytecode::Ldfunction: {:?}",
            body.bytecodes
        );
        let super_calls = body
            .bytecodes
            .iter()
            .filter(|bc| matches!(bc, Bytecode::Supercallthisrange(..)))
            .count();
        assert_eq!(super_calls, 2, "opt={opt}: expected 2 Supercallthisrange");
    }
}
