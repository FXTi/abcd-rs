//! End-to-end multi-module `--merge-abc` regression and VM-oracle suite (#28).
//!
//! Covers all four `--merge-abc` metadata channels (`moduleRecordIdx`,
//! `moduleRequestPhaseIdx`, `scopeNames`, and `jsonFileContent`) across all
//! four tool pipelines:
//!
//! 1. `abcd_file::decode → encode` container round-trip;
//! 2. `abcd_file::pandasm::{emit_file, parse_file_with_version} → encode`
//!    disassembly/assembly round-trip;
//! 3. `abcd_lift::lift_file → verify_module → [abcd_opt::optimize_module] →
//!    abcd_lower::{lower_function_with_options, to_method_body} → encode`
//!    full SSA rewrite (both `v2lift` and `v2opt`);
//! 4. `abcd_decompile::emit::decompile_module` JS emission & syntax check.
//!
//! Part 1 (`synthetic_merge_abc_*`) runs unconditionally on every OS/arch lane
//! in `cargo test` with zero external tools.
//! Part 2 (`merge_abc_docker_oracle`) is `#[ignore]`d by default and gated in
//! CI (`lift-lower`), compiling real multi-file ESM + `import lazy` + closure +
//! `.json` inputs via `es2abc --module --merge-abc` across `12.0.6.0`,
//! `13.0.1.0`, and `24.0.0.0`, and verifying every rewritten artifact in
//! `ark_disasm` and `ark_js_vm --entry-point=main`.

use std::process::Command;

use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_decompile::split::{SplitFileKind, decompile_module_split};
use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationValue, Builder, CatchBlock, FieldValue,
    File, FunctionKind as FileFunctionKind, JSON_FILE_CONTENT_FIELD, LiteralArray, LiteralArrayIdx,
    LiteralValue, MODULE_RECORD_IDX_FIELD, MODULE_REQUEST_PHASE_FIELD, Method, MethodBody,
    ModuleRecordDef, SCOPE_NAMES_FIELD, SourceLang, TryBlock, Type, Version, decode, encode,
    pandasm,
};
use abcd_ir::{Op, verify_module};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Label, Reg, encode as encode_isa, insn};
use abcd_lift::lift_file;
use abcd_lower::{LowerOptions, lower_module_bodies};
use abcd_opt::optimize_module;

/// Supported `--merge-abc` versions (12.0.6.0 header literal table, 13.0.1.0
/// and 24.0.0.0 index/field-referenced literal collection).
const MERGE_VERSIONS: [Version; 3] = [
    Version::new(12, 0, 6, 0),
    Version::new(13, 0, 1, 0),
    Version::new(24, 0, 0, 0),
];

/// Build a multi-record `--merge-abc` `.abc` buffer at `version` exercising:
/// - `Lmain;`: `moduleRecordIdx` (2 requests: `./helper`, `./lazyMod`),
///   `moduleRequestPhaseIdx` (`[0, 1]`), `scopeNames` (`["mainScope"]`), and a
///   foldable `func_main_0` body (`20 + 22` → `42`, `num_args = 3`);
/// - `Lhelper;`: `moduleRecordIdx` (1 request: `./cfg`), `scopeNames`
///   (`["capturedSeed", "innerStep"]`), `func_main_0` + `makeAdder`;
/// - `Lcfg;`: `jsonFileContent` (`"{\"base\":20,\"tag\":\"merge-ok\"}"`).
fn build_synthetic_merge_abc(version: Version) -> Vec<u8> {
    let mut b = Builder::new();
    b.set_file_version(version)
        .expect("supported merge-abc version");

    // --- Record 1: Lmain; ---
    let cls_main = b.add_class("Lmain;");
    b.class_set_source_lang(cls_main, SourceLang::EcmaScript);
    let main_mod_field = b.class_add_field(
        cls_main,
        MODULE_RECORD_IDX_FIELD,
        Type::U32,
        AccessFlags::PUBLIC,
    );
    let main_phase_field = b.class_add_field(
        cls_main,
        MODULE_REQUEST_PHASE_FIELD,
        Type::U32,
        AccessFlags::PUBLIC,
    );
    let main_scope_field =
        b.class_add_field(cls_main, SCOPE_NAMES_FIELD, Type::U32, AccessFlags::PUBLIC);

    let req_helper = b.add_string("./helper");
    let req_lazy = b.add_string("./lazyMod");
    let main_mod_la = b.add_literal_array("Lmain_mod");
    let main_records = vec![
        ModuleRecordDef::RegularImport {
            local_name: b.add_string("makeAdder"),
            import_name: b.add_string("makeAdder"),
            module_request_idx: 0,
        },
        ModuleRecordDef::RegularImport {
            local_name: b.add_string("bonus"),
            import_name: b.add_string("bonus"),
            module_request_idx: 1,
        },
        ModuleRecordDef::LocalExport {
            local_name: b.add_string("result"),
            export_name: b.add_string("result"),
        },
    ];
    b.literal_array_add_module_data(main_mod_la, &[req_helper, req_lazy], &main_records)
        .expect("stage Lmain moduleRecordIdx");
    b.field_set_value_literalarray(main_mod_field, main_mod_la)
        .expect("wire Lmain moduleRecordIdx");

    let main_phase_la = b.add_literal_array("Lmain_phase");
    b.literal_array_add_module_request_phase(main_phase_la, &[0, 1])
        .expect("stage Lmain moduleRequestPhaseIdx");
    b.field_set_value_literalarray(main_phase_field, main_phase_la)
        .expect("wire Lmain moduleRequestPhaseIdx");

    let main_scope_la = b.add_literal_array("Lmain_scope");
    let s_main_scope = b.add_string("mainScope");
    b.literal_array_add_string(main_scope_la, s_main_scope);
    b.field_set_value_literalarray(main_scope_field, main_scope_la)
        .expect("wire Lmain scopeNames");

    let proto = b.create_proto(Type::Tagged, &[]);
    // Foldable `20 + 22` body with the 3 implicit es2abc frame args (`0xF`).
    let (main_code, _) = encode_isa(&[
        insn::Ldai::new(Imm(20)),
        insn::Sta::new(Reg(0)),
        insn::Ldai::new(Imm(22)),
        insn::Add2::new(Imm(0), Reg(0)),
        Bytecode::Return,
    ])
    .expect("encode main_code");
    let m_main = b.class_add_method(
        cls_main,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &main_code,
        2,
        3,
    );
    b.method_set_source_lang(m_main, SourceLang::EcmaScript);

    // --- Record 2: Lhelper; ---
    let cls_helper = b.add_class("Lhelper;");
    b.class_set_source_lang(cls_helper, SourceLang::EcmaScript);
    let helper_mod_field = b.class_add_field(
        cls_helper,
        MODULE_RECORD_IDX_FIELD,
        Type::U32,
        AccessFlags::PUBLIC,
    );
    let helper_scope_field = b.class_add_field(
        cls_helper,
        SCOPE_NAMES_FIELD,
        Type::U32,
        AccessFlags::PUBLIC,
    );

    let req_cfg = b.add_string("./cfg");
    let helper_mod_la = b.add_literal_array("Lhelper_mod");
    let helper_records = vec![
        ModuleRecordDef::RegularImport {
            local_name: b.add_string("cfg"),
            import_name: b.add_string("default"),
            module_request_idx: 0,
        },
        ModuleRecordDef::LocalExport {
            local_name: b.add_string("makeAdder"),
            export_name: b.add_string("makeAdder"),
        },
    ];
    b.literal_array_add_module_data(helper_mod_la, &[req_cfg], &helper_records)
        .expect("stage Lhelper moduleRecordIdx");
    b.field_set_value_literalarray(helper_mod_field, helper_mod_la)
        .expect("wire Lhelper moduleRecordIdx");

    let helper_scope_la = b.add_literal_array("Lhelper_scope");
    let s_seed = b.add_string("capturedSeed");
    let s_step = b.add_string("innerStep");
    b.literal_array_add_string(helper_scope_la, s_seed);
    b.literal_array_add_string(helper_scope_la, s_step);
    b.field_set_value_literalarray(helper_scope_field, helper_scope_la)
        .expect("wire Lhelper scopeNames");

    // Exercise external import slot 0 (`ldexternalmodulevar`), lazy import
    // slot 1 (`callruntime.ldlazymodulevar`), local export store (`stmodulevar`),
    // and local export load (`ldlocalmodulevar`) so `lift → lower` proves all
    // three module-var load flavors survive without collapsing to `ldlocalmodulevar`.
    let (helper_main_code, _) = encode_isa(&[
        insn::Ldexternalmodulevar::new(Imm(0)),
        insn::Sta::new(Reg(0)),
        insn::CallruntimeLdlazymodulevar::new(Imm(1)),
        insn::Add2::new(Imm(0), Reg(0)),
        insn::Stmodulevar::new(Imm(0)),
        insn::Ldlocalmodulevar::new(Imm(0)),
        Bytecode::Return,
    ])
    .expect("encode helper");
    let m_helper_main = b.class_add_method(
        cls_helper,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &helper_main_code,
        2,
        3,
    );
    b.method_set_source_lang(m_helper_main, SourceLang::EcmaScript);

    let (adder_code, _) =
        encode_isa(&[insn::Ldai::new(Imm(10)), Bytecode::Return]).expect("encode adder");
    let m_adder = b.class_add_method(
        cls_helper,
        "makeAdder",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &adder_code,
        1,
        4,
    );
    b.method_set_source_lang(m_adder, SourceLang::EcmaScript);

    // --- Record 3: Lcfg; (JSON module) ---
    let cls_cfg = b.add_class("Lcfg;");
    b.class_set_source_lang(cls_cfg, SourceLang::EcmaScript);
    let json_field = b.class_add_field(
        cls_cfg,
        JSON_FILE_CONTENT_FIELD,
        Type::U32,
        AccessFlags::PUBLIC,
    );
    let json_payload = b.add_string("{\"base\":20,\"tag\":\"merge-ok\"}");
    b.field_set_value_string(json_field, json_payload)
        .expect("wire Lcfg jsonFileContent");

    b.finalize().expect("finalize synthetic merge-abc")
}

fn assert_merge_abc_invariants(file: &File, expect_json: bool, from_pandasm: bool) {
    assert_eq!(
        file.literal_arrays.len(),
        2,
        "only the two tagged scopeNames arrays belong in File::literal_arrays"
    );

    let main_cls = file.class_by_str("Lmain;").expect("Lmain;");
    let main_mod = main_cls
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some(MODULE_RECORD_IDX_FIELD))
        .expect("Lmain.moduleRecordIdx");
    let Some(FieldValue::ModuleData(md_main)) = &main_mod.initial_value else {
        panic!("expected ModuleData on Lmain;");
    };
    assert_eq!(md_main.requests.len(), 2);
    assert_eq!(md_main.records.len(), 3);

    let main_phase = main_cls
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some(MODULE_REQUEST_PHASE_FIELD))
        .expect("Lmain.moduleRequestPhaseIdx");
    let Some(FieldValue::ModuleRequestPhase(ph)) = &main_phase.initial_value else {
        panic!("expected ModuleRequestPhase on Lmain;");
    };
    if from_pandasm {
        // Upstream `ark_disasm` excludes untagged phase blobs from `# LITERALS`,
        // so `.pa` text preserves the sibling request count (`2`), not the raw flags.
        assert_eq!(ph.flags.len(), 2);
    } else {
        assert_eq!(ph.flags, vec![0, 1]);
    }

    let helper_cls = file.class_by_str("Lhelper;").expect("Lhelper;");
    let helper_mod = helper_cls
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some(MODULE_RECORD_IDX_FIELD))
        .expect("Lhelper.moduleRecordIdx");
    let Some(FieldValue::ModuleData(md_helper)) = &helper_mod.initial_value else {
        panic!("expected ModuleData on Lhelper;");
    };
    assert_eq!(md_helper.requests.len(), 1);
    assert_eq!(file.strings.resolve(md_helper.requests[0]), Some("./cfg"));

    if expect_json {
        let cfg_cls = file.class_by_str("Lcfg;").expect("Lcfg;");
        let json_f = cfg_cls
            .fields
            .iter()
            .find(|f| file.strings.resolve(f.name) == Some(JSON_FILE_CONTENT_FIELD))
            .expect("Lcfg.jsonFileContent");
        let Some(FieldValue::JsonFileContent { content, .. }) = json_f.initial_value else {
            panic!("expected JsonFileContent on Lcfg;");
        };
        assert_eq!(
            file.strings.resolve(content),
            Some("{\"base\":20,\"tag\":\"merge-ok\"}")
        );
    }
}

fn assert_helper_module_var_opcodes(file: &File) {
    let helper_cls = file.class_by_str("Lhelper;").expect("Lhelper;");
    let helper_main = helper_cls
        .methods
        .iter()
        .find(|m| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("Lhelper::func_main_0");
    let bcs = helper_main.body.as_ref().expect("helper body").bytecodes();
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::Ldexternalmodulevar(Imm(0)))),
        "Ldexternalmodulevar(0) must survive lift → lower: {bcs:?}"
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::CallruntimeLdlazymodulevar(Imm(1)))),
        "CallruntimeLdlazymodulevar(1) must survive lift → lower: {bcs:?}"
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::Stmodulevar(Imm(0)))),
        "Stmodulevar(0) must survive lift → lower: {bcs:?}"
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::Ldlocalmodulevar(Imm(0)))),
        "Ldlocalmodulevar(0) must survive lift → lower: {bcs:?}"
    );
}

/// Rewrite every method body of `file` through `lift → verify → [opt → verify] → lower → encode`.
fn rewrite_file_e2e(bytes: &[u8], optimize: bool) -> (Vec<u8>, bool) {
    let file = decode(bytes).expect("decode for rewrite");
    let mut module = lift_file(&file).expect("lift merge-abc");
    let report = verify_module(&module);
    assert!(
        report.is_ok(),
        "pre-opt IR verify failed: {:?}",
        report.errors
    );

    let changed = optimize && optimize_module(&mut module);
    if optimize {
        let post = verify_module(&module);
        assert!(post.is_ok(), "post-opt IR verify failed: {:?}", post.errors);
    }

    let bodies =
        lower_module_bodies(&module, &file, LowerOptions::default()).expect("lower_module_bodies");

    let mut rebuilt = file.clone();
    let mut cursor = bodies.into_iter();
    let mut bc_errs = Vec::new();
    let mut method_idx = 0usize;
    for class in rebuilt.classes.values_mut() {
        let cls_name = file
            .strings
            .resolve(class.descriptor)
            .unwrap_or("?")
            .to_string();
        for method in &mut class.methods {
            let slot = cursor.next().expect("method cursor");
            if method.body.is_some() {
                let b = slot.expect("lowered body");
                let bcs = b.bytecodes();
                if let Err(e) = encode_isa(&bcs) {
                    let m_name = file.strings.resolve(method.name).unwrap_or("?");
                    let mut bad_insns = Vec::new();
                    for (i, bc) in bcs.iter().enumerate() {
                        if !matches!(bc, Bytecode::Jmp(_) | Bytecode::Jeqz(_) | Bytecode::Jnez(_))
                            && encode_isa(std::slice::from_ref(bc)).is_err()
                        {
                            bad_insns.push(format!("[{i}] {bc:?}"));
                        }
                    }
                    bc_errs.push(format!(
                        "FuncId({method_idx}) {cls_name}::{m_name} (len={}, vregs={}, args={}): {e}; bad_nonbranch={bad_insns:?}",
                        bcs.len(),
                        b.num_vregs,
                        b.num_args
                    ));
                }
                drop(bcs);
                method.body = Some(b);
            }
            method_idx += 1;
        }
    }
    assert!(cursor.next().is_none());
    assert!(
        bc_errs.is_empty(),
        "bytecode encode failed on {} methods (optimize={optimize}):\n{}",
        bc_errs.len(),
        bc_errs.join("\n")
    );

    let encoded = encode(&rebuilt).expect("encode rewritten merge-abc");
    (encoded, changed)
}

#[test]
fn synthetic_merge_abc_all_four_pipelines_across_versions() {
    let has_node = Command::new("node").arg("--version").output().is_ok();

    for version in MERGE_VERSIONS {
        let raw = build_synthetic_merge_abc(version);

        // 1) Container decode → encode → re-decode
        let file1 = decode(&raw).expect("decode synthetic merge-abc");
        assert_eq!(file1.version, version);
        assert_merge_abc_invariants(&file1, true, false);
        let reencoded = encode(&file1).expect("encode synthetic merge-abc");
        let file2 = decode(&reencoded).expect("re-decode synthetic merge-abc");
        assert_merge_abc_invariants(&file2, true, false);

        // 2) Pandasm emit → parse → encode → decode
        let mut file_no_json = file1.clone();
        let cfg_sid = file_no_json.strings.get("Lcfg;").expect("Lcfg; sid");
        file_no_json.classes.remove(&cfg_sid);
        let bytes_no_json = encode(&file_no_json).expect("encode no-json");
        let decoded_no_json = decode(&bytes_no_json).expect("decode no-json");
        let pa = pandasm::emit_file(&decoded_no_json, "merged.abc");
        let parsed =
            pandasm::parse_file_with_version(&pa, version).expect("parse merge-abc pandasm");
        let pa_reencoded = encode(&parsed).expect("encode parsed pandasm");
        let pa_decoded = decode(&pa_reencoded).expect("decode pandasm-encoded");
        assert_merge_abc_invariants(&pa_decoded, false, true);

        // 3) Lift + IR metadata verification + v2lift & v2opt rewrite
        let ir = lift_file(&file1).expect("lift merge-abc");
        assert!(verify_module(&ir).is_ok());
        let main_ir = ir
            .classes
            .iter()
            .find(|c| ir.sym.resolve(c.descriptor) == Some("Lmain;"))
            .expect("IR Lmain;");
        let es_main = main_ir.es_module.as_ref().expect("Lmain.es_module");
        assert_eq!(es_main.module_requests.len(), 2);
        assert!(!es_main.module_requests[0].lazy);
        assert!(es_main.module_requests[1].lazy);
        assert!(main_ir.scope_names.is_some(), "Lmain.scope_names");

        let (rewritten_lift, _) = rewrite_file_e2e(&raw, false);
        let decoded_lift = decode(&rewritten_lift).expect("decode v2lift merge-abc");
        assert_merge_abc_invariants(&decoded_lift, true, false);
        assert_helper_module_var_opcodes(&decoded_lift);

        let (rewritten_opt, opt_changed) = rewrite_file_e2e(&raw, true);
        assert!(
            opt_changed,
            "20 + 22 in Lmain::func_main_0 must constant-fold"
        );
        let decoded_opt = decode(&rewritten_opt).expect("decode v2opt merge-abc");
        assert_merge_abc_invariants(&decoded_opt, true, false);
        assert_helper_module_var_opcodes(&decoded_opt);

        // 4) Decompile determinism, zero fallbacks, and Node syntax check
        let d1 = decompile_module(&ir, &EmitOptions::default());
        let d2 = decompile_module(&ir, &EmitOptions::default());
        assert_eq!(d1.text, d2.text, "non-deterministic merge-abc decompile");
        assert_eq!(
            d1.stats.functions_with_fallbacks, 0,
            "unexpected fallbacks on merge-abc decompile: {:?}",
            d1.stats.fallback_comments
        );
        if has_node {
            let tmp = std::env::temp_dir().join(format!(
                "abcd-merge-decompile-{}-{}.{}.{}.{}.mjs",
                std::process::id(),
                version.major(),
                version.minor(),
                version.patch(),
                version.build()
            ));
            std::fs::write(&tmp, &d1.text).expect("write temp mjs");
            let check = Command::new("node")
                .arg("--check")
                .arg(&tmp)
                .output()
                .expect("run node --check");
            let _ = std::fs::remove_file(&tmp);
            assert!(
                check.status.success(),
                "node --check rejected decompiled merge-abc ({version}):\n{}\n{}",
                String::from_utf8_lossy(&check.stderr),
                d1.text
            );
        }

        // 5) Multi-file `--split-modules` tree reconstruction (#26 Phase 2)
        let split = decompile_module_split(&ir, &EmitOptions::default());
        assert_eq!(
            split.files.len(),
            3,
            "expected main.js, helper.js, cfg.json"
        );
        let main_sf = split
            .files
            .iter()
            .find(|f| f.rel_path == "main.js")
            .expect("main.js");
        assert!(
            main_sf
                .text
                .contains("import { makeAdder } from \"./helper\";")
        );
        assert!(
            main_sf
                .text
                .contains("import { bonus } from \"./lazyMod\";")
        );
        assert!(main_sf.text.contains("export { result };"));

        let helper_sf = split
            .files
            .iter()
            .find(|f| f.rel_path == "helper.js")
            .expect("helper.js");
        assert!(
            helper_sf.text.contains("import cfg from \"./cfg.json\";"),
            "helper.js must rewrite extensionless JSON import:\n{}",
            helper_sf.text
        );
        assert!(helper_sf.text.contains("export { makeAdder };"));

        let cfg_sf = split
            .files
            .iter()
            .find(|f| f.rel_path == "cfg.json")
            .expect("cfg.json");
        assert_eq!(cfg_sf.kind, SplitFileKind::Json);
        assert_eq!(cfg_sf.text, "{\"base\":20,\"tag\":\"merge-ok\"}\n");

        if has_node {
            for sf in &split.files {
                if sf.kind == SplitFileKind::Json {
                    continue;
                }
                let tmp = std::env::temp_dir().join(format!(
                    "abcd-merge-split-{}-{}-{}",
                    std::process::id(),
                    version,
                    sf.rel_path.replace('/', "_")
                ));
                std::fs::write(&tmp, &sf.text).expect("write split mjs");
                // Copy with `.mjs` suffix so `node --check` parses ESM syntax.
                let mjs = tmp.with_extension("mjs");
                std::fs::rename(&tmp, &mjs).expect("rename to mjs");
                let check = Command::new("node")
                    .arg("--check")
                    .arg(&mjs)
                    .output()
                    .expect("run node --check on split file");
                let _ = std::fs::remove_file(&mjs);
                assert!(
                    check.status.success(),
                    "node --check rejected split {} ({version}):\n{}\n{}",
                    sf.rel_path,
                    String::from_utf8_lossy(&check.stderr),
                    sf.text
                );
            }
        }
    }
}

/// Full upstream black-box oracle (`es2abc --module --merge-abc`, `ark_disasm`,
/// and `ark_js_vm --entry-point=main`) inside a single `$ARK_TEST_IMAGE`
/// container across `12.0.6.0`, `13.0.1.0`, and `24.0.0.0`.
#[test]
#[ignore = "requires docker and ARK_TEST_IMAGE (gated in CI lift-lower)"]
fn merge_abc_docker_oracle() {
    let image = std::env::var("ARK_TEST_IMAGE")
        .unwrap_or_else(|_| "ghcr.io/fxti/arkcompiler-test:latest".to_string());
    let work = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("merge-abc-oracle");
    if work.exists() {
        std::fs::remove_dir_all(&work).expect("clean merge-abc-oracle");
    }
    let src = work.join("src");
    std::fs::create_dir_all(&src).expect("create merge-abc-oracle/src");

    std::fs::write(src.join("cfg.json"), "{\"base\":20,\"tag\":\"merge-ok\"}\n").expect("cfg.json");
    std::fs::write(
        src.join("helper.js"),
        "export function makeAdder(seed) {\n\
           const step = 2;\n\
           return (x) => x + seed + step;\n\
         }\n\
         export function sumDown(n) {\n\
           let acc = 0;\n\
           while (n > 0) {\n\
             acc += n;\n\
             n = n - 1;\n\
           }\n\
           return acc;\n\
         }\n\
         export function pickEq(a, b) {\n\
           if (a === b) {\n\
             return a + b;\n\
           }\n\
           return a - b;\n\
         }\n",
    )
    .expect("helper.js");
    std::fs::write(src.join("lazyMod.js"), "export const bonus = 10;\n").expect("lazyMod.js");
    std::fs::write(
        src.join("main.js"),
        "import cfg from \"./cfg.json\";\n\
         import { makeAdder, sumDown, pickEq } from \"./helper\";\n\
         import lazy { bonus } from \"./lazyMod\";\n\
         const add = makeAdder(cfg.base);\n\
         const guard = (sumDown(3) - 6) + (pickEq(5, 5) - 10);\n\
         print(cfg.tag + \":\" + (add(10) + bonus + guard));\n",
    )
    .expect("main.js");
    std::fs::write(
        work.join("filesInfo.txt"),
        "/work/src/cfg.json;cfg;esm;cfg.json;entry\n\
         /work/src/helper.js;helper;esm;helper.js;entry\n\
         /work/src/lazyMod.js;lazyMod;esm;lazyMod.js;entry\n\
         /work/src/main.js;main;esm;main.js;entry\n",
    )
    .expect("filesInfo.txt");

    // Step 1: Compile `orig-<ver>.abc` + `orig-<ver>.pa` + baseline VM run for
    // all 3 versions inside ONE container invocation.
    let compile_py = r#"
import json, subprocess, sys
sys.path.insert(0, "/opt/arkcompiler-test")
import arktest

versions = arktest.read_json(arktest.ROOT / "versions.json")
out = {}
for ver in ["12.0.6.0", "13.0.1.0", "24.0.0.0"]:
    abc = f"/work/orig-{ver}.abc"
    pa = f"/work/orig-{ver}.pa"
    c = arktest.call("es2abc", versions[ver] + [
        "--module", "--merge-abc", f"--output={abc}", "@/work/filesInfo.txt"
    ])
    arktest.require_ok(c)
    d = arktest.call("ark_disasm", [abc, pa])
    arktest.require_ok(d)
    r = arktest.call("ark_js_vm", ["--entry-point=main", abc])
    arktest.require_ok(r)
    out[ver] = r["stdout"]
print(json.dumps(out))
"#;
    let compile_out = Command::new("docker")
        .args([
            "run",
            "--rm",
            "--platform",
            "linux/amd64",
            "--network",
            "none",
            "--ulimit",
            "stack=8388608:8388608",
            "-v",
            &format!("{}:/work", work.display()),
            "--entrypoint",
            "python3",
            &image,
            "-c",
            compile_py,
        ])
        .output()
        .expect("run docker es2abc --merge-abc");
    assert!(
        compile_out.status.success(),
        "docker merge-abc compile failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&compile_out.stdout),
        String::from_utf8_lossy(&compile_out.stderr)
    );
    let baseline: serde_json::Value =
        serde_json::from_slice(&compile_out.stdout).expect("baseline json");
    for ver in ["12.0.6.0", "13.0.1.0", "24.0.0.0"] {
        assert_eq!(baseline[ver].as_str(), Some("merge-ok:42\n"));
    }

    // Step 2: Run all 4 abcd-rs pipelines per version on the host and stage
    // candidate .abc files (`id`, `v2lift`, `v2opt`) for VM verification.
    let has_node = Command::new("node").arg("--version").output().is_ok();
    for ver in MERGE_VERSIONS {
        let ver_s = ver.to_string();
        let orig_bytes = std::fs::read(work.join(format!("orig-{ver_s}.abc"))).expect("orig abc");
        let ref_pa = std::fs::read(work.join(format!("orig-{ver_s}.pa"))).expect("orig pa");

        let file = decode(&orig_bytes).expect("decode es2abc merge-abc");
        assert_eq!(file.version, ver);

        // Pipeline 2a: pandasm::emit_file matches upstream ark_disasm byte-for-byte!
        let our_pa = pandasm::emit_file(&file, &format!("orig-{ver_s}.abc"));
        assert_eq!(
            our_pa, ref_pa,
            "pandasm::emit_file diverged from ark_disasm on --merge-abc ({ver_s})"
        );

        // Pipeline 1: decode → encode
        let id_bytes = encode(&file).expect("identity encode merge-abc");
        std::fs::write(work.join(format!("cand-id-{ver_s}.abc")), &id_bytes).expect("write id");

        // Pipeline 3: lift → [opt] → lower → encode
        let (lift_bytes, _) = rewrite_file_e2e(&orig_bytes, false);
        std::fs::write(work.join(format!("cand-lift-{ver_s}.abc")), &lift_bytes)
            .expect("write v2lift");
        let (opt_bytes, _) = rewrite_file_e2e(&orig_bytes, true);
        std::fs::write(work.join(format!("cand-opt-{ver_s}.abc")), &opt_bytes)
            .expect("write v2opt");

        // Pipeline 4: decompile syntax & zero-fallback check
        let ir = lift_file(&file).expect("lift es2abc merge-abc");
        let decomp = decompile_module(&ir, &EmitOptions::default());
        assert_eq!(
            decomp.stats.functions_with_fallbacks, 0,
            "fallbacks in es2abc merge-abc ({ver_s}): {:?}",
            decomp.stats.fallback_comments
        );
        let mjs_path = work.join(format!("decomp-{ver_s}.mjs"));
        std::fs::write(&mjs_path, &decomp.text).expect("write decomp mjs");
        if has_node {
            let chk = Command::new("node")
                .arg("--check")
                .arg(&mjs_path)
                .output()
                .expect("node --check");
            assert!(
                chk.status.success(),
                "node --check failed ({ver_s}):\n{}\n{}",
                String::from_utf8_lossy(&chk.stderr),
                decomp.text
            );
        }

        // Pipeline 5 (#26 Phase 2): `--split-modules` multi-file tree output
        // ready for `es2abc --module --merge-abc` re-bundling & VM execution!
        let split = decompile_module_split(
            &ir,
            &EmitOptions {
                call_entry: true,
                ..Default::default()
            },
        );
        assert_eq!(
            split.stats.functions_with_fallbacks, 0,
            "fallbacks in split merge-abc ({ver_s}): {:?}",
            split.stats.fallback_comments
        );
        let split_dir = work.join(format!("split-{ver_s}"));
        std::fs::create_dir_all(&split_dir).expect("create split dir");
        let mut info_lines = String::new();
        for sf in &split.files {
            let dst = split_dir.join(&sf.rel_path);
            if let Some(parent) = dst.parent() {
                std::fs::create_dir_all(parent).expect("create split parent");
            }
            std::fs::write(&dst, &sf.text).expect("write split file");
            info_lines.push_str(&format!(
                "/work/split-{ver_s}/{};{};esm;{};entry\n",
                sf.rel_path, sf.record_name, sf.rel_path
            ));
        }
        std::fs::write(
            work.join(format!("split-filesInfo-{ver_s}.txt")),
            info_lines,
        )
        .expect("write split filesInfo");
    }

    // Step 3: Verify ALL 12 candidate .abc files (3 versions × 4 variants:
    // identity encode, v2lift, v2opt, and re-bundled `--split-modules` output)
    // pass BOTH `ark_disasm` AND `ark_js_vm --entry-point=main` with exact
    // `"merge-ok:42\n"` stdout inside ONE single container!
    let verify_py = r#"
import json, subprocess, sys
sys.path.insert(0, "/opt/arkcompiler-test")
import arktest

versions = arktest.read_json(arktest.ROOT / "versions.json")
checked = 0
for ver in ["12.0.6.0", "13.0.1.0", "24.0.0.0"]:
    split_abc = f"/work/cand-split-{ver}.abc"
    c = arktest.call("es2abc", versions[ver] + [
        "--module", "--merge-abc", f"--output={split_abc}", f"@/work/split-filesInfo-{ver}.txt"
    ])
    arktest.require_ok(c)
    for kind in ["id", "lift", "opt", "split"]:
        abc = f"/work/cand-{kind}-{ver}.abc"
        pa = f"/work/cand-{kind}-{ver}.pa"
        arktest.inspect(abc)
        d = arktest.call("ark_disasm", [abc, pa])
        arktest.require_ok(d)
        r = arktest.call("ark_js_vm", ["--entry-point=main", abc])
        arktest.require_ok(r)
        if r["stdout"] != "merge-ok:42\n" or r["stderr"]:
            raise RuntimeError(f"mismatch on {abc}: {r}")
        checked += 1
print(json.dumps({"checked": checked}))
"#;
    let verify_out = Command::new("docker")
        .args([
            "run",
            "--rm",
            "--platform",
            "linux/amd64",
            "--network",
            "none",
            "--ulimit",
            "stack=8388608:8388608",
            "-v",
            &format!("{}:/work", work.display()),
            "--entrypoint",
            "python3",
            &image,
            "-c",
            verify_py,
        ])
        .output()
        .expect("run docker merge-abc oracle verify");
    assert!(
        verify_out.status.success(),
        "docker merge-abc candidate verification failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&verify_out.stdout),
        String::from_utf8_lossy(&verify_out.stderr)
    );
    eprintln!(
        "MERGE-ABC-ORACLE green: {}",
        String::from_utf8_lossy(&verify_out.stdout).trim()
    );
}

/// Build a multi-record `--merge-abc` bundle exercising all four #32
/// commercial edge cases in one artifact:
/// 1. `Lmain;::func_main_0`: `L_ESTypeAnnotation;._TypeOfInstruction` with a
///    nested `LiteralValue::LiteralArray` surrounded by integer entries;
/// 2. `Lhelper;::loopFromZero`: loop header at bytecode index `0` mutating an
///    argument register (`a3`) + unfused `Stricteq + Jnez` where `v0` stays
///    live across the branch;
/// 3. `Lhelper;::catchAtZero`: `TryBlock` whose catch handler sits at bytecode
///    index `0`;
/// 4. `Lsendable;::func_main_0`: `callruntime.definesendableclass` whose class
///    buffer carries a trailing field-type-layout `LiteralArray` reference.
fn build_commercial_edge_merge_abc(version: Version) -> Vec<u8> {
    let mut file = decode(&build_synthetic_merge_abc(version)).expect("decode base merge-abc");

    // 1) Nested `_ESTypeAnnotation._TypeOfInstruction` on Lmain::func_main_0
    let nested_type_idx = file.literal_arrays.len() as u32;
    file.literal_arrays.push(LiteralArray::new(vec![
        LiteralValue::Integer(1),
        LiteralValue::Integer(51),
    ]));

    let s_estype = file.strings.get_or_intern("L_ESTypeAnnotation;");
    let s_typeof = file.strings.get_or_intern("_TypeOfInstruction");
    file.classes.insert(
        s_estype,
        abcd_file::Class {
            descriptor: s_estype,
            name: s_estype,
            access_flags: AccessFlags::PUBLIC,
            source_lang: SourceLang::EcmaScript,
            source_file: None,
            is_external: false,
            super_class: None,
            interfaces: Vec::new(),
            methods: Vec::new(),
            fields: Vec::new(),
            annotations: Default::default(),
        },
    );
    let main_cls = file
        .classes
        .values_mut()
        .find(|c| file.strings.resolve(c.descriptor) == Some("Lmain;"))
        .expect("Lmain;");
    main_cls.methods[0]
        .annotations
        .compile_time
        .push(Annotation {
            class_descriptor: s_estype,
            elements: vec![AnnotationElem {
                name: s_typeof,
                value: AnnotationValue::LiteralArray(vec![
                    LiteralValue::Integer(0),
                    LiteralValue::LiteralArray(LiteralArrayIdx(nested_type_idx)),
                    LiteralValue::Integer(4),
                ]),
            }],
        });

    // 2) Loop back-edge to offset 0 mutating param a3 + live compare operand,
    // and 3) Catch handler at offset 0 on Lhelper;
    let s_loop = file.strings.get_or_intern("loopFromZero");
    let s_catch0 = file.strings.get_or_intern("catchAtZero");
    let helper_cls = file
        .classes
        .values_mut()
        .find(|c| file.strings.resolve(c.descriptor) == Some("Lhelper;"))
        .expect("Lhelper;");
    helper_cls.methods.push(Method {
        name: s_loop,
        offset: 0,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::Function,
        source_lang: SourceLang::EcmaScript,
        is_external: false,
        return_type: Some(Type::Tagged),
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 2,
            num_args: 4,
            code: vec![
                Bytecode::Lda(Reg(5)),              // [0] header0: acc = a3
                Bytecode::Sta(Reg(0)),              // [1] v0 = a3 (kept live!)
                Bytecode::Ldai(Imm(0)),             // [2] acc = 0
                Bytecode::Stricteq(Imm(0), Reg(0)), // [3] acc = (0 === v0)
                Bytecode::Jnez(Label(9)),           // [4] if 0 === v0 -> [9]
                Bytecode::Lda(Reg(0)),              // [5] latch: v0 still live!
                Bytecode::Dec(Imm(1)),              // [6] acc = v0 - 1
                Bytecode::Sta(Reg(5)),              // [7] a3 = acc
                Bytecode::Jmp(Label(0)),            // [8] back-edge to offset 0
                Bytecode::Lda(Reg(0)),              // [9] exit
                Bytecode::Return,                   // [10]
            ]
            .into(),
            entities: abcd_file::MethodEntities::new(),
            try_blocks: Vec::new(),
            ic_size: Some(2),
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    });
    helper_cls.methods.push(Method {
        name: s_catch0,
        offset: 0,
        access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
        function_kind: FileFunctionKind::Function,
        source_lang: SourceLang::EcmaScript,
        is_external: false,
        return_type: Some(Type::Tagged),
        arg_types: Vec::new(),
        body: Some(MethodBody {
            num_vregs: 1,
            num_args: 3,
            code: vec![
                Bytecode::Sta(Reg(0)),    // [0] handler == 0 & entry target
                Bytecode::Jeqz(Label(4)), // [1]
                Bytecode::Ldundefined,    // [2] try [2..4)
                Bytecode::Throw,          // [3]
                Bytecode::Lda(Reg(0)),    // [4]
                Bytecode::Return,         // [5]
            ]
            .into(),
            entities: abcd_file::MethodEntities::new(),
            try_blocks: vec![TryBlock {
                start: 2,
                len: 2,
                catches: vec![CatchBlock {
                    type_class: None,
                    handler: 0,
                    len: 2,
                }],
            }],
            ic_size: None,
        }),
        annotations: Default::default(),
        param_annotations: Default::default(),
        debug: None,
    });

    // 4) Sendable class record with trailing field-type-layout literal array
    let s_send_desc = file.strings.get_or_intern("Lsendable;");
    let s_send_ctor = file.strings.get_or_intern("SendableBox");
    let s_get_val = file.strings.get_or_intern("getVal");
    let s_field_x = file.strings.get_or_intern("x");
    let s_func_main = file.strings.get_or_intern("func_main_0");

    let field_la_idx = file.literal_arrays.len() as u32;
    file.literal_arrays.push(LiteralArray::new(vec![
        LiteralValue::String(s_field_x),
        LiteralValue::Integer(2),
        LiteralValue::Integer(1),
    ]));
    let class_la_idx = file.literal_arrays.len() as u32;
    file.literal_arrays.push(LiteralArray::new(Vec::new()));

    file.classes.insert(
        s_send_desc,
        abcd_file::Class {
            descriptor: s_send_desc,
            name: s_send_desc,
            access_flags: AccessFlags::PUBLIC,
            source_lang: SourceLang::EcmaScript,
            source_file: None,
            is_external: false,
            super_class: None,
            interfaces: Vec::new(),
            methods: vec![
                Method {
                    name: s_send_ctor,
                    offset: 0,
                    access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
                    function_kind: FileFunctionKind::SendableFunction,
                    source_lang: SourceLang::EcmaScript,
                    is_external: false,
                    return_type: Some(Type::Tagged),
                    arg_types: Vec::new(),
                    body: Some(MethodBody {
                        num_vregs: 0,
                        num_args: 3,
                        code: vec![Bytecode::Lda(Reg(2)), Bytecode::Return].into(),
                        entities: abcd_file::MethodEntities::new(),
                        try_blocks: Vec::new(),
                        ic_size: None,
                    }),
                    annotations: Default::default(),
                    param_annotations: Default::default(),
                    debug: None,
                },
                Method {
                    name: s_get_val,
                    offset: 0,
                    access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
                    function_kind: FileFunctionKind::SendableFunction,
                    source_lang: SourceLang::EcmaScript,
                    is_external: false,
                    return_type: Some(Type::Tagged),
                    arg_types: Vec::new(),
                    body: Some(MethodBody {
                        num_vregs: 0,
                        num_args: 3,
                        code: vec![Bytecode::Ldai(Imm(7)), Bytecode::Return].into(),
                        entities: abcd_file::MethodEntities::new(),
                        try_blocks: Vec::new(),
                        ic_size: None,
                    }),
                    annotations: Default::default(),
                    param_annotations: Default::default(),
                    debug: None,
                },
                Method {
                    name: s_func_main,
                    offset: 0,
                    access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
                    function_kind: FileFunctionKind::Function,
                    source_lang: SourceLang::EcmaScript,
                    is_external: false,
                    return_type: Some(Type::Tagged),
                    arg_types: Vec::new(),
                    body: Some(MethodBody {
                        num_vregs: 1,
                        num_args: 3,
                        code: vec![
                            Bytecode::Ldhole,
                            Bytecode::Sta(Reg(0)),
                            Bytecode::CallruntimeDefinesendableclass(
                                Imm(0),
                                EntityId(0),
                                EntityId(1),
                                Imm(1),
                                Reg(0),
                            ),
                            Bytecode::Return,
                        ]
                        .into(),
                        entities: abcd_file::MethodEntities::new(),
                        try_blocks: Vec::new(),
                        ic_size: None,
                    }),
                    annotations: Default::default(),
                    param_annotations: Default::default(),
                    debug: None,
                },
            ],
            fields: Vec::new(),
            annotations: Default::default(),
        },
    );

    let send_ctor_idx = file
        .all_methods()
        .position(|(d, m)| d == s_send_desc && m.name == s_send_ctor)
        .expect("sendable ctor method index") as u32;
    let get_val_idx = file
        .all_methods()
        .position(|(d, m)| d == s_send_desc && m.name == s_get_val)
        .expect("sendable getter method index") as u32;
    file.literal_arrays[class_la_idx as usize].values = vec![
        LiteralValue::String(s_get_val),
        LiteralValue::Getter(abcd_file::MethodIdx(get_val_idx)),
        LiteralValue::MethodAffiliate(0),
        LiteralValue::Integer(1),
        LiteralValue::LiteralArray(LiteralArrayIdx(field_la_idx)),
    ];
    file.classes.get_mut(&s_send_desc).unwrap().methods[2]
        .body
        .as_mut()
        .unwrap()
        .entities = abcd_file::MethodEntities::from_iter([
        (
            (EntityKind::MethodId, 0),
            abcd_file::EntityRef::Method(abcd_file::MethodIdx(send_ctor_idx)),
        ),
        (
            (EntityKind::LiteralarrayId, 1),
            abcd_file::EntityRef::LiteralArray(LiteralArrayIdx(class_la_idx)),
        ),
    ]);

    encode(&file).expect("encode commercial edge merge-abc")
}

fn assert_commercial_edge_invariants(file: &File) {
    // 1) `_TypeOfInstruction` nested literal array survived without shifting
    let main_cls = file.class_by_str("Lmain;").expect("Lmain;");
    let m0 = &main_cls.methods[0];
    let estype = m0
        .annotations
        .compile_time
        .iter()
        .chain(&m0.annotations.runtime)
        .find(|a| file.strings.resolve(a.class_descriptor) == Some("L_ESTypeAnnotation;"))
        .expect("L_ESTypeAnnotation; on Lmain::func_main_0");
    let elem = estype
        .elements
        .iter()
        .find(|e| file.strings.resolve(e.name) == Some("_TypeOfInstruction"))
        .expect("_TypeOfInstruction");
    let AnnotationValue::LiteralArray(items) = &elem.value else {
        panic!(
            "expected LiteralArray value on _TypeOfInstruction, got {:?}",
            elem.value
        );
    };
    assert_eq!(items.len(), 3, "nested literal array items must not shift");
    assert_eq!(items[0], LiteralValue::Integer(0));
    assert_eq!(items[2], LiteralValue::Integer(4));
    let LiteralValue::LiteralArray(nested_idx) = items[1] else {
        panic!("expected nested LiteralArray at item 1, got {:?}", items[1]);
    };
    let nested_la = file
        .literal_arrays
        .get(nested_idx.0 as usize)
        .expect("nested _TypeOfInstruction target in File::literal_arrays");
    assert_eq!(
        nested_la.values,
        vec![LiteralValue::Integer(1), LiteralValue::Integer(51)]
    );

    // 2) Zero dead fused register-compare branches anywhere in the file
    for (_, method) in file.all_methods() {
        let Some(body) = &method.body else { continue };
        for bc in body.bytecodes().iter() {
            assert!(
                !matches!(
                    bc,
                    Bytecode::Jeq(..)
                        | Bytecode::Jne(..)
                        | Bytecode::Jstricteq(..)
                        | Bytecode::Jnstricteq(..)
                ),
                "lowered bytecode must never emit broken fused compare-branch: {bc:?}"
            );
        }
    }

    // 3) Re-lifting the rewritten file verifies cleanly and preserves Sendable member_attrs
    let ir = lift_file(file).expect("lift commercial edge merge-abc");
    let report = verify_module(&ir);
    assert!(report.is_ok(), "verify failed: {:?}", report.errors);
    let sendable_attrs: Vec<usize> = ir
        .insts
        .iter()
        .filter_map(|inst| match &inst.op {
            Op::DefineSendableClass(cls) => Some(cls.member_attrs.len()),
            _ => None,
        })
        .collect();
    assert_eq!(
        sendable_attrs,
        vec![1],
        "DefineSendableClass must preserve getter member_attrs across trailing field layout"
    );
}

#[test]
fn synthetic_merge_abc_commercial_edge_cases_across_versions() {
    for version in MERGE_VERSIONS {
        let raw = build_commercial_edge_merge_abc(version);
        let decoded = decode(&raw).expect("decode commercial edge merge-abc");
        assert_eq!(decoded.version, version);
        assert_commercial_edge_invariants(&decoded);

        let (rewritten_lift, _) = rewrite_file_e2e(&raw, false);
        let decoded_lift = decode(&rewritten_lift).expect("decode v2lift commercial merge-abc");
        assert_commercial_edge_invariants(&decoded_lift);

        let (rewritten_opt, opt_changed) = rewrite_file_e2e(&raw, true);
        assert!(
            opt_changed,
            "constant folding must fire on Lmain::func_main_0"
        );
        let decoded_opt = decode(&rewritten_opt).expect("decode v2opt commercial merge-abc");
        assert_commercial_edge_invariants(&decoded_opt);
    }
}

#[test]
#[ignore = "requires local-only modules.abc (gitignored)"]
fn modules_abc_commercial_bundle_rewrite_v2lift_and_v2opt() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("modules.abc");
    if !path.exists() {
        eprintln!("modules.abc absent at {} — skipped", path.display());
        return;
    }
    let raw = std::fs::read(&path).expect("read modules.abc");

    for optimize in [false, true] {
        let tag = if optimize { "v2opt" } else { "v2lift" };
        let (rewritten, _) = rewrite_file_e2e(&raw, optimize);
        let relifted_file =
            decode(&rewritten).unwrap_or_else(|e| panic!("re-decode modules.abc ({tag}): {e}"));
        let relifted_ir = lift_file(&relifted_file)
            .unwrap_or_else(|e| panic!("re-lift modules.abc ({tag}): {e}"));
        assert_eq!(relifted_ir.functions.len(), 58_699);
        let report = verify_module(&relifted_ir);
        assert!(
            report.is_ok(),
            "post-rewrite verify failed on modules.abc ({tag}): {:?}",
            &report.errors[..report.errors.len().min(10)]
        );
    }
}
