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
    AccessFlags, Builder, FieldValue, File, JSON_FILE_CONTENT_FIELD, MODULE_RECORD_IDX_FIELD,
    MODULE_REQUEST_PHASE_FIELD, ModuleRecordDef, SCOPE_NAMES_FIELD, SourceLang, Type, Version,
    decode, encode, pandasm,
};
use abcd_ir::verify_module;
use abcd_isa::{Bytecode, Imm, Reg, encode as encode_isa, insn};
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
    let bcs = &helper_main.body.as_ref().expect("helper body").bytecodes;
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
    for class in rebuilt.classes.values_mut() {
        for method in &mut class.methods {
            let slot = cursor.next().expect("method cursor");
            if method.body.is_some() {
                method.body = Some(slot.expect("lowered body"));
            }
        }
    }
    assert!(cursor.next().is_none());

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
        "export function makeAdder(seed) {\n  const step = 2;\n  return (x) => x + seed + step;\n}\n",
    )
    .expect("helper.js");
    std::fs::write(src.join("lazyMod.js"), "export const bonus = 10;\n").expect("lazyMod.js");
    std::fs::write(
        src.join("main.js"),
        "import cfg from \"./cfg.json\";\n\
         import { makeAdder } from \"./helper\";\n\
         import lazy { bonus } from \"./lazyMod\";\n\
         const add = makeAdder(cfg.base);\n\
         print(cfg.tag + \":\" + (add(10) + bonus));\n",
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
