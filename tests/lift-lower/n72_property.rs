//! N72-C4 regression pins: the 5 test262 fixtures of the
//! property-semantics behavior-divergence cluster (v2lift rewrite changed
//! exit code 0 → 255). Two independent root causes, both diagnosed
//! against vendored sources:
//!
//! **Cause A — modern `callthisrange` argc off-by-one (lift + lower),
//! SHARED with N72-C3 (fixed in the same tree state).** Vendor semantics
//! (arkcompiler_ets_runtime `ecmascript/interpreter/interpreter-inl.cpp`:
//! `CALL_PUSH_ARGS_THISRANGE` pushes `sp[startReg + i]` for
//! `i = actualNumArgs ..= 1` — "1: skip this"; es2panda
//! `PandaGen::CallThis`, pandagen.cpp:1357-1366: `actualArgs =
//! argCount - 1`): `imm2` counts the REAL arguments EXCLUDING `this`, and
//! the register window is `[this, arg0..]` = `imm2 + 1` slots. The lift's
//! `call_this_args` read only `imm2` registers (dropping the last
//! argument); the lower's `emit_range_call` wrote `argc_imm` = window
//! size INCLUDING `this`. Round-trip was self-consistent, so the
//! 1149-row project corpus (zero runtime-passed modern-callthisrange
//! coverage) never caught it. Signature: `Reflect.set(o, 'p', v, recv)`
//! silently degraded to a 3-argument call — `recv` dropped, `receiver`
//! semantics gone (returns `true` instead of `false` on a non-writable
//! receiver property; the receiver-as-`this` assertion fails).
//! `Object.assign(t, "aaa", "bb2b", "1c")` likewise dropped `"1c"`.
//!
//! **Cause B — global-record stores fold into global-object stores
//! (N72-C4 unique).** The lift maps `sttoglobalrecord` /
//! `stconsttoglobalrecord` (and the deprecated
//! stlet-/stclass-/stconstto-globalrecord trio) to the SAME
//! `Op::StoreGlobal` as `stglobalvar` (translate.rs), so the lower
//! re-emits `stglobalvar`. Vendor semantics differ
//! (interpreter-inl.cpp: `SlowRuntimeStub::StGlobalVar` stores a property
//! on the global OBJECT; `SlowRuntimeStub::StGlobalRecord(name, value,
//! isConst)` stores into the global LEXICAL record): the rewrite turns a
//! top-level `let Array` into `globalThis.Array = undefined`, clobbering
//! the builtin — `typeof this.Array` reads `undefined` instead of
//! `function`.
//!
//! Table below: the 5 cluster rows (corpus-relative abc paths) with the
//! exact post-fix expectation that was RED at HEAD-before-fix:
//!
//! - `RangeCalls { argc, count }`: the rewritten file must contain
//!   exactly `count` modern `callthisrange`-family instructions carrying
//!   `argc` (pre-fix: zero — the sites degraded to short-form
//!   `callthis3` with the last argument dropped).
//! - `GlobalRecordStores { record, object }`: the rewritten file must
//!   contain exactly `record` `sttoglobalrecord`/`stconsttoglobalrecord`
//!   instructions and exactly `object` `stglobalvar` instructions
//!   (pre-fix: the 2 record stores degraded to `stglobalvar`, giving 0
//!   record / 5 object).
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-lower --release -- --ignored --nocapture n72_property
//! ```

use std::path::PathBuf;

use abcd_isa::Bytecode;
use abcd_lower::LowerOptions;

use super::rewrite_pipeline::{front_end, guarded, rewrite_fixture};

enum Expect {
    /// Exactly `count` modern callthisrange-family instructions with
    /// this argc in the whole rewritten file.
    RangeCalls { argc: i64, count: usize },
    /// Exactly `record` global-RECORD stores (sttoglobalrecord /
    /// stconsttoglobalrecord) and exactly `object` global-OBJECT stores
    /// (stglobalvar) in the whole rewritten file.
    GlobalRecordStores { record: usize, object: usize },
}

const N72_ROWS: [(&str, Expect); 5] = [
    // `Reflect.set(o1, 'p', 42, receiver)` — two 4-argument
    // callthisrange sites (o1 without own `p`, o2 with a data `p`);
    // the dropped receiver made both return `true`.
    (
        "24.0.0.0/test262/built-ins/Reflect/set/different-property-descriptors/baseline/input.abc",
        Expect::RangeCalls { argc: 4, count: 2 },
    ),
    // `Reflect.set(o1, 'p', 43, receiver)` — one 4-argument site; the
    // dropped receiver turned the non-writable-receiver `false` into
    // `true`.
    (
        "24.0.0.0/test262/built-ins/Reflect/set/return-false-if-target-is-not-writable/baseline/input.abc",
        Expect::RangeCalls { argc: 4, count: 1 },
    ),
    // `Reflect.set(o1, 'p', 42, receiver)` — one 4-argument site; the
    // dropped receiver broke the setter's `this`.
    (
        "24.0.0.0/test262/built-ins/Reflect/set/set-value-on-accessor-descriptor-with-receiver/baseline/input.abc",
        Expect::RangeCalls { argc: 4, count: 1 },
    ),
    // `Object.assign(target, "aaa", "bb2b", "1c")` — one 4-argument
    // site; the dropped "1c" left result[0] === 'b' instead of '1'.
    (
        "24.0.0.0/test262/built-ins/Object/assign/Override-notstringtarget/baseline/input.abc",
        Expect::RangeCalls { argc: 4, count: 1 },
    ),
    // `let Array;` + `let descriptor = …` at global scope — two
    // sttoglobalrecord stores; the harness function declarations are
    // three stglobalvar stores. Pre-fix rewrite: 0 record / 5 object.
    (
        "24.0.0.0/test262/language/global-code/decl-lex-configurable-global/baseline/input.abc",
        Expect::GlobalRecordStores { record: 2, object: 3 },
    ),
];

/// Count modern callthisrange-family instructions with the given argc
/// immediate.
fn range_calls_with_argc(file: &abcd_file::File, argc: i64) -> usize {
    file.classes
        .values()
        .flat_map(|class| class.methods.iter())
        .filter_map(|method| method.body.as_ref())
        .flat_map(|body| body.bytecodes.iter())
        .filter(|bc| {
            matches!(
                bc,
                Bytecode::Callthisrange(_, imm, _)
                | Bytecode::WideCallthisrange(imm, _)
                | Bytecode::Callthisrangewithname(_, imm, _, _)
                | Bytecode::WideCallthisrangewithname(imm, _, _)
                if imm.0 == argc
            )
        })
        .count()
}

/// Count (global-record stores, global-object stores) in the file.
fn global_store_counts(file: &abcd_file::File) -> (usize, usize) {
    let mut record = 0usize;
    let mut object = 0usize;
    for bc in file
        .classes
        .values()
        .flat_map(|class| class.methods.iter())
        .filter_map(|method| method.body.as_ref())
        .flat_map(|body| body.bytecodes.iter())
    {
        match bc {
            Bytecode::Sttoglobalrecord(..) | Bytecode::Stconsttoglobalrecord(..) => record += 1,
            Bytecode::Stglobalvar(..) => object += 1,
            _ => {}
        }
    }
    (record, object)
}

#[test]
#[ignore = "requires exported GHCR corpus"]
fn n72_property_cluster_fixtures_rewrite_losslessly() {
    let root = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus"));

    let mut failures = Vec::new();
    for (relative, expect) in &N72_ROWS {
        let result = guarded(|| {
            let (file, module) = front_end(&root.join(relative))?;
            rewrite_fixture(&module, &file, LowerOptions::default())
        });
        let (encoded, _functions) = match result {
            Ok(pair) => pair,
            Err((category, reason)) => {
                eprintln!("FAIL {relative} | {category} | {reason}");
                failures.push(*relative);
                continue;
            }
        };
        match expect {
            Expect::RangeCalls { argc, count } => {
                let decoded = abcd_file::decode(&encoded).expect("re-decode rewritten fixture");
                let found = range_calls_with_argc(&decoded, *argc);
                if found != *count {
                    eprintln!(
                        "FAIL {relative} | expected {count} callthisrange argc={argc}, found {found}"
                    );
                    failures.push(*relative);
                }
            }
            Expect::GlobalRecordStores { record, object } => {
                let decoded = abcd_file::decode(&encoded).expect("re-decode rewritten fixture");
                let (got_record, got_object) = global_store_counts(&decoded);
                if got_record != *record || got_object != *object {
                    eprintln!(
                        "FAIL {relative} | expected {record} record / {object} object global \
                         stores, found {got_record} / {got_object}"
                    );
                    failures.push(*relative);
                }
            }
        }
    }

    assert!(
        failures.is_empty(),
        "N72 property-semantics cluster regressions: {failures:?}"
    );
}
