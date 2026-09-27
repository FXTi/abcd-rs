//! N72-C2 regression pins: the builtin-subclassing behavior-exit-code
//! cluster (4 test262 rows) — the default derived constructor of
//! `class X extends <builtin> {}` mis-lowered.
//!
//! Root cause (vendor-verified): es2abc emits the default derived
//! constructor as a `callruntime.supercallforwardallargs v_func` site
//! (isa.yaml:944 `sig: callruntime.supercallforwardallargs v:in:top`).
//! The vendor handler (interpreter-inl.cpp:3814-3830
//! `HANDLE_OPCODE(CALLRUNTIME_SUPERCALLFORWARDALLARGS_PREF_V8)`) reads
//! `thisFunc` from the REGISTER operand, takes `newTarget` from the
//! CURRENT frame (`GetNewTarget(thread, sp)`), and forwards the frame's
//! FULL actual argument list (`GetNumArgs(thread, sp, …)`) to
//! `RuntimeSuperCallForwardAllArgs` (runtime_stubs-inl.h:299-322), which
//! `JSFunction::Construct`s the super constructor with those arguments.
//! There is NO explicit argument window and the acc is NOT an input.
//!
//! The v0.2 lift keeps a dedicated IR kind (`CallKind::SuperForwardAllArgs`,
//! translate.rs `Bytecode::CallruntimeSupercallforwardallargs` arm — N58),
//! but the lower's arm (abcd-lower/src/isel.rs `CallKind::SuperForwardAllArgs`)
//! used to emit `supercallthisrange ic, argc=1, window=[func]` — the super
//! constructor was Construct'ed with ONE argument, the function object
//! itself:
//!
//! - `Error/regular-subclassing`: `Error(func)` → message =
//!   `Function.prototype.toString(func)` = "Cannot get source code"
//!   (expected «foo 42»);
//! - `TypedArray/regular-subclassing`: `Int8Array(func)` → length 0
//!   (expected 2);
//! - `WeakSet/regular-subclassing`: `WeakSet(func)` → func is not
//!   iterable → "TypeError: Callable is false";
//! - `ArrayBuffer/isView/arg-is-dataview-subclass-instance`:
//!   `DataView(func, …)` → "TypeError: buffer is not ArrayBuffer".
//!
//! The fix lowers the arm to the vendor opcode
//! `callruntime.supercallforwardallargs v_func` itself.
//!
//! Per fixture the test asserts: (a) the IR of the fixture DOES contain
//! `SuperForwardAllArgs` call sites (the construct is present — a vacuous
//! green is impossible), and (b) the lowered bytecode stream contains
//! exactly as many `callruntime.supercallforwardallargs` instructions as
//! IR sites, and (c) the full rewrite (lower + splice + encode) succeeds.
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-lower --release -- --ignored --nocapture n72_subclass
//! ```

use std::path::PathBuf;

use abcd_ir::{CallKind, FuncId, Op};
use abcd_isa::Bytecode;
use abcd_lower::{lower_function_with_options, LowerOptions};

use super::rewrite_pipeline::{front_end, guarded, rewrite_fixture};

/// The 4 test262 fixtures of the builtin-subclassing behavior-exit-code
/// cluster (corpus-relative abc paths, as listed in
/// scripts/test262-vm-divergences.json).
const N72_SUBCLASS_FIXTURES: [&str; 4] = [
    "24.0.0.0/test262/language/statements/class/subclass/builtin-objects/Error/regular-subclassing/baseline/input.abc",
    "24.0.0.0/test262/language/statements/class/subclass/builtin-objects/TypedArray/regular-subclassing/baseline/input.abc",
    "24.0.0.0/test262/language/statements/class/subclass/builtin-objects/WeakSet/regular-subclassing/baseline/input.abc",
    "24.0.0.0/test262/built-ins/ArrayBuffer/isView/arg-is-dataview-subclass-instance/baseline/input.abc",
];

#[test]
#[ignore = "requires exported GHCR corpus"]
fn n72_supercallforwardallargs_preserved_by_rewrite() {
    let root = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus"));

    let mut failures = Vec::new();
    for relative in N72_SUBCLASS_FIXTURES {
        let result = guarded(|| {
            let (file, module) = front_end(&root.join(relative))?;

            // (a) The fixture's IR must contain the construct under test.
            let mut ir_sites = 0usize;
            for index in 0..module.functions.len() {
                let func_id = FuncId::new(index as u32);
                let func = module.func(func_id).expect("function-table index");
                for &block_id in &func.blocks {
                    let block = module.block(block_id).expect("block-table index");
                    for &inst_id in &block.insts {
                        let inst = module.inst(inst_id).expect("inst-table index");
                        if let Op::Call {
                            kind: CallKind::SuperForwardAllArgs,
                            ..
                        } = &inst.op
                        {
                            ir_sites += 1;
                        }
                    }
                }
            }

            // (b) Every IR site must lower to the vendor opcode.
            let mut lowered_sites = 0usize;
            for index in 0..module.functions.len() {
                let func_id = FuncId::new(index as u32);
                let func = module.func(func_id).expect("function-table index");
                if func.blocks.is_empty() {
                    continue;
                }
                let lowered =
                    lower_function_with_options(&module, func_id, LowerOptions::default())
                        .map_err(|e| {
                            (
                                super::rewrite_pipeline::SkipCategory::LowerOther,
                                format!("lower: {e}"),
                            )
                        })?;
                lowered_sites += lowered
                    .bytecodes
                    .iter()
                    .filter(|bc| matches!(bc, Bytecode::CallruntimeSupercallforwardallargs(_)))
                    .count();
            }

            // (c) The full rewrite must still succeed.
            let (encoded, _functions) = rewrite_fixture(&module, &file, LowerOptions::default())?;
            Ok((ir_sites, lowered_sites, encoded.len()))
        });
        match result {
            Ok((ir_sites, lowered_sites, size)) => {
                eprintln!(
                    "N72-C2 {relative}: ir SuperForwardAllArgs sites = {ir_sites}, \
                     lowered callruntime.supercallforwardallargs = {lowered_sites} \
                     ({size} bytes)"
                );
                if ir_sites == 0 {
                    eprintln!(
                        "FAIL {relative} | fixture no longer contains the construct under test"
                    );
                    failures.push(relative);
                } else if lowered_sites != ir_sites {
                    eprintln!(
                        "FAIL {relative} | {ir_sites} IR site(s) lowered to \
                         {lowered_sites} callruntime.supercallforwardallargs (the \
                         supercallthisrange argc=1 approximation)"
                    );
                    failures.push(relative);
                }
            }
            Err((category, reason)) => {
                eprintln!("FAIL {relative} | {category} | {reason}");
                failures.push(relative);
            }
        }
    }
    assert!(
        failures.is_empty(),
        "N72-C2: {} fixture(s) still mis-lower supercallforwardallargs: {failures:?}",
        failures.len()
    );
}
