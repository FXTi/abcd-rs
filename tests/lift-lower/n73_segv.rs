//! N73 regression: the three `call_this_range_with_name` corpus fixtures
//! (`runtime.status == "not-applicable"` — no VM gate covers them) used to
//! rewrite into a file that SIGSEGVs the VM (`ark_js_vm` exit -11) at the
//! LAST of its three 128-argument `wide.callthisrange` sites.
//!
//! Root cause (fixed in `abcd-file::encode`): the lower's dense per-method
//! IC-slot assignment can consume MORE slots than the source bytecode did —
//! here +6, because three `wide.callthisrangewithname` (no IC operand)
//! fold to narrow `callthisrange` (a two-slot IC each). The method's
//! `_ESSlotNumberAnnotation`/`SlotNumber` annotation was preserved verbatim
//! from the source file (319) while the rewritten bytecode referenced IC
//! slots up to 324. The runtime sizes the method's `ProfileTypeInfo` array
//! from that annotation
//! (arkcompiler_ets_runtime-master/ecmascript/jspandafile/
//! method_literal.cpp:51-77) and the interpreter's IC paths index it with
//! the unchecked slot immediate (interpreter-inl.cpp:2556-2565), so slots
//! ≥ 319 read/write past the array — heap corruption surfacing as a
//! SIGSEGV in the last catch handler's `print(e.stack)`.
//!
//! The fix syncs the annotation to the lowered body's `ic_size` at encode
//! time. This test pins the contract STRUCTURALLY (no docker needed): for
//! every method of every rewritten fixture, every IC-slot immediate must
//! lie strictly below the method's `SlotNumber` annotation. At HEAD
//! (pre-fix) func_main_0 fails with annotation 319 < max slot end 325.
//!
//! VM-level evidence (docker, recorded at the N73 fix): all 3 fixtures ×
//! v2lift/v2opt/v2inline run to completion (exit 0, 18 caught "not
//! callable" messages); pre-fix all crashed with exit -11 after the 18th
//! message. The remaining stdout difference vs the original — "1 is not
//! callable" vs "b is not callable, b is 1" — is the ACCEPTED
//! withname→plain fold (the name operand is dropped; documented, not part
//! of N73).
//!
//! When `ABCD_LOWERED_DIR` is set the rewrites are also written into
//! `$ABCD_LOWERED_DIR/{v2lift,v2opt}/` (the corpus_lower_oracle candidate
//! tree — the fixtures' not-applicable runtime status keeps them out of
//! the VM comparison itself).

use std::path::Path;

use abcd_isa::{BytecodeFlags, Operand};

use super::rewrite_pipeline::{front_end, rewrite_fixture};

/// The three N73 fixtures (corpus-relative abc paths).
const FIXTURES: [&str; 3] = [
    "24.0.0.0/upstream/version_control/API24/bytecode_feature/call_this_range_with_name/baseline/input.abc",
    "24.0.0.0/upstream/version_control/API24/bytecode_feature/call_this_range_with_name/debug-info/input.abc",
    "24.0.0.0/upstream/version_control/API24/bytecode_feature/call_this_range_with_name/optimized/input.abc",
];

/// The highest IC slot END referenced by `body` (0 when the body uses no
/// IC). The IC immediate is the first operand of every IC-carrying
/// instruction (isa.yaml: the `imm`/`imm1` sig operand holds the slot);
/// `two_slot` instructions occupy two consecutive slots. The 0xFF
/// degraded no-IC sentinel never exceeds a sane annotation, so it needs
/// no special-casing here.
fn max_ic_slot_end(body: &abcd_file::MethodBody) -> u32 {
    let mut max_end = 0u32;
    for bc in &body.bytecodes {
        if !bc.has_flag(BytecodeFlags::IC_SLOT) && !bc.has_flag(BytecodeFlags::JIT_IC_SLOT) {
            continue;
        }
        let width = if bc.has_flag(BytecodeFlags::TWO_SLOT) {
            2
        } else {
            1
        };
        if let Some(Operand::Imm(slot)) = bc.operands().first() {
            max_end = max_end.max((*slot as u32) + width);
        }
    }
    max_end
}

/// The method's `_ESSlotNumberAnnotation`/`SlotNumber` value, if present.
fn slot_number_annotation(file: &abcd_file::File, method: &abcd_file::Method) -> Option<u32> {
    method
        .annotations
        .compile_time
        .iter()
        .chain(method.annotations.runtime.iter())
        .chain(method.annotations.compile_time_type.iter())
        .chain(method.annotations.runtime_type.iter())
        .filter(|ann| {
            file.strings.resolve(ann.class_descriptor) == Some("L_ESSlotNumberAnnotation;")
        })
        .flat_map(|ann| &ann.elements)
        .filter(|e| file.strings.resolve(e.name) == Some("SlotNumber"))
        .find_map(|e| match e.value {
            abcd_file::AnnotationValue::U32(v) => Some(v),
            _ => None,
        })
}

/// Assert the N73 contract on an encoded rewrite: every method body's
/// IC-slot immediates lie below the method's SlotNumber annotation (the
/// VM's ProfileTypeInfo array size).
fn assert_ic_slots_covered(encoded: &[u8], context: &str) {
    let file = abcd_file::decode(encoded).expect("re-decode rewritten output");
    for class in file.classes.values() {
        for method in &class.methods {
            let Some(body) = &method.body else { continue };
            let max_end = max_ic_slot_end(body);
            if max_end == 0 {
                continue; // no IC-carrying instructions
            }
            let ann = slot_number_annotation(&file, method).unwrap_or_else(|| {
                panic!("{context}: method with IC slots (max end {max_end}) has no SlotNumber annotation")
            });
            assert!(
                ann >= max_end,
                "{context}: SlotNumber annotation {ann} < max IC slot end {max_end} \
                 (VM ProfileTypeInfo array would be undersized — the N73 SIGSEGV)"
            );
        }
    }
}

#[test]
#[ignore = "requires exported GHCR corpus"]
fn n73_call_this_range_with_name_rewrites_with_synced_ic_slots() {
    let root = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus"));

    let out_root = std::env::var_os("ABCD_LOWERED_DIR").map(std::path::PathBuf::from);

    for relative in FIXTURES {
        let path = root.join(relative);
        assert!(path.exists(), "missing corpus fixture: {}", path.display());

        let (file, module) = front_end(Path::new(&path)).unwrap_or_else(|(cat, reason)| {
            panic!("{relative}: front-end failed: {cat} | {reason}")
        });

        // v2lift.
        let (encoded, functions) = rewrite_fixture(&module, &file, Default::default())
            .unwrap_or_else(|(cat, reason)| {
                panic!("{relative}: v2lift rewrite failed: {cat} | {reason}")
            });
        assert!(functions > 0);
        assert_ic_slots_covered(&encoded, &format!("{relative} v2lift"));
        if let Some(dir) = &out_root {
            let target = dir.join("v2lift").join(relative);
            std::fs::create_dir_all(target.parent().unwrap()).unwrap();
            std::fs::write(target, &encoded).expect("write oracle candidate");
        }

        // v2opt (the optimizer deletes the last use of a frame-initial
        // constant; same LowerOptions split as the corpus oracle).
        let mut optimized = module.clone();
        abcd_opt::optimize_module(&mut optimized);
        let report = abcd_ir::verify_module(&optimized);
        assert!(
            report.is_ok(),
            "{relative}: post-optimize verify: {:?}",
            report.errors
        );
        let (encoded, _) = rewrite_fixture(
            &optimized,
            &file,
            abcd_lower::LowerOptions {
                prune_unused_frame_init_consts: true,
            },
        )
        .unwrap_or_else(|(cat, reason)| {
            panic!("{relative}: v2opt rewrite failed: {cat} | {reason}")
        });
        assert_ic_slots_covered(&encoded, &format!("{relative} v2opt"));
        if let Some(dir) = &out_root {
            let target = dir.join("v2opt").join(relative);
            std::fs::create_dir_all(target.parent().unwrap()).unwrap();
            std::fs::write(target, &encoded).expect("write oracle candidate");
        }

        eprintln!("N73-OK {relative}");
    }
}
