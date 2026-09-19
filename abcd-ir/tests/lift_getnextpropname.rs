//! N33 regression (P3-T21): `getnextpropname` must round-trip as its
//! own instruction, not collapse into `GetPropIterator`.
//!
//! Vendor facts:
//! - `getnextpropname v:in:top, acc: out:top`
//!   (abcd-isa-sys/vendor/isa/isa.yaml:1289-1292): the register operand
//!   is the ITERATOR; the next property name goes to the accumulator.
//!   The handler advances the iterator
//!   (`SlowRuntimeStub::GetNextPropName(thread, iter)` + `SET_ACC`,
//!   arkcompiler_ets_runtime-master/ecmascript/interpreter/
//!   interpreter_assembly.cpp:2085-2099) — a side effect on the
//!   iterator object, so the instruction stays DCE-essential even when
//!   its result is unused.
//! - Corpus corroboration (exports/corpus/9.0.0.0/local/for-in/
//!   baseline/reference.pa:42-44): `getnextpropname v7` / `sta v8`.
//!
//! Pre-N33 the lift "reused" `GetPropIterator` for `getnextpropname`
//! (translate.rs's own comment confessed the shortcut): lowering emitted
//! `getpropiterator` where the source had `getnextpropname`, wrapping
//! the iterator in a fresh prop-iterator every loop iteration — the
//! for-in x18 GC-abort family.

use abcd_file::decode;
use abcd_ir::entity::FuncId;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::lower_function;
use abcd_ir::verify::verify_module;
use abcd_isa::Bytecode;

fn corpus_root() -> std::path::PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        })
}

fn for_in_fixture() -> std::path::PathBuf {
    corpus_root().join("9.0.0.0/local/for-in/baseline/input.abc")
}

/// Opcode-for-opcode round-trip: the lowered stream must contain
/// `getnextpropname` (and `getpropiterator`) exactly as many times as
/// the source. Pre-N33 every `getnextpropname` came back as
/// `getpropiterator` (0 vs N), doubling the getpropiterator count.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn lowered_for_in_fixture_preserves_getnextpropname() {
    let data = std::fs::read(for_in_fixture()).expect("for-in fixture");
    let file = decode(&data).expect("decode for-in fixture");
    let (mut src_next, mut src_iter) = (0usize, 0usize);
    for (_, method) in file.all_methods() {
        if let Some(body) = &method.body {
            for bc in &body.bytecodes {
                match bc {
                    Bytecode::Getnextpropname(..) => src_next += 1,
                    Bytecode::Getpropiterator => src_iter += 1,
                    _ => {}
                }
            }
        }
    }
    assert!(src_next > 0, "fixture must exercise getnextpropname");

    let module = lift_file(&file).expect("lift for-in fixture");
    assert!(verify_module(&module).is_empty());

    let (mut out_next, mut out_iter) = (0usize, 0usize);
    for index in 0..module.functions.len() {
        let lowered =
            lower_function(&module, FuncId::from_index(index)).expect("for-in fixture must lower");
        for bc in &lowered.bytecodes {
            match bc {
                Bytecode::Getnextpropname(..) => out_next += 1,
                Bytecode::Getpropiterator => out_iter += 1,
                _ => {}
            }
        }
    }
    assert_eq!(
        out_next, src_next,
        "every source getnextpropname must lower back to getnextpropname \
         (not getpropiterator)"
    );
    assert_eq!(
        out_iter, src_iter,
        "no extra getpropiterator may appear from collapsed getnextpropname"
    );
}
