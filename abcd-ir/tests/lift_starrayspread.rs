//! N31 regression (P3-T21): `starrayspread` must round-trip as its own
//! instruction with all THREE vendor operands and the acc-out result.
//!
//! Vendor facts:
//! - `starrayspread v1:in:top, v2:in:top, acc: inout:top`
//!   (abcd-isa-sys/vendor/isa/isa.yaml:1329-1332): v1 is the
//!   DESTINATION ARRAY, v2 the INDEX, the accumulator the SOURCE
//!   ITERABLE; the runtime appends the spread elements and writes the
//!   NEW INDEX back to acc (`SlowRuntimeStub::StArraySpread(thread,
//!   dst, index, src)` + `SET_ACC`, arkcompiler_ets_runtime-master/
//!   ecmascript/interpreter/interpreter_assembly.cpp:2876-2894).
//! - Corpus corroboration (exports/corpus/9.0.0.0/local/call-shapes/
//!   baseline/reference.pa:72-79):
//!
//! ```text
//! sta v8                      # v8 = destination array
//! ldai 0x0
//! sta v9                      # v9 = index 0
//! tryldglobalbyname 0xd, "x"  # acc = source iterable
//! starrayspread v8, v9
//! ```
//!
//! Pre-N31 the lift collapsed `starrayspread` into a single
//! `StoreProperty { object: arr, key: ByValue(idx), value: acc }` —
//! ONE property store instead of a spread append, with the new-index
//! acc-out dropped — so lowering emitted `stobjbyvalue` where the
//! source had `starrayspread` (call-shapes x18 failures).

use abcd_file::decode;
use abcd_ir::entity::FuncId;
use abcd_ir::inst::InstData;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::lower_function;
use abcd_ir::module::ValueDef;
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

fn call_shapes_fixture() -> std::path::PathBuf {
    corpus_root().join("9.0.0.0/local/call-shapes/baseline/input.abc")
}

/// Opcode-for-opcode round-trip: the lowered stream must contain
/// `starrayspread` exactly as many times as the source (pre-N31: zero
/// — every one came back as `stobjbyvalue`).
#[test]
#[ignore = "requires exported GHCR corpus"]
fn lowered_call_shapes_fixture_preserves_starrayspread() {
    let data = std::fs::read(call_shapes_fixture()).expect("call-shapes fixture");
    let file = decode(&data).expect("decode call-shapes fixture");
    let mut src_spread = 0usize;
    for (_, method) in file.all_methods() {
        if let Some(body) = &method.body {
            for bc in &body.bytecodes {
                if matches!(bc, Bytecode::Starrayspread(..)) {
                    src_spread += 1;
                }
            }
        }
    }
    assert!(src_spread > 0, "fixture must exercise starrayspread");

    let module = lift_file(&file).expect("lift call-shapes fixture");
    assert!(verify_module(&module).is_empty());

    let mut out_spread = 0usize;
    for index in 0..module.functions.len() {
        let lowered = lower_function(&module, FuncId::from_index(index))
            .expect("call-shapes fixture must lower");
        for bc in &lowered.bytecodes {
            if matches!(bc, Bytecode::Starrayspread(..)) {
                out_spread += 1;
            }
        }
    }
    assert_eq!(
        out_spread, src_spread,
        "every source starrayspread must lower back to starrayspread \
         (not stobjbyvalue)"
    );
}

/// The lifted `ArraySpread` must carry the THREE vendor operands in
/// role: dst = the array (defined by `CreateArrayWithBuffer`), index =
/// the integer start index (`LiteralNumber`), src = the accumulator
/// iterable (the `tryldglobalbyname` result).
#[test]
#[ignore = "requires exported GHCR corpus"]
fn lifted_starrayspread_carries_dst_index_and_src() {
    let data = std::fs::read(call_shapes_fixture()).expect("call-shapes fixture");
    let file = decode(&data).expect("decode call-shapes fixture");
    let module = lift_file(&file).expect("lift call-shapes fixture");

    let mut spreads = 0usize;
    for index in 0..module.functions.len() {
        let func = module.func(FuncId::from_index(index));
        for &bb in &func.blocks {
            let block = module.block(bb);
            for &inst_id in block.phis.iter().chain(block.insts.iter()) {
                let InstData::ArraySpread {
                    dst,
                    index: idx,
                    src,
                } = &module.inst(inst_id).data
                else {
                    continue;
                };
                spreads += 1;
                let def_of = |v: abcd_ir::entity::Value| match module.value(v).def {
                    ValueDef::Inst(def) => module.inst(def).data.clone(),
                    other => panic!("operand must be an instruction result, got {other:?}"),
                };
                assert!(
                    matches!(def_of(*dst), InstData::CreateEmptyArray),
                    "dst must be the createemptyarray value (vendor v1), got {:?}",
                    def_of(*dst)
                );
                assert!(
                    matches!(def_of(*idx), InstData::LiteralNumber(_)),
                    "index must be the integer start index (vendor v2)"
                );
                assert!(
                    matches!(def_of(*src), InstData::TryLoadGlobalByName { .. }),
                    "src must be the acc iterable (vendor acc: inout)"
                );
            }
        }
    }
    assert!(spreads > 0, "fixture must exercise starrayspread");
}
