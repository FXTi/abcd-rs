//! N32 regression (P3-T21): the acc↔v2 (value↔key) permutation shared
//! by isel's `StoreProperty::ByValue` arm and lift's
//! `Stobjbyvalue`/`Stthisbyvalue` arms must follow the VENDOR
//! convention at BOTH ends.
//!
//! Vendor facts:
//! - `stobjbyvalue imm:u16, v1:in:top, v2:in:top, acc: in:top`
//!   (abcd-isa-sys/vendor/isa/isa.yaml:1353-1357): v1 is the RECEIVER,
//!   v2 the PROPERTY KEY, the accumulator the VALUE —
//!   `receiver = GET_VREG_VALUE(v0)`, `propKey = GET_VREG_VALUE(v1)`,
//!   `value = GET_ACC()` (arkcompiler_ets_runtime-master/ecmascript/
//!   interpreter/interpreter_assembly.cpp:2306-2335,
//!   HandleStobjbyvalueImm16V8V8).
//! - `stthisbyvalue imm:u16, v:in:top, acc: in:top`
//!   (isa.yaml:1642-1646): same convention with `this` as receiver —
//!   `propKey = GET_VREG_VALUE(v0)`, `value = GET_ACC()`
//!   (interpreter_assembly.cpp:6195-6257, HandleStthisbyvalueImm16V8).
//! - Corpus corroboration (exports/corpus/9.0.0.0/local/array-index/
//!   baseline/reference.pa:30-33):
//!
//! ```text
//! ldai 0x1
//! sta v6                      # v6 = index 1 (the KEY)
//! ldai 0x8                    # acc = 8 (the VALUE)
//! stobjbyvalue 0x3, v5, v6    # receiver = v5, key = v6, value = acc
//! ```
//!
//! Pre-N32 the lift bound `key = acc` / `value = v2` and the isel
//! emitted `Stobjbyvalue(obj, value)` with the key in acc — the SAME
//! permutation at both ends, byte-transparent in the round-trip but an
//! IR-level lie: the optimizer saw key and value swapped, and any
//! single-ended use (N31's starrayspread modeling) exploded.

use abcd_file::decode;
use abcd_ir::entity::FuncId;
use abcd_ir::inst::{InstData, PropKind};
use abcd_ir::lift::lift_file;
use abcd_ir::module::ValueDef;
use abcd_ir::verify::verify_module;

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

fn array_index_fixture() -> std::path::PathBuf {
    corpus_root().join("9.0.0.0/local/array-index/baseline/input.abc")
}

/// The lifted `StoreProperty` for `stobjbyvalue` must bind key = the
/// v2 register content (the index 1) and value = the acc content (8),
/// per the vendor convention. Pre-N32 both were swapped.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn stobjbyvalue_binds_key_from_register_and_value_from_acc() {
    let data = std::fs::read(array_index_fixture()).expect("array-index fixture");
    let file = decode(&data).expect("decode array-index fixture");
    let module = lift_file(&file).expect("lift array-index fixture");
    assert!(verify_module(&module).is_empty());

    let mut stores = 0usize;
    for index in 0..module.functions.len() {
        let func = module.func(FuncId::from_index(index));
        for &bb in &func.blocks {
            let block = module.block(bb);
            for &inst_id in block.phis.iter().chain(block.insts.iter()) {
                let InstData::StoreProperty {
                    key: PropKind::ByValue(key),
                    value,
                    ..
                } = &module.inst(inst_id).data
                else {
                    continue;
                };
                stores += 1;
                let def_of = |v: abcd_ir::entity::Value| match module.value(v).def {
                    ValueDef::Inst(def) => module.inst(def).data.clone(),
                    other => panic!("operand must be an instruction result, got {other:?}"),
                };
                assert!(
                    matches!(def_of(*key), InstData::LiteralNumber(n) if n == 1.0),
                    "key must be the v2 register content (index 1, vendor \
                     v2 = propKey), got {:?}",
                    def_of(*key)
                );
                assert!(
                    matches!(def_of(*value), InstData::LiteralNumber(n) if n == 8.0),
                    "value must be the acc content (8, vendor acc = \
                     value), got {:?}",
                    def_of(*value)
                );
            }
        }
    }
    assert!(stores > 0, "fixture must exercise stobjbyvalue");
}
