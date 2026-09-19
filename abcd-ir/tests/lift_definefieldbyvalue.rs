//! N29 regression (P3-T21): `callruntime.definefieldbyvalue`'s two
//! register operands must bind propKey (v1) and obj (v2) in the VENDOR
//! order, not swapped.
//!
//! Vendor facts:
//! - `callruntime.definefieldbyvalue imm:u8, v1:in:top, v2:in:top,
//!   acc: in:top` (abcd-isa-sys/vendor/isa/isa.yaml:826-831).
//! - The stub reads `obj = GetVregValue(v1)` from the SECOND register
//!   operand and `propKey` from the FIRST, with the acc as value:
//!   `HandleCallRuntimeDefineFieldByValuePrefImm8V8V8`
//!   (arkcompiler_ets_runtime-master/ecmascript/compiler/
//!   interpreter_stub.cpp:6031-6043: `v0 = ReadInst8_2(pc)` → propKey,
//!   `v1 = ReadInst8_3(pc)` → obj, `DefineField(glue, obj, propKey, acc)`).
//! - Corpus corroboration (exports/corpus/9.0.0.0/local/tagged-template/
//!   baseline/reference.pa:34-39):
//!
//! ```text
//! ldai 0x0
//! sta v7                      # v7 = index 0 (the PROPERTY KEY)
//! lda.str "a"                 # acc = value
//! callruntime.definefieldbyvalue 0x6, v7, v8
//!                             # key = v7, obj = v8 (createemptyarray)
//! ```
//!
//! Pre-N29 the lift bound `obj = read_reg(first)`, `key =
//! read_reg(second)` — swapped vs the vendor — so the IR stored the
//! property on the KEY with the OBJECT as key; the lowered
//! `stownbyvalue` then called SetPropertyByValue(receiver=key,
//! propKey=obj) (tagged-template x18 'Cannot convert UNDEFINED to
//! JSObject').

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

fn tagged_template_fixture() -> std::path::PathBuf {
    corpus_root().join("9.0.0.0/local/tagged-template/baseline/input.abc")
}

/// Every `definefieldbyvalue` in the fixture defines an ELEMENT of a
/// `createemptyarray` array keyed by a small integer: the lifted
/// `StoreOwnProperty`'s `object` must be the array value (defined by
/// `CreateEmptyArray`), and the ByValue `key` must be the integer index
/// (defined by `LiteralNumber`). Pre-N29 both bindings were swapped.
#[test]
#[ignore = "requires exported GHCR corpus"]
fn definefieldbyvalue_binds_object_and_key_in_vendor_order() {
    let data = std::fs::read(tagged_template_fixture()).expect("tagged-template fixture");
    let file = decode(&data).expect("decode tagged-template fixture");
    let module = lift_file(&file).expect("lift tagged-template fixture");
    assert!(verify_module(&module).is_empty());

    let mut stores = 0usize;
    for index in 0..module.functions.len() {
        let func = module.func(FuncId::from_index(index));
        for &bb in &func.blocks {
            let block = module.block(bb);
            for &inst_id in block.phis.iter().chain(block.insts.iter()) {
                let InstData::StoreOwnProperty {
                    object,
                    key: PropKind::ByValue(key),
                    ..
                } = &module.inst(inst_id).data
                else {
                    continue;
                };
                stores += 1;
                let object_def = match module.value(*object).def {
                    ValueDef::Inst(def) => &module.inst(def).data,
                    other => panic!("object must be an instruction result, got {other:?}"),
                };
                let key_def = match module.value(*key).def {
                    ValueDef::Inst(def) => &module.inst(def).data,
                    other => panic!("key must be an instruction result, got {other:?}"),
                };
                assert!(
                    matches!(object_def, InstData::CreateEmptyArray),
                    "object must be the createemptyarray value (vendor v2 = \
                     obj), got {object_def:?}"
                );
                assert!(
                    matches!(key_def, InstData::LiteralNumber(_)),
                    "key must be the integer index (vendor v1 = propKey), \
                     got {key_def:?}"
                );
            }
        }
    }
    assert!(
        stores >= 4,
        "fixture must exercise definefieldbyvalue (found {stores})"
    );
}
