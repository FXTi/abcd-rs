//! N30 regression (P3-T21): `gettemplateobject` must round-trip as its
//! own instruction, not collapse into `LoadProperty(obj, 0)`.
//!
//! Vendor facts:
//! - `gettemplateobject imm:u16, acc: inout:top`
//!   (abcd-isa-sys/vendor/isa/isa.yaml:1279-1283, properties
//!   `[ic_slot, one_slot, eight_sixteen_bit_ic]` — ONE IC slot): the
//!   acc carries the template literal, the (cached) template object is
//!   written back to acc (`SlowRuntimeStub::GetTemplateObject(thread,
//!   literal)` + `SET_ACC`, arkcompiler_ets_runtime-master/ecmascript/
//!   interpreter/interpreter_assembly.cpp:2071-2083).
//! - `deprecated.gettemplateobject v:in:top, acc: inout:top`
//!   (isa.yaml:1284-1288): the template literal comes from the register
//!   operand instead.
//! - Corpus corroboration (exports/corpus/9.0.0.0/local/template/
//!   baseline/reference.pa:67): `gettemplateobject 0x16`.
//!
//! Pre-N30 the lift modeled both arms as `LoadProperty { object: acc,
//! key: ByIndex(0) }` — an element read, not a template-object
//! materialization — so lowering emitted `ldobjbyindex` where the
//! source had `gettemplateobject` (template x18 failures).

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

fn template_fixture() -> std::path::PathBuf {
    corpus_root().join("9.0.0.0/local/template/baseline/input.abc")
}

/// Opcode-for-opcode round-trip: the lowered stream must contain
/// `gettemplateobject` exactly as many times as the source (pre-N30:
/// zero — every one came back as `ldobjbyindex`).
#[test]
#[ignore = "requires exported GHCR corpus"]
fn lowered_template_fixture_preserves_gettemplateobject() {
    let data = std::fs::read(template_fixture()).expect("template fixture");
    let file = decode(&data).expect("decode template fixture");
    let mut src_gettpl = 0usize;
    for (_, method) in file.all_methods() {
        if let Some(body) = &method.body {
            for bc in &body.bytecodes {
                if matches!(bc, Bytecode::Gettemplateobject(..)) {
                    src_gettpl += 1;
                }
            }
        }
    }
    assert!(src_gettpl > 0, "fixture must exercise gettemplateobject");

    let module = lift_file(&file).expect("lift template fixture");
    assert!(verify_module(&module).is_empty());

    let mut out_gettpl = 0usize;
    for index in 0..module.functions.len() {
        let lowered = lower_function(&module, FuncId::from_index(index))
            .expect("template fixture must lower");
        for bc in &lowered.bytecodes {
            if matches!(bc, Bytecode::Gettemplateobject(..)) {
                out_gettpl += 1;
            }
        }
    }
    assert_eq!(
        out_gettpl, src_gettpl,
        "every source gettemplateobject must lower back to \
         gettemplateobject (not ldobjbyindex)"
    );
}
