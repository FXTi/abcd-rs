//! N34 regression (P3-T21): the private-property instruction family
//! must round-trip as its own instructions, not collapse into
//! ByIndex(0) property access or be dropped.
//!
//! Vendor facts (abcd-isa-sys/vendor/isa/isa.yaml;
//! arkcompiler_ets_runtime-master/ecmascript/compiler/interpreter_stub.cpp):
//! - `ldprivateproperty imm1:u8, imm2:u16, imm3:u16, acc: inout:top`
//!   (isa.yaml:436-440): imm1 = IC slot, imm2 = level, imm3 = slot;
//!   acc in = the OBJECT, acc out = the private value
//!   (`RTSTUB_ID(LdPrivateProperty){currentEnv, level, slot, obj=acc}`,
//!   interpreter_stub.cpp:853-867).
//! - `stprivateproperty imm1:u8, imm2:u16, imm3:u16, v:in:top,
//!   acc: in:top` (isa.yaml:441-445): obj = the REGISTER operand,
//!   value = acc (interpreter_stub.cpp:869-879).
//! - `testin imm1:u8, imm2:u16, imm3:u16, acc: inout:top`
//!   (isa.yaml:446-450): acc in = obj, acc out = boolean
//!   (interpreter_stub.cpp:881-890).
//! - `callruntime.defineprivateproperty imm1:u8, imm2:u16, imm3:u16,
//!   v:in:top, acc: in:top` (isa.yaml:849-854): obj = REGISTER, value =
//!   acc (interpreter_stub.cpp:6079-6091).
//! - `callruntime.createprivateproperty imm:u16, literalarray_id,
//!   acc: none` (isa.yaml:843-848): registers `count` private names
//!   from the literal array in the current environment
//!   (interpreter_stub.cpp:6066-6077) — VOID, but observable: without
//!   it the names are never registered.
//! - Corpus corroboration (exports/corpus/24.0.0.0/local/private-field/
//!   baseline/reference.pa:55,69,94): one `ldprivateproperty`, one
//!   `callruntime.defineprivateproperty`, one
//!   `callruntime.createprivateproperty`.
//!
//! Pre-N34 the lift dropped `createprivateproperty` outright and
//! collapsed ld/st/define/testin into LoadProperty/StoreProperty with
//! a SYNTHETIC `ByIndex(level << 16 | slot)` key — plus obj/value
//! swapped for st/define vs the vendor — so lowering emitted
//! `ldobjbyindex`/`stownbyindex` and the private-name registration
//! vanished (private-field x3 failures).

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

fn private_field_fixture() -> std::path::PathBuf {
    corpus_root().join("24.0.0.0/local/private-field/baseline/input.abc")
}

/// Opcode-for-opcode round-trip across the whole private-property
/// family: the lowered stream must contain exactly the source's counts
/// of each opcode (pre-N34: 0/0/0 for the three exercised ones).
#[test]
#[ignore = "requires exported GHCR corpus"]
fn lowered_private_field_fixture_preserves_the_family() {
    let data = std::fs::read(private_field_fixture()).expect("private-field fixture");
    let file = decode(&data).expect("decode private-field fixture");

    fn counts<'a>(bytecodes: impl Iterator<Item = &'a Bytecode>) -> [usize; 5] {
        let mut c = [0usize; 5];
        for bc in bytecodes {
            match bc {
                Bytecode::Ldprivateproperty(..) => c[0] += 1,
                Bytecode::Stprivateproperty(..) => c[1] += 1,
                Bytecode::Testin(..) => c[2] += 1,
                Bytecode::CallruntimeDefineprivateproperty(..) => c[3] += 1,
                Bytecode::CallruntimeCreateprivateproperty(..) => c[4] += 1,
                _ => {}
            }
        }
        c
    }

    let mut src = [0usize; 5];
    for (_, method) in file.all_methods() {
        if let Some(body) = &method.body {
            for (i, n) in src.iter_mut().enumerate() {
                *n += counts(body.bytecodes.iter())[i];
            }
        }
    }
    assert_eq!(
        src,
        [1, 0, 0, 1, 1],
        "fixture shape changed — update the test expectation"
    );

    let module = lift_file(&file).expect("lift private-field fixture");
    assert!(verify_module(&module).is_empty());

    let mut out = [0usize; 5];
    for index in 0..module.functions.len() {
        let lowered = lower_function(&module, FuncId::from_index(index))
            .expect("private-field fixture must lower");
        for (i, n) in out.iter_mut().enumerate() {
            *n += counts(lowered.bytecodes.iter())[i];
        }
    }
    assert_eq!(
        out, src,
        "every private-property opcode must round-trip (ld/st/testin/\
         define/create) — createprivateproperty must not be dropped and \
         ld/define must not collapse into ByIndex property access"
    );
}
