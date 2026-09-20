//! N18 dead-island sweep (Phase 5).
//!
//! es2abc emits unreachable bytecode (dead code after unconditional control
//! flow, dead catch bodies). Lift faithfully materialized those islands as
//! blocks reading frame-initial values (P3-T7) — junk that lowering lays
//! out and emits, and whose preds/phi entries perturb regalloc and the
//! optimizer. Lift now sweeps blocks unreachable from the entry under the
//! AUGMENTED successor relation (terminator edges + try→handler exception
//! edges, `analysis::augmented_succs`) — the same model opt's
//! `remove_unreachable_blocks` and verify's N27 rule use.
//!
//! Rule note: a plain terminator-only sweep would mark every catch handler
//! (and all code downstream of it) unreachable and delete LIVE catch
//! bodies; the second test pins that handler-downstream code survives.

mod common;

use abcd_file::{AccessFlags, Builder, CatchBlockDef, File, Type};
use abcd_ir::entity::FuncId;
use abcd_ir::lift::lift_file;
use abcd_ir::module::Module;
use abcd_ir::verify::verify_module;
use abcd_isa::{Bytecode, Label, encode as encode_bytecodes};

/// Build a 12.x file whose global class carries one static method `f` with
/// the given bytecodes and one catch-all try region (instruction indices;
/// the handler range extends to the end of the code).
fn build_file(bytecodes: &[Bytecode], try_range: Option<(u32, u32, u32)>) -> File {
    let mut builder = Builder::new();
    builder.set_api(12, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let (code, offsets) = encode_bytecodes(bytecodes).unwrap();
    let code_h = builder.create_code(&code, 4, 0);
    if let Some((try_start, try_end, handler)) = try_range {
        builder.code_add_try_block(
            code_h,
            offsets[try_start as usize],
            offsets[try_end as usize] - offsets[try_start as usize],
            &[CatchBlockDef {
                type_class: None, // catch-all
                handler_pc: offsets[handler as usize],
                code_size: code.len() as u32 - offsets[handler as usize],
            }],
        );
    }
    let m = builder.class_add_method(class, "f", proto, AccessFlags::STATIC, &code, 4, 0);
    builder.method_set_code(m, code_h);
    abcd_file::decode(&builder.finalize().unwrap()).unwrap()
}

fn func_by_name(module: &Module, name: &str) -> FuncId {
    (0..module.functions.len())
        .map(FuncId::from_index)
        .find(|&f| module.strings.get(module.func(f).name) == name)
        .unwrap_or_else(|| panic!("function {name}"))
}

/// A completely dead try/catch island after an unconditional return is
/// swept: the dead try body (pred-less) and its dead handler (exception
/// dispatch can never fire from a dead protected range) both go.
#[test]
fn dead_try_island_is_swept() {
    let bytecodes = vec![
        Bytecode::Ldundefined,     // 0
        Bytecode::Returnundefined, // 1 -- everything below is dead
        Bytecode::Ldnull,          // 2 dead try body
        Bytecode::Throw,           // 3
        Bytecode::Ldtrue,          // 4 dead catch handler
        Bytecode::Returnundefined, // 5
    ];
    let file = build_file(&bytecodes, Some((2, 4, 4)));
    let module = lift_file(&file).unwrap();
    let func = module.func(func_by_name(&module, "f"));
    assert_eq!(
        func.blocks.len(),
        1,
        "dead island must be swept, leaving only the entry block: {:?}",
        func.blocks
    );
    assert!(
        func.try_regions.is_empty(),
        "the dead try region must be pruned with its island"
    );
    assert!(
        func.exception_values.is_empty(),
        "the dead handler's exception value must be pruned"
    );
    let errors = verify_module(&module);
    assert!(errors.is_empty(), "verify after sweep: {errors:?}");
}

/// A LIVE try/catch whose handler (and the code reachable only through
/// the handler) has no terminator path from the entry must survive
/// whole: handlers are reached by exception dispatch, not terminators.
#[test]
fn live_handler_and_handler_downstream_survive() {
    let bytecodes = vec![
        Bytecode::Ldtrue,          // 0 A
        Bytecode::Jeqz(Label(8)),  // 1 A -> F / fallthrough B
        Bytecode::Ldnull,          // 2 B (try body)
        Bytecode::Throw,           // 3 B
        Bytecode::Jeqz(Label(6)),  // 4 C (handler) -> E / fallthrough D
        Bytecode::Returnundefined, // 5 D
        Bytecode::Ldnull,          // 6 E (reachable ONLY via the handler)
        Bytecode::Returnundefined, // 7 E
        Bytecode::Ldtrue,          // 8 F (merge)
        Bytecode::Returnundefined, // 9 F
    ];
    let file = build_file(&bytecodes, Some((2, 4, 4)));
    let module = lift_file(&file).unwrap();
    let func = module.func(func_by_name(&module, "f"));
    assert_eq!(
        func.blocks.len(),
        6,
        "every block is live: the sweep must keep handlers and \
         handler-downstream code: {:?}",
        func.blocks
    );
    assert_eq!(func.try_regions.len(), 1);
    assert_eq!(func.exception_values.len(), 1);
    let errors = verify_module(&module);
    assert!(errors.is_empty(), "verify after sweep: {errors:?}");
}
