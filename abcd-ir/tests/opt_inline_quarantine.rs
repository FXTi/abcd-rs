//! N44 quarantine (P4-T3): opt::inline produces module-INVALID IR — the
//! P4-T2 review red-proved on a trivial caller/callee shape that the
//! inliner leaves callee parameters unmapped, does not rebuild block
//! predecessors, leaves stale per-instruction block fields, and drops
//! try-regions (4 structural verifier errors on one inline). The pass was
//! never in the default pipeline (opt/mod.rs `optimize_func`), so the
//! honest treatment is quarantine, not a rushed rewrite: `Inline::run`
//! is hard-gated to a no-op until a v0.2-era rewrite decision.
//!
//! This test pins the quarantine: on the exact probe shape that used to
//! corrupt the module, running the pass must change NOTHING — no IR
//! modification (`run` returns false), identical instruction count, the
//! call site intact, and the module still verifies clean.

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::inst::{CallKind, InstData};
use abcd_ir::module::Module;
use abcd_ir::opt::FuncPass;
use abcd_ir::opt::inline::Inline;
use abcd_ir::types::IrType;
use abcd_ir::verify::verify_module;

/// The P4-T2 probe shape: caller `f` calls small same-module callee `g`
/// (resolved through DefineFunc method_offset identity, S1/N2-era).
fn build_inline_probe() -> (Module, abcd_ir::entity::FuncId, abcd_ir::entity::Inst) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);

    // Callee g: tiny body `return 42`, source offset set so the inliner's
    // offset-keyed callee resolution matches it.
    let g = IRBuilder::create_function(&mut module, "g", FunctionKind::Function, 0);
    module.func_mut(g).source_offset = Some(0x100);
    {
        let mut builder = IRBuilder::new(&mut module, g);
        let lit = builder.emit_val(InstData::LiteralNumber(42.0), IrType::default());
        builder.emit_void(InstData::Return { value: Some(lit) });
    }

    // Caller f: `%callee = DefineFunc(g); %r = call %callee(); return %r`.
    let g_name = module.strings.intern("g");
    let f = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let call_inst;
    {
        let mut builder = IRBuilder::new(&mut module, f);
        let callee = builder.emit_val(
            InstData::DefineFunc {
                method_id: g_name,
                method_offset: 0x100,
                length: 0,
            },
            IrType::default(),
        );
        let (inst, result) = builder.emit(
            InstData::Call {
                kind: CallKind::Call,
                callee,
                args: Vec::new(),
            },
            IrType::default(),
        );
        call_inst = inst;
        builder.emit_void(InstData::Return { value: result });
    }
    (module, f, call_inst)
}

#[test]
fn inline_is_quarantined_noop() {
    let (mut module, f, call_inst) = build_inline_probe();

    let pre_errors = verify_module(&module);
    assert!(
        pre_errors.is_empty(),
        "probe module must verify before the pass: {pre_errors:?}"
    );
    let inst_count_before = module.insts.len();

    let changed = Inline::new(50).run(&mut module, f);

    assert!(
        !changed,
        "N44 quarantine: Inline::run must be a no-op (it reported a change)"
    );
    assert_eq!(
        module.insts.len(),
        inst_count_before,
        "N44 quarantine: instruction arena must be untouched"
    );
    match &module.inst(call_inst).data {
        InstData::Call { .. } => {}
        other => panic!("N44 quarantine: call site must survive, got {other:?}"),
    }
    let post_errors = verify_module(&module);
    assert!(
        post_errors.is_empty(),
        "N44 quarantine: module must still verify after the pass: {post_errors:?}"
    );
}
