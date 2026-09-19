//! N48 regression: ADCE must keep OBSERVABLE loads even when their
//! result is dead. Deleting a dead-result `o.p` drops a user getter
//! call (and the nullish-receiver TypeError); deleting a dead
//! `o.#x`/`#x in o` drops the private-brand check; deleting a dead
//! `CreateRegExp` drops the invalid-flags SyntaxError; deleting a dead
//! `LoadGlobalVar` drops the TDZ/"not defined" ReferenceError; deleting
//! a dead `GetIterator`/`GetAsyncIterator` skips the user @@iterator
//! call entirely.
//!
//! Vendored-property audit (the card's preferred source): the vendored
//! `abcd-isa-sys/vendor/isa/isa.yaml` has NO `can_throw` property at
//! all, and every instruction group declares `exceptions: x_none` —
//! including the groups holding getiterator (isa.yaml:401-416),
//! createregexpwithliteral (:466-525), ldglobalvar/ldobjbyname
//! (:1250-1513) — so essentiality CANNOT be derived from vendored yaml
//! properties. The hand list below is therefore the primary source,
//! backed by vendored RUNTIME evidence:
//!
//! - GetIterator/GetAsyncIterator: `RuntimeGetIterator` reads
//!   `@@iterator` and CALLS it via `EcmaInterpreter::Execute`
//!   (runtime_stubs-inl.h:1569-1582, :1584+; abrupt-checked).
//! - LoadProperty (`ldobjbyname`, interpreter_assembly.cpp:5543+):
//!   `GetProperty` invokes getters; nullish receivers throw TypeError.
//! - LoadPrivateProperty: getter call + `THROW_TYPE_ERROR_AND_RETURN
//!   "invalid or cannot find private key"` brand check
//!   (runtime_stubs-inl.h:1592-1620); TestPrivateProperty (`testin`,
//!   compiler/interpreter_stub.cpp:881-890) brand-checks the same way.
//! - CreateRegExp: `RuntimeCreateRegExpWithLiteral` →
//!   `BuiltinsRegExp::RegExpCreateWithRawFlags`
//!   (runtime_stubs-inl.h:2508-2513) validates pattern/flags.
//! - LoadGlobalVar (`ldglobalvar`,
//!   interpreter_assembly.cpp:2575-2614): fast path calls global
//!   getters (`CallGetter`, fast_runtime_stub-inl.h:224-225), slow path
//!   is abrupt-checked; global-record misses/TDZ raise ReferenceError
//!   (`RuntimeThrowReferenceError`, runtime_stubs-inl.h:1769-1779).

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::Inst;
use abcd_ir::inst::{BinOp, InstData, PropKind};
use abcd_ir::module::Module;
use abcd_ir::opt::FuncPass;
use abcd_ir::opt::dce::Adce;
use abcd_ir::types::IrType;

/// Build `f(p0) { <inst>; return; }` with `<inst>`'s result UNUSED, run
/// ADCE, and return whether `<inst>` survived.
fn inst_survives_adce(
    make: impl FnOnce(&mut IRBuilder, abcd_ir::entity::Value) -> InstData,
) -> bool {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 1);
    let inst_id;
    {
        let mut b = IRBuilder::new(&mut module, func);
        let p0 = b.create_func_param(0, IrType::default());
        let data = make(&mut b, p0);
        let (id, _dead_result) = b.emit(data, IrType::default());
        inst_id = id;
        b.emit_void(InstData::Return { value: None });
    }
    Adce.run(&mut module, func);
    module.func(func).blocks.iter().any(|&bb| {
        module.block(bb).insts.contains(&inst_id) || module.block(bb).phis.contains(&inst_id)
    })
}

/// N48 red pins: every observable load in the hand list must be kept.
#[test]
fn adce_keeps_observable_loads_with_dead_results() {
    let cases: Vec<(
        &str,
        Box<dyn FnOnce(&mut IRBuilder, abcd_ir::entity::Value) -> InstData>,
    )> = vec![
        (
            "GetIterator (user @@iterator call)",
            Box::new(|_m, p0| InstData::GetIterator { obj: p0 }),
        ),
        (
            "GetAsyncIterator (user @@asyncIterator call)",
            Box::new(|_m, p0| InstData::GetAsyncIterator { obj: p0 }),
        ),
        (
            "LoadProperty (getters + nullish TypeError)",
            Box::new(|m, p0| InstData::LoadProperty {
                object: p0,
                key: PropKind::ByName(m.intern("p")),
            }),
        ),
        (
            "LoadPrivateProperty (brand check)",
            Box::new(|_m, p0| InstData::LoadPrivateProperty {
                level: 0,
                slot: 0,
                obj: p0,
            }),
        ),
        (
            "TestPrivateProperty (brand check)",
            Box::new(|_m, p0| InstData::TestPrivateProperty {
                level: 0,
                slot: 0,
                obj: p0,
            }),
        ),
        (
            "CreateRegExp (invalid-flags SyntaxError)",
            Box::new(|m, _p0| {
                let pattern = m.intern("a");
                let flags = m.intern("g");
                InstData::CreateRegExp { pattern, flags }
            }),
        ),
        (
            "LoadGlobalVar (TDZ ReferenceError)",
            Box::new(|m, _p0| InstData::LoadGlobalVar {
                name: m.intern("x"),
            }),
        ),
    ];
    let mut deleted = Vec::new();
    for (name, make) in cases {
        if !inst_survives_adce(make) {
            deleted.push(name);
        }
    }
    assert!(
        deleted.is_empty(),
        "ADCE deleted observable loads with dead results (N48): {deleted:?}"
    );
}

/// Control: a genuinely PURE computation with a dead result must still
/// be eliminated (the essentiality widening must not neuter ADCE).
#[test]
fn adce_still_deletes_pure_dead_computations() {
    let survives = inst_survives_adce(|_m, p0| InstData::BinaryOp {
        op: BinOp::Add,
        left: p0,
        right: p0,
    });
    assert!(!survives, "dead-result pure binop must still be swept");
}

/// Control: the dead load's OPERAND must not keep anything alive by
/// itself — the load is kept for its own side effect, and a pure
/// operand producer stays dead if ITS result feeds only the load...
/// no: the load is live, so its operand chain is live. Pin the chain
/// propagation instead: the operand's producer must survive too.
#[test]
fn adce_keeps_operand_chain_of_observable_load() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let producer: Inst;
    {
        let mut b = IRBuilder::new(&mut module, func);
        let lit = b.emit_val(InstData::LiteralNumber(1.0), IrType::default());
        let (prod, obj) = b.emit(
            InstData::UnaryOp {
                op: abcd_ir::inst::UnOp::Minus,
                operand: lit,
            },
            IrType::default(),
        );
        producer = prod;
        let _dead = b.emit_val(
            InstData::GetIterator { obj: obj.unwrap() },
            IrType::default(),
        );
        b.emit_void(InstData::Return { value: None });
    }
    Adce.run(&mut module, func);
    let entry = module.func(func).entry_block;
    assert!(
        module.block(entry).insts.contains(&producer),
        "operand producer of a live observable load must survive"
    );
}
