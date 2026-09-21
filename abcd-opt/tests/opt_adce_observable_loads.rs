//! N48/N50 regression (v0.2 port of v0.1 `opt_adce_observable_loads.rs`):
//! ADCE must keep OBSERVABLE loads even when their result is dead.
//! Deleting a dead-result `o.p` drops a user getter call (and the
//! nullish-receiver TypeError); deleting a dead `o.#x`/`#x in o` drops
//! the private-brand check; deleting a dead `AllocRegExp` drops the
//! invalid-flags SyntaxError; deleting a dead global load drops the
//! getter call / ReferenceError; deleting a dead
//! `GetIterator`/`GetAsyncIterator` skips the user @@iterator call
//! entirely.
//!
//! v0.2 difference: essentiality is not a hand list in the pass — it is
//! DERIVED from the T3 effects table (`Op::effects`,
//! design/ir-v0.2.md §4.4): write / may-throw / may-call effects make an
//! op essential. These tests pin the end-to-end behavior (dead-result
//! observable loads survive ADCE); the table-level coverage pin lives in
//! abcd-ir's effects tests (`effects_cover_v0_1_observable_loads`).
//!
//! Vendored runtime evidence (unchanged from v0.1):
//!
//! - GetIterator/GetAsyncIterator: `RuntimeGetIterator` reads
//!   `@@iterator` and CALLS it via `EcmaInterpreter::Execute`
//!   (runtime_stubs-inl.h:1569-1582, :1584+; abrupt-checked).
//! - LoadProp (`ldobjbyname`, interpreter_assembly.cpp:5543+):
//!   `GetProperty` invokes getters; nullish receivers throw TypeError.
//! - LoadPrivate: getter call + `THROW_TYPE_ERROR_AND_RETURN
//!   "invalid or cannot find private key"` brand check
//!   (runtime_stubs-inl.h:1592-1620); TestPrivate (`testin`,
//!   compiler/interpreter_stub.cpp:881-890) brand-checks the same way.
//! - AllocRegExp: `RuntimeCreateRegExpWithLiteral` →
//!   `BuiltinsRegExp::RegExpCreateWithRawFlags`
//!   (runtime_stubs-inl.h:2508-2513) validates pattern/flags.
//! - TryGetGlobal (both forms): the slow paths run `GetProperty` on the
//!   global's prototype chain — global getters are CALLED and the calls
//!   are abrupt-checked (`RuntimeLdGlobalVarFromProto`,
//!   runtime_stubs-inl.h:1782-1793; `RuntimeTryLdGlobalByName`,
//!   :1739-1748 — the try form also raises ReferenceError " is not
//!   defined" on a miss).
//! - LoadSuper: `RuntimeStubs::RuntimeLdSuperByValue`
//!   (stubs/runtime_stubs-inl.h:681-697) — `GetSuperBase` /
//!   `RequireObjectCoercible` / `ToPropertyKey` are abrupt-checked and
//!   the final `GetProperty(superBase, key, receiver)` CALLS super
//!   getters.

mod common;

use abcd_ir::verify_module;
use abcd_ir::{BinOp, Const, FunctionKind, Module, Op, SuperKey, UnOp, ValueId};
use abcd_opt::FuncPass;
use abcd_opt::dce::Adce;

use common::V2Builder;

/// Build `f(p0) { <inst>; return; }` with `<inst>`'s result UNUSED, run
/// ADCE, and return whether `<inst>` survived.
fn inst_survives_adce(make: impl FnOnce(&mut V2Builder, ValueId) -> Op) -> bool {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let inst_id;
    {
        let mut b = V2Builder::new(&mut module, func);
        let p0 = b.create_param();
        let op = make(&mut b, p0);
        let (id, _dead_result) = b.emit(op);
        inst_id = id;
        b.emit_void(Op::Return { value: None });
    }
    Adce.run(&mut module, func);
    module.functions[func.index()]
        .blocks
        .iter()
        .any(|&bb| module.blocks[bb.index()].insts.contains(&inst_id))
}

/// N48 red pins: every observable load in the list must be kept.
#[test]
fn adce_keeps_observable_loads_with_dead_results() {
    let cases: Vec<(&str, Box<dyn FnOnce(&mut V2Builder, ValueId) -> Op>)> = vec![
        (
            "GetIterator (user @@iterator call)",
            Box::new(|_b, p0| Op::GetIterator { obj: p0 }),
        ),
        (
            "GetAsyncIterator (user @@asyncIterator call)",
            Box::new(|_b, p0| Op::GetAsyncIterator { obj: p0 }),
        ),
        (
            "LoadProp (getters + nullish TypeError)",
            Box::new(|b, p0| Op::LoadProp {
                object: p0,
                name: b.sym("p"),
            }),
        ),
        (
            "LoadPrivate (brand check)",
            Box::new(|_b, p0| Op::LoadPrivate {
                level: 0,
                slot: 0,
                obj: p0,
            }),
        ),
        (
            "TestPrivate (brand check)",
            Box::new(|_b, p0| Op::TestPrivate {
                level: 0,
                slot: 0,
                obj: p0,
            }),
        ),
        (
            "AllocRegExp (invalid-flags SyntaxError)",
            Box::new(|b, _p0| Op::AllocRegExp {
                pattern: b.sym("a"),
                flags: 1, // 'g'
            }),
        ),
        (
            "TryGetGlobal default:None (v0.1 LoadGlobalVar — getter call)",
            Box::new(|b, _p0| Op::TryGetGlobal {
                name: b.sym("x"),
                default: None,
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

/// N50 red pins: the two global/super load forms the N48 list missed.
#[test]
fn adce_keeps_n50_observable_loads_with_dead_results() {
    let cases: Vec<(&str, Box<dyn FnOnce(&mut V2Builder, ValueId) -> Op>)> = vec![
        (
            "TryGetGlobal default:Some (v0.1 TryLoadGlobalByName — proto getters)",
            Box::new(|b, _p0| {
                let default = b.create_const_value(Const::Undefined);
                Op::TryGetGlobal {
                    name: b.sym("missing_global"),
                    default: Some(default),
                }
            }),
        ),
        (
            "LoadSuper (super getter call)",
            Box::new(|b, _p0| Op::LoadSuper {
                key: SuperKey::Name(b.sym("p")),
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
        "ADCE deleted observable loads with dead results (N50): {deleted:?}"
    );
}

/// Control: a genuinely PURE computation with a dead result must still
/// be eliminated (the effects-derived essentiality must not neuter ADCE).
#[test]
fn adce_still_deletes_pure_dead_computations() {
    let survives = inst_survives_adce(|_b, p0| Op::BinaryOp {
        op: BinOp::Add,
        left: p0,
        right: p0,
    });
    assert!(!survives, "dead-result pure binop must still be swept");
}

/// Control: the dead load's OPERAND chain stays alive through the load —
/// the operand's producer must survive too.
#[test]
fn adce_keeps_operand_chain_of_observable_load() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let producer;
    {
        let mut b = V2Builder::new(&mut module, func);
        let lit = b.emit_number(1.0);
        let (prod, obj) = b.emit(Op::UnaryOp {
            op: UnOp::Minus,
            operand: lit,
        });
        producer = prod;
        let _dead = b.emit_val(Op::GetIterator {
            obj: obj.expect("unop result"),
        });
        b.emit_void(Op::Return { value: None });
    }
    Adce.run(&mut module, func);
    let entry = module.functions[func.index()].blocks[0];
    assert!(
        module.blocks[entry.index()].insts.contains(&producer),
        "operand producer of a live observable load must survive"
    );
}

/// Pure reads and pure allocations with dead results stay dead-deletable
/// (v0.1 parity — they were NOT on the v0.1 essential list).
#[test]
fn adce_still_deletes_pure_reads_and_allocs() {
    let cases: Vec<(&str, Box<dyn FnOnce(&mut V2Builder, ValueId) -> Op>)> = vec![
        (
            "GetLexVar",
            Box::new(|_b, _p0| Op::GetLexVar { level: 0, slot: 0 }),
        ),
        (
            "LoadModuleVar",
            Box::new(|_b, _p0| Op::LoadModuleVar { index: 0 }),
        ),
        (
            "AllocObject",
            Box::new(|b, _p0| Op::AllocObject {
                shape: b.konst(Const::ObjectLiteral {
                    keys: vec![],
                    values: vec![],
                }),
            }),
        ),
        (
            "AllocArray (empty)",
            Box::new(|_b, _p0| Op::AllocArray { shape: None }),
        ),
        (
            "GetPropIterator",
            Box::new(|_b, p0| Op::GetPropIterator { obj: p0 }),
        ),
    ];
    let mut kept = Vec::new();
    for (name, make) in cases {
        if inst_survives_adce(make) {
            kept.push(name);
        }
    }
    assert!(
        kept.is_empty(),
        "pure reads/allocs with dead results must still be swept (v0.1 parity): {kept:?}"
    );
}

/// Post-ADCE modules stay verifier-clean (N27/N28 hygiene).
#[test]
fn adce_output_verifies() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p0 = b.create_param();
        let lit = b.emit_number(41.0);
        let one = b.emit_number(1.0);
        let sum = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: lit,
            right: one,
        });
        let _dead = b.emit_val(Op::GetIterator { obj: p0 });
        b.emit_void(Op::Return { value: Some(sum) });
    }
    Adce.run(&mut module, func);
    let report = verify_module(&module);
    assert!(report.is_ok(), "post-ADCE verify: {:?}", report.errors);
}
