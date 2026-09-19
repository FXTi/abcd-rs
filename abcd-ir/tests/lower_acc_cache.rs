//! B4 regression (Phase 3 finale): the accumulator is a PHYSICAL
//! emission-time resource, not a coloring class ("acc-as-cache").
//!
//! Under the old acc-as-color model `RegSlot::Acc` claimed "this value
//! lives in the accumulator", but acc is ONE physical location: any
//! emitted `Lda`/acc-writing instruction destroys its content, and the
//! allocator never tracked those clobbers. An Acc-colored value used
//! after an intervening acc write read garbage — the live corpus evidence
//! was class-accessors lift ×18 ('TypeError: Constructor is false'),
//! generator baseline/debug ×12 (`ldfalse` clobbers the acc-held yield
//! value before its spill), and super-properties opt ×18 (B4 families,
//! 48 fixtures).
//!
//! The two `*_miscomputes_*` tests below are the crafted wrong-value
//! witnesses: under the old model the register allocator colors the
//! pinned victim value Acc (verified by hand-simulation of the MCS +
//! greedy ordering), an intervening literal definition or store clobbers
//! the physical acc, and the victim's later use silently reads the
//! clobbered content. They were RED before the acc-as-cache refactor
//! (the simulator observed the wrong value) and must stay GREEN after:
//! every value now has a register home, every acc-writing instruction
//! result with a use is homed by a `Sta`, and isel's emission-time acc
//! tracker reloads the home whenever the physical acc content is not
//! provably the requested value.
//!
//! The remaining tests pin the NEW contract: homing stores, cache-hit
//! `Lda` elision on def→use chains, and the block-entry meet rule.

mod common;

use std::collections::HashMap;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::StringId;
use abcd_ir::inst::{BinOp, InstData, PropKind, UnOp};
use abcd_ir::lower::regalloc::{self, RegSlot};
use abcd_ir::lower::{isel, lower_function};
use abcd_ir::module::{CatchHandler, Module, TryRegion};
use abcd_ir::types::IrType;
use abcd_isa::{Bytecode, EntityId};

use common::{Halt, Machine};

// ─── Red witness 1: class-accessors shape (definegettersetterbyvalue) ──────

/// The class-accessors B4 mechanism, reduced to four literals and the one
/// instruction that reads them:
///
/// ```text
/// k = 111   ; the "key"   — defined FIRST, used LAST
/// o = 222   ; the object
/// g = 333   ; the getter
/// s = 444   ; the setter
/// definegettersetterbyvalue(o, k, g, s)
/// ```
///
/// The four operands form an interference clique with equal acc-preference
/// scores, so the old MCS + greedy coloring handed the earliest-defined
/// operand `k` to the accumulator and registers to the rest. Each later
/// literal's `Sta` left ITS value in acc, so when the store instruction
/// spilled the "acc-resident" `k`, the spill captured 444 (the setter),
/// not 111 — the exact 'Constructor is false' chain pinned live on the
/// class-accessors corpus family. Under acc-as-cache every operand has a
/// register home and the define reads the homes: key must be 111.
#[test]
fn definegettersetter_operands_survive_intervening_acc_writes() {
    const K: i64 = 111;
    const O: i64 = 222;
    const G: i64 = 333;
    const S: i64 = 444;

    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "accessors", FunctionKind::Function, 0);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let k = builder.emit_val(InstData::LiteralNumber(111.0), IrType::default());
        let o = builder.emit_val(InstData::LiteralNumber(222.0), IrType::default());
        let g = builder.emit_val(InstData::LiteralNumber(333.0), IrType::default());
        let s = builder.emit_val(InstData::LiteralNumber(444.0), IrType::default());
        builder.emit_void(InstData::DefineGetterSetterByValue {
            obj: o,
            key: k,
            getter: g,
            setter: s,
        });
        builder.emit_void(InstData::Return { value: None });
    }

    let result = lower_function(&module, func).expect("accessors shape must lower");
    let halt = Machine::new().run(&result.bytecodes);
    let Halt::DefineGetterSetterByValue {
        obj,
        key,
        getter,
        setter,
    } = halt
    else {
        panic!(
            "expected execution to stop at definegettersetterbyvalue, got \
             {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(obj, O, "obj operand (bytecodes: {:?})", result.bytecodes);
    assert_eq!(
        key, K,
        "B4: the key operand must be its own literal; under acc-as-color \
         the acc-held key was clobbered by the setter's definition before \
         the spill (bytecodes: {:?})",
        result.bytecodes
    );
    assert_eq!(
        getter, G,
        "getter operand (bytecodes: {:?})",
        result.bytecodes
    );
    assert_eq!(
        setter, S,
        "setter operand (bytecodes: {:?})",
        result.bytecodes
    );
}

// ─── Red witness 2: generator shape (yield value vs ldfalse clobber) ───────

/// The generator B4 mechanism, reduced:
///
/// ```text
/// gen, obj = params
/// y = 777                                    ; the yield value
/// f = false
/// obj.x = f                                  ; StoreProperty ByName
/// suspendgenerator(gen, y)                   ; acc must be the yield value
/// ```
///
/// `f`'s use as the stored value keeps it Reg-colored (negative acc
/// score), so the old coloring gave `y` the accumulator — and the store's
/// `Lda(home f)` then destroyed the physical acc before
/// `suspendgenerator`'s "already in acc" no-op. The VM saw `false` as the
/// yield value (generator baseline/debug ×12). Under acc-as-cache the
/// store's acc load is tracked, so the suspend's `ensure_acc(y)` reloads
/// `y` from its home: the yield value must be 777.
#[test]
fn acc_held_yield_value_survives_clobber_before_suspend() {
    const GEN: i64 = 4242;
    const OBJ: i64 = 7777;
    const YIELD: i64 = 777;

    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "gen_fn", FunctionKind::Function, 2);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let genobj = builder.create_func_param(0, IrType::default());
        let obj = builder.create_func_param(1, IrType::default());
        let y = builder.emit_val(InstData::LiteralNumber(777.0), IrType::default());
        let f = builder.emit_val(InstData::LiteralBool(false), IrType::default());
        let name = builder.intern("x");
        builder.emit_void(InstData::StoreProperty {
            object: obj,
            key: PropKind::ByName(name),
            value: f,
        });
        builder.emit_void(InstData::SuspendGenerator { genobj, value: y });
        builder.emit_void(InstData::Return { value: None });
    }

    let result = lower_function(&module, func).expect("generator shape must lower");
    // Seed the ABI top slots (num_regs = frame; args sit above it) with the
    // gen/obj sentinels; the copy-in prologue moves them into the homes.
    let mut machine = Machine::new()
        .with_reg(result.num_regs, GEN)
        .with_reg(result.num_regs + 1, OBJ);
    let halt = machine.run(&result.bytecodes);
    let Halt::SuspendGenerator { genobj, value } = halt else {
        panic!(
            "expected execution to stop at suspendgenerator, got {halt:?} \
             (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(
        genobj, GEN,
        "genobj operand (bytecodes: {:?})",
        result.bytecodes
    );
    assert_eq!(
        value, YIELD,
        "B4: the acc at suspendgenerator must be the yield value; under \
         acc-as-color the intervening store's Lda clobbered the acc-held \
         yield value with false (bytecodes: {:?})",
        result.bytecodes
    );
}

// ─── New contract: homing stores + cache-hit elision ───────────────────────

/// Count bytecodes matching a predicate in a flat sequence.
fn count_matching(bytecodes: &[Bytecode], pred: impl Fn(&Bytecode) -> bool) -> usize {
    bytecodes.iter().filter(|bc| pred(bc)).count()
}

/// Every acc-writing instruction result that has a use is homed with a
/// `Sta` immediately after its definition, and the emission-time acc
/// tracker makes the very next acc use of that value a cache hit (no
/// `Lda`). A def→use chain of three acc-consuming instructions therefore
/// contains ZERO `Lda`:
///
/// ```text
/// a = 1
/// b = -a        ; ensure_acc(a): acc already holds a (just homed)
/// c = !b        ; ensure_acc(b): cache hit again
/// return c      ; ensure_acc(c): cache hit
/// ```
#[test]
fn def_use_chains_hit_the_acc_cache() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "chain", FunctionKind::Function, 0);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let a = builder.emit_val(InstData::LiteralNumber(1.0), IrType::default());
        let b = builder.emit_val(
            InstData::UnaryOp {
                op: UnOp::Minus,
                operand: a,
            },
            IrType::default(),
        );
        let c = builder.emit_val(
            InstData::UnaryOp {
                op: UnOp::LogicalNot,
                operand: b,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(c) });
    }

    let result = lower_function(&module, func).expect("chain must lower");
    assert_eq!(
        count_matching(&result.bytecodes, |bc| matches!(bc, Bytecode::Lda(_))),
        0,
        "every acc use in a def→use chain is a cache hit — no Lda at all \
         (bytecodes: {:?})",
        result.bytecodes
    );
    // And every used result was homed: a, b, c each got exactly one Sta.
    assert_eq!(
        count_matching(&result.bytecodes, |bc| matches!(bc, Bytecode::Sta(_))),
        3,
        "each used acc-writing result is homed with one Sta (bytecodes: {:?})",
        result.bytecodes
    );
}

/// A repeated acc use of the same value across acc-NON-writing
/// instructions (`stglobalvar` is vendor `acc: in:top`) stays a cache
/// hit: the first `ensure_acc` loads once, the second is a no-op.
#[test]
fn repeated_acc_use_across_non_clobbering_stores_loads_once() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "twice", FunctionKind::Function, 0);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let v = builder.emit_val(InstData::LiteralNumber(42.0), IrType::default());
        let a = builder.intern("a");
        let b = builder.intern("b");
        builder.emit_void(InstData::StoreGlobalVar { name: a, value: v });
        builder.emit_void(InstData::StoreGlobalVar { name: b, value: v });
        builder.emit_void(InstData::Return { value: None });
    }

    let result = lower_function(&module, func).expect("double store must lower");
    // v is homed right after its definition (Sta), the first store's
    // ensure_acc is a cache hit on that Sta, and stglobalvar does not
    // write acc — so the second store's ensure_acc hits too: zero Lda.
    assert_eq!(
        count_matching(&result.bytecodes, |bc| matches!(bc, Bytecode::Lda(_))),
        0,
        "stglobalvar does not clobber acc; both uses hit the cache \
         (bytecodes: {:?})",
        result.bytecodes
    );
}

// ─── New contract: block-entry meet rule ───────────────────────────────────

/// Select instructions with the REAL allocator and return the per-block
/// bytecodes keyed by block (easier meet-rule assertions than flat code).
fn select_blocks(
    module: &Module,
    func: abcd_ir::entity::FuncId,
) -> HashMap<abcd_ir::entity::Block, Vec<Bytecode>> {
    let alloc = regalloc::allocate(module, func).expect("allocation must succeed");
    let rpo = regalloc::compute_rpo(module, func);
    let string_map: HashMap<StringId, EntityId> = HashMap::new();
    isel::select(module, func, &alloc, &rpo, &string_map)
        .expect("selection must succeed")
        .block_codes
        .into_iter()
        .collect()
}

/// Single-predecessor propagation: a block whose only predecessor exits
/// with the acc provably holding value V enters with that knowledge, so
/// its first acc use of V emits NO `Lda`.
///
/// ```text
/// entry: a = 1; b = 2; jmp body      ; entry exit: acc holds b (homed)
/// body:  g = b                       ; ensure_acc(b): cache hit
/// ```
#[test]
fn single_predecessor_acc_content_propagates() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "prop", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;
    let body;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let _a = builder.emit_val(InstData::LiteralNumber(1.0), IrType::default());
        let b = builder.emit_val(InstData::LiteralNumber(2.0), IrType::default());
        body = builder.create_block();
        builder.add_predecessor(body, entry);
        builder.emit_void(InstData::Branch { dest: body });
        builder.set_insert_block(body);
        let g = builder.intern("g");
        builder.emit_void(InstData::StoreGlobalVar { name: g, value: b });
        builder.emit_void(InstData::Return { value: None });
    }

    let blocks = select_blocks(&module, func);
    let body_codes = &blocks[&body];
    assert_eq!(
        count_matching(body_codes, |bc| matches!(bc, Bytecode::Lda(_))),
        0,
        "the body's ensure_acc(b) must be a cache hit propagated from the \
         single predecessor (body bytecodes: {body_codes:?})"
    );
}

/// The meet over disagreeing predecessors is UNKNOWN: when two
/// predecessors exit with acc holding different values, the join's first
/// acc use must reload from the home (`Lda` present) — a stale meet would
/// read the wrong predecessor's content.
///
/// ```text
/// entry: w = 9; c = true; CondBranch(c, t, f)
/// t: g1 = w        ; exit: acc holds w
/// f: x = 3; g2 = x ; exit: acc holds x
/// join: g3 = w     ; meet(w, x) = unknown → Lda(home w) required
/// ```
#[test]
fn disagreeing_predecessors_force_a_reload_at_the_join() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "diamond", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;
    let (t, f, join);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let w = builder.emit_val(InstData::LiteralNumber(9.0), IrType::default());
        let c = builder.emit_val(InstData::LiteralBool(true), IrType::default());
        t = builder.create_block();
        f = builder.create_block();
        join = builder.create_block();
        builder.add_predecessor(t, entry);
        builder.add_predecessor(f, entry);
        builder.add_predecessor(join, t);
        builder.add_predecessor(join, f);
        builder.emit_void(InstData::CondBranch {
            cond: c,
            true_dest: t,
            false_dest: f,
        });

        builder.set_insert_block(t);
        let g1 = builder.intern("g1");
        builder.emit_void(InstData::StoreGlobalVar { name: g1, value: w });
        builder.emit_void(InstData::Branch { dest: join });

        builder.set_insert_block(f);
        let x = builder.emit_val(InstData::LiteralNumber(3.0), IrType::default());
        let g2 = builder.intern("g2");
        builder.emit_void(InstData::StoreGlobalVar { name: g2, value: x });
        builder.emit_void(InstData::Branch { dest: join });

        builder.set_insert_block(join);
        let g3 = builder.intern("g3");
        builder.emit_void(InstData::StoreGlobalVar { name: g3, value: w });
        builder.emit_void(InstData::Return { value: None });
    }

    let blocks = select_blocks(&module, func);
    let join_codes = &blocks[&join];
    assert!(
        join_codes.iter().any(|bc| matches!(bc, Bytecode::Lda(_))),
        "the join's predecessors disagree on the acc content (w vs x), so \
         the join must reload w from its home (join bytecodes: {join_codes:?})"
    );
    // And the whole diamond must still compute correctly end to end.
    let result = lower_function(&module, func).expect("diamond must lower");
    let halt = Machine::new().run(&result.bytecodes);
    assert!(
        matches!(halt, Halt::ReturnUndefined),
        "diamond must execute cleanly (bytecodes: {:?})",
        result.bytecodes
    );
}

// ─── B4-exposed latent bug: dead phi results must not emit copies ───────────

/// A phi whose RESULT is never used does not interfere with any value, so
/// coloring may legally share its slot with a LIVE value — and its edge
/// copies then clobber that live home. Exposed by the B4 re-coloring on
/// local/typescript-enum ×6 (lift): the fall-through edge's dead-phi
/// `mov` overwrote the just-homed live phi result, turning the printed
/// enum value into NaN. Pre-existing latently (the copy was always dead
/// traffic); the old acc-coloring happened to order it harmlessly.
///
/// Shape (cond → t/f → join):
///
/// ```text
/// entry: X = 222; Y = 333; cond = a0; CondBranch(cond, t, f)
/// t: obj = 111; jmp join
/// f: jmp join
/// join: phi_dead = φ(t: X, f: X)      ; NEVER used
///       phi_live = φ(t: obj, f: Y)    ; returned
/// ```
///
/// phi_dead is dead, so it may legally share phi_live's slot. On the t
/// edge the dead phi's copy would be `mov v0, v2` — overwriting obj's
/// just-written home. The fix skips copies (and handler-phi stores) for
/// dead phi results.
#[test]
fn dead_phi_result_emits_no_clobbering_copies() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "dead_phi", FunctionKind::Function, 1);
    let entry = module.func(func).entry_block;

    let (t, f, join, x, y, obj, phi_live, phi_dead, cond);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        cond = builder.create_func_param(0, IrType::default());
        x = builder.emit_val(InstData::LiteralNumber(222.0), IrType::default());
        y = builder.emit_val(InstData::LiteralNumber(333.0), IrType::default());
        t = builder.create_block();
        f = builder.create_block();
        join = builder.create_block();
        builder.add_predecessor(t, entry);
        builder.add_predecessor(f, entry);
        builder.add_predecessor(join, t);
        builder.add_predecessor(join, f);
        builder.emit_void(InstData::CondBranch {
            cond,
            true_dest: t,
            false_dest: f,
        });

        builder.set_insert_block(t);
        obj = builder.emit_val(InstData::LiteralNumber(111.0), IrType::default());
        builder.emit_void(InstData::Branch { dest: join });

        builder.set_insert_block(f);
        builder.emit_void(InstData::Branch { dest: join });

        builder.set_insert_block(join);
        phi_dead = builder.emit_val(
            InstData::Phi {
                entries: vec![(t, x), (f, x)],
            },
            IrType::default(),
        );
        let _ = phi_dead; // never used
        phi_live = builder.emit_val(
            InstData::Phi {
                entries: vec![(t, obj), (f, y)],
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return {
            value: Some(phi_live),
        });
    }

    // Regalloc's boissinot pass must emit no copies for the dead phi.
    let real = regalloc::allocate(&module, func).expect("allocation must succeed");
    assert!(
        real.phi_copies
            .values()
            .flatten()
            .all(|&(_, dst)| dst != phi_dead),
        "a dead phi result must not produce edge copies: {:?}",
        real.phi_copies
    );

    // End-to-end through lower_function: with cond truthy the t path runs
    // and the join must return obj = 111, not the dead phi's X = 222.
    let result = lower_function(&module, func).expect("dead-phi shape must lower");
    let mut machine = Machine::new().with_reg(result.num_regs, 1); // a0 = truthy
    let halt = machine.run(&result.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(111),
        "the join must return obj; a dead phi's copy would have clobbered \
         its home with X = 222 (bytecodes: {:?})",
        result.bytecodes
    );
}

/// The meet must NOT propagate predecessor acc content into a catch
/// handler: exception dispatch physically clobbers the accumulator at
/// handler entry, even when every CFG predecessor agrees on the content.
/// This covers handlers WITHOUT a seeded exception value (hand-built IR);
/// the seeded case is covered by the N13 prologue.
///
/// ```text
/// entry (try body): v = 42; x = 1; Throw(x); Unreachable
/// handler (catch, no exception value seeded): return x + v
/// ```
///
/// entry exits with the tracker provably holding x (homed, then the
/// throw's ensure_acc hit). A naive single-pred meet would seed the
/// handler with Holds(x) and ELIDE the add's `ensure_acc(x)` load — the
/// physical acc at dispatch holds the exception object, not x.
#[test]
fn handler_entry_never_inherits_predecessor_acc_content() {
    const V: i64 = 42;
    const X: i64 = 1;
    const EXC: i64 = 999;

    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "h", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let (v, x, handler);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        v = builder.emit_val(InstData::LiteralNumber(42.0), IrType::default());
        x = builder.emit_val(InstData::LiteralNumber(1.0), IrType::default());
        builder.emit_void(InstData::Throw { value: x });
        builder.emit_void(InstData::Unreachable);

        handler = builder.create_block();
        builder.add_predecessor(handler, entry);
        builder.set_insert_block(handler);
        let sum = builder.emit_val(
            InstData::BinaryOp {
                op: BinOp::Add,
                left: x,
                right: v,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(sum) });
    }
    module.func_mut(func).try_regions.push(TryRegion {
        try_blocks: vec![entry],
        catches: vec![CatchHandler {
            type_idx: u32::MAX,
            handler_block: handler,
        }],
    });

    // Simulate the handler slice with acc = the dispatched exception
    // object: the add must reload x from its home (Lda present) and
    // compute x + v, never read the exception object as x.
    let alloc = regalloc::allocate(&module, func).expect("allocation must succeed");
    let x_home = match alloc.allocation.get(&x) {
        Some(RegSlot::Reg(r)) => *r,
        other => panic!("x must have a register home, got {other:?}"),
    };
    let v_home = match alloc.allocation.get(&v) {
        Some(RegSlot::Reg(r)) => *r,
        other => panic!("v must have a register home, got {other:?}"),
    };
    let rpo = regalloc::compute_rpo(&module, func);
    let string_map: HashMap<StringId, EntityId> = HashMap::new();
    let selected =
        isel::select(&module, func, &alloc, &rpo, &string_map).expect("selection must succeed");
    let (_, handler_codes) = selected
        .block_codes
        .iter()
        .find(|(bb, _)| *bb == handler)
        .expect("handler block code must exist");
    assert!(
        handler_codes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Lda(_))),
        "the handler must reload from the homes — the dispatch clobbered \
         acc (handler bytecodes: {handler_codes:?})"
    );
    let mut machine = Machine::new()
        .with_reg(x_home, X)
        .with_reg(v_home, V)
        .with_acc(EXC);
    let halt = machine.run(handler_codes);
    assert_eq!(
        halt,
        Halt::Return(X + V),
        "the handler must compute x + v from the homes, not read the \
         dispatched exception object as x (handler bytecodes: {handler_codes:?})"
    );
}
