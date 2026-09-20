//! B4 regression (v0.2 port of `abcd-ir/tests/lower_acc_cache.rs`): the
//! accumulator is a PHYSICAL emission-time resource, not a coloring class
//! ("acc-as-cache").
//!
//! Every value has a register home, every acc-writing instruction result
//! with a use is homed by a `Sta`, and isel's emission-time acc tracker
//! reloads the home whenever the physical acc content is not provably the
//! requested value. The two `*_miscomputes_*` shapes are the crafted
//! wrong-value witnesses; the rest pin the contract: homing stores,
//! cache-hit `Lda` elision on def→use chains, and the block-entry meet
//! rule.

mod common;

use std::collections::HashMap;

use abcd_ir2::{
    BinOp, BlockId, Catch, FunctionKind, Module, Op, TryRegion, UnOp, ValueDef,
};
use abcd_isa::Bytecode;
use abcd_lower::regalloc::{self, RegSlot};
use abcd_lower::{fusion, isel, lower_function};

use common::{Halt, Machine, V2Builder};

// ─── Red witness 1: class-accessors shape (definegettersetterbyvalue) ──────

/// ```text
/// k = 111   ; the "key"   — defined FIRST, used LAST
/// o = 222   ; the object
/// g = 333   ; the getter
/// s = 444   ; the setter
/// definegettersetterbyvalue(o, k, g, s)
/// ```
#[test]
fn definegettersetter_operands_survive_intervening_acc_writes() {
    const K: i64 = 111;
    const O: i64 = 222;
    const G: i64 = 333;
    const S: i64 = 444;

    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "accessors", FunctionKind::Function);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let lit = |b: &mut V2Builder, v: f64| {
            let cid = b.konst(abcd_ir2::Const::number(v));
            b.emit_val(Op::LoadConst(cid))
        };
        let k = lit(&mut builder, 111.0);
        let o = lit(&mut builder, 222.0);
        let g = lit(&mut builder, 333.0);
        let s = lit(&mut builder, 444.0);
        builder.emit_void(Op::DefineGetterSetterByValue {
            obj: o,
            key: k,
            getter: g,
            setter: s,
        });
        builder.emit_void(Op::Return { value: None });
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
        "B4: the key operand must be its own literal (bytecodes: {:?})",
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

/// ```text
/// gen, obj = params
/// y = 777                                    ; the yield value
/// f = false
/// obj.x = f                                  ; StoreProp
/// suspendgenerator(gen, y)                   ; acc must be the yield value
/// ```
#[test]
fn acc_held_yield_value_survives_clobber_before_suspend() {
    const GEN: i64 = 4242;
    const OBJ: i64 = 7777;
    const YIELD: i64 = 777;

    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "gen_fn", FunctionKind::Function);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let genobj = builder.create_param();
        let obj = builder.create_param();
        let ycid = builder.konst(abcd_ir2::Const::number(777.0));
        let y = builder.emit_val(Op::LoadConst(ycid));
        let fcid = builder.konst(abcd_ir2::Const::Bool(false));
        let f = builder.emit_val(Op::LoadConst(fcid));
        let name = builder.sym("x");
        builder.emit_void(Op::StoreProp {
            object: obj,
            name,
            value: f,
        });
        builder.emit_void(Op::SuspendGenerator { genobj, value: y });
        builder.emit_void(Op::Return { value: None });
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
        "B4: the acc at suspendgenerator must be the yield value (bytecodes: {:?})",
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
/// `Lda`):
///
/// ```text
/// a = 1
/// b = -a        ; ensure_acc(a): acc already holds a (just homed)
/// c = !b        ; ensure_acc(b): cache hit again
/// return c      ; ensure_acc(c): cache hit
/// ```
#[test]
fn def_use_chains_hit_the_acc_cache() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "chain", FunctionKind::Function);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let cid = builder.konst(abcd_ir2::Const::number(1.0));
        let a = builder.emit_val(Op::LoadConst(cid));
        let b = builder.emit_val(Op::UnaryOp {
            op: UnOp::Minus,
            operand: a,
        });
        let c = builder.emit_val(Op::UnaryOp {
            op: UnOp::LogicalNot,
            operand: b,
        });
        builder.emit_void(Op::Return { value: Some(c) });
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
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "twice", FunctionKind::Function);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let cid = builder.konst(abcd_ir2::Const::number(42.0));
        let v = builder.emit_val(Op::LoadConst(cid));
        let a = builder.sym("a");
        let b = builder.sym("b");
        builder.emit_void(Op::StoreGlobal { name: a, value: v });
        builder.emit_void(Op::StoreGlobal { name: b, value: v });
        builder.emit_void(Op::Return { value: None });
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
fn select_blocks(module: &Module, func: abcd_ir2::FuncId) -> HashMap<BlockId, Vec<Bytecode>> {
    let suppression = fusion::analyze(module, &module.functions[func.index()].blocks);
    let alloc = regalloc::allocate(module, func, &suppression).expect("allocation must succeed");
    let rpo = regalloc::compute_rpo(module, func);
    isel::select(module, func, &alloc, &rpo, &suppression)
        .expect("selection must succeed")
        .block_codes
        .into_iter()
        .collect()
}

/// Single-predecessor propagation: a block whose only predecessor exits
/// with the acc provably holding value V enters with that knowledge, so
/// its first acc use of V emits NO `Lda`.
#[test]
fn single_predecessor_acc_content_propagates() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "prop", FunctionKind::Function);
    let (entry, body);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        let cid1 = builder.konst(abcd_ir2::Const::number(1.0));
        let _a = builder.emit_val(Op::LoadConst(cid1));
        let cid2 = builder.konst(abcd_ir2::Const::number(2.0));
        let b = builder.emit_val(Op::LoadConst(cid2));
        body = builder.create_block();
        builder.add_predecessor(body, entry);
        builder.emit_void(Op::Branch { dest: body });
        builder.set_insert_block(body);
        let g = builder.sym("g");
        builder.emit_void(Op::StoreGlobal { name: g, value: b });
        builder.emit_void(Op::Return { value: None });
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
#[test]
fn disagreeing_predecessors_force_a_reload_at_the_join() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "diamond", FunctionKind::Function);
    let (entry, t, f, join);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        let cid9 = builder.konst(abcd_ir2::Const::number(9.0));
        let w = builder.emit_val(Op::LoadConst(cid9));
        let cidt = builder.konst(abcd_ir2::Const::Bool(true));
        let c = builder.emit_val(Op::LoadConst(cidt));
        t = builder.create_block();
        f = builder.create_block();
        join = builder.create_block();
        builder.add_predecessor(t, entry);
        builder.add_predecessor(f, entry);
        builder.add_predecessor(join, t);
        builder.add_predecessor(join, f);
        builder.emit_void(Op::CondBranch {
            cond: c,
            true_dest: t,
            false_dest: f,
        });

        builder.set_insert_block(t);
        let g1 = builder.sym("g1");
        builder.emit_void(Op::StoreGlobal { name: g1, value: w });
        builder.emit_void(Op::Branch { dest: join });

        builder.set_insert_block(f);
        let cid3 = builder.konst(abcd_ir2::Const::number(3.0));
        let x = builder.emit_val(Op::LoadConst(cid3));
        let g2 = builder.sym("g2");
        builder.emit_void(Op::StoreGlobal { name: g2, value: x });
        builder.emit_void(Op::Branch { dest: join });

        builder.set_insert_block(join);
        let g3 = builder.sym("g3");
        builder.emit_void(Op::StoreGlobal { name: g3, value: w });
        builder.emit_void(Op::Return { value: None });
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
/// copies then clobber that live home.
///
/// ```text
/// entry: X = 222; Y = 333; cond = a0; CondBranch(cond, t, f)
/// t: obj = 111; jmp join
/// f: jmp join
/// join: phi_dead = φ(t: X, f: X)      ; NEVER used
///       phi_live = φ(t: obj, f: Y)    ; returned
/// ```
#[test]
fn dead_phi_result_emits_no_clobbering_copies() {
    use abcd_ir2::{Edge, EdgeKind};

    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "dead_phi", FunctionKind::Function);
    let (entry, t, f, join, x, y, obj, phi_live, phi_dead, cond);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        cond = builder.create_param();
        let cx = builder.konst(abcd_ir2::Const::number(222.0));
        x = builder.emit_val(Op::LoadConst(cx));
        let cy = builder.konst(abcd_ir2::Const::number(333.0));
        y = builder.emit_val(Op::LoadConst(cy));
        t = builder.create_block();
        f = builder.create_block();
        join = builder.create_block();
        builder.add_predecessor(t, entry);
        builder.add_predecessor(f, entry);
        builder.add_predecessor(join, t);
        builder.add_predecessor(join, f);
        builder.emit_void(Op::CondBranch {
            cond,
            true_dest: t,
            false_dest: f,
        });

        builder.set_insert_block(t);
        let cobj = builder.konst(abcd_ir2::Const::number(111.0));
        obj = builder.emit_val(Op::LoadConst(cobj));
        builder.emit_void(Op::Branch { dest: join });

        builder.set_insert_block(f);
        builder.emit_void(Op::Branch { dest: join });

        builder.set_insert_block(join);
        let normal = |from: BlockId| Edge {
            from,
            kind: EdgeKind::Normal,
        };
        phi_dead = builder.emit_val(Op::Phi {
            entries: vec![(normal(t), x), (normal(f), x)],
        });
        let _ = phi_dead; // never used
        phi_live = builder.emit_val(Op::Phi {
            entries: vec![(normal(t), obj), (normal(f), y)],
        });
        builder.emit_void(Op::Return {
            value: Some(phi_live),
        });
    }

    // Regalloc's boissinot pass must emit no copies for the dead phi.
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let real = regalloc::allocate(&module, func, &suppression).expect("allocation must succeed");
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
///
/// ```text
/// entry (try body): v = 42; x = 1; Throw(x); Unreachable
/// handler (catch, exception value unused): return x + v
/// ```
#[test]
fn handler_entry_never_inherits_predecessor_acc_content() {
    const V: i64 = 42;
    const X: i64 = 1;
    const EXC: i64 = 999;

    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "h", FunctionKind::Function);
    let (entry, v, x, handler, exception);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        let cv = builder.konst(abcd_ir2::Const::number(42.0));
        v = builder.emit_val(Op::LoadConst(cv));
        let cx = builder.konst(abcd_ir2::Const::number(1.0));
        x = builder.emit_val(Op::LoadConst(cx));
        builder.emit_void(Op::Throw { value: x });
        builder.emit_void(Op::Unreachable);

        handler = builder.create_block();
        builder.add_exceptional_predecessor(handler, entry);
        exception = builder.create_exception_param(handler);
        builder.set_insert_block(handler);
        let sum = builder.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: x,
            right: v,
        });
        builder.emit_void(Op::Return { value: Some(sum) });
    }
    module.functions[func.index()].try_regions.push(TryRegion {
        protected: vec![entry],
        catches: vec![Catch {
            handler,
            exception,
            type_idx: None,
        }],
    });

    // Simulate the handler slice with acc = the dispatched exception
    // object: the add must reload x from its home (Lda present) and
    // compute x + v, never read the exception object as x.
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let alloc = regalloc::allocate(&module, func, &suppression).expect("allocation must succeed");
    let x_home = match alloc.allocation.get(&x) {
        Some(RegSlot::Reg(r)) => *r,
        other => panic!("x must have a register home, got {other:?}"),
    };
    let v_home = match alloc.allocation.get(&v) {
        Some(RegSlot::Reg(r)) => *r,
        other => panic!("v must have a register home, got {other:?}"),
    };
    let rpo = regalloc::compute_rpo(&module, func);
    let selected = isel::select(&module, func, &alloc, &rpo, &suppression)
        .expect("selection must succeed");
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

/// The exception value is unused in the shape above, so it stays
/// uncolored and the handler prologue is skipped — asserted implicitly by
/// the Lda-reload behavior. A USED exception value gets the N13 `Sta`
/// prologue instead (covered by the exception-edge tests).
#[test]
fn unused_exception_value_is_uncolored() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "h2", FunctionKind::Function);
    let (entry, handler, exception);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        builder.emit_void(Op::ThrowNotExists);
        builder.emit_void(Op::Unreachable);
        handler = builder.create_block();
        builder.add_exceptional_predecessor(handler, entry);
        exception = builder.create_exception_param(handler);
        builder.set_insert_block(handler);
        builder.emit_void(Op::Return { value: None });
    }
    module.functions[func.index()].try_regions.push(TryRegion {
        protected: vec![entry],
        catches: vec![Catch {
            handler,
            exception,
            type_idx: None,
        }],
    });
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let alloc = regalloc::allocate(&module, func, &suppression).expect("allocation must succeed");
    assert!(
        !alloc.allocation.contains_key(&exception),
        "an unused exception value needs no register home"
    );
    let _ = ValueDef::ExceptionParam(handler);
}
