//! Issue `#103` (`P3-OPT-1`) regression suite: cross-function inliner cache
//! eviction (`callee_cache` and `env_reads_cache`) after a caller mutates via
//! inlining, plus linear-time `ConstId` literal DAG memoization on `256 KiB`
//! stacks.

use crate::common::V2Builder;
use abcd_ir::{
    BinOp, Block, BlockId, CallKind, ClassData, ClassId, Const, FuncId, FunctionData, FunctionKind,
    LexEnvKind, Modifiers, Module, ModuleVarKind, Op, ValueId, verify_module,
};
use abcd_opt::inline::{InlinePolicy, SkipReason, inline_module};
use abcd_opt::optimize_module;

fn verify_ok(module: &Module) {
    let report = verify_module(module);
    assert!(
        report.is_ok(),
        "module failed verification: {:?}",
        report.errors
    );
}

fn create_static_in_class(
    module: &mut Module,
    class_id: ClassId,
    name: &str,
    formal_count: usize,
) -> FuncId {
    let sym = module.sym.intern(name);
    let fid = FuncId::new(module.functions.len() as u32);
    let mut fdata = FunctionData::new(class_id, sym, FunctionKind::Function);
    fdata.modifiers = Modifiers::STATIC;
    let entry = BlockId::new(module.blocks.len() as u32);
    module.blocks.push(Block::default());
    fdata.blocks.push(entry);
    module.functions.push(fdata);
    module.classes[class_id.index()].methods.push(fid);

    let mut b = V2Builder::new(module, fid);
    // 3 implicit `[func][new.target][this]` slots (`0xF` static default) + formals.
    for _ in 0..(3 + formal_count) {
        b.create_param();
    }
    fid
}

fn emit_closure_call(b: &mut V2Builder<'_>, target: FuncId, args: Vec<ValueId>) -> ValueId {
    let df = b.emit_val(Op::DefineFunc {
        body: target,
        captures: Vec::new(),
        length: args.len() as u16,
    });
    let cl = b.emit_val(Op::AllocClosure { func: df });
    b.emit_val(Op::Call {
        callee: cl,
        this: None,
        args,
        kind: CallKind::Dynamic,
    })
}

fn func_has_call(module: &Module, fid: FuncId) -> bool {
    module.functions[fid.index()].blocks.iter().any(|&bb| {
        module.blocks[bb.index()]
            .insts
            .iter()
            .any(|&iid| matches!(module.insts[iid.index()].op, Op::Call { .. }))
    })
}

/// 1. `f0 -> f1`, `f1` inlines `f2` 4 times so `f1`'s instruction count grows
///    past `policy.max_callee_insts`, and `f3 -> f1` recomputes `f1`'s summary
///    and skips inlining `f1` with `SkipReason::CalleeTooLarge`.
///    Verifies both when `f0` inlined pre-growth `f1` and when `f0` skipped
///    `f1` due to `BlockTerminalCall` after caching `f1`'s summary.
#[test]
fn stale_callee_cache_evicted_when_f1_grows_past_max_callee_insts() {
    for f0_inlines_f1 in [true, false] {
        let mut module = Module::new();
        let c_sym = module.sym.intern("LGlobal;");
        let cid = ClassId::new(0);
        module.classes.push(ClassData::new(c_sym, c_sym));

        // Module function order: `[f0, f2, f1, f3]` so `f0` populates
        // `callee_cache[f1]` BEFORE `inline_func(f1)` mutates `f1`, and `f3`
        // queries `f1` AFTER `inline_func(f1)`.
        let f0 = create_static_in_class(&mut module, cid, "f0", 1);
        let f2 = create_static_in_class(&mut module, cid, "f2", 1);
        let f1 = create_static_in_class(&mut module, cid, "f1", 1);
        let f3 = create_static_in_class(&mut module, cid, "f3", 1);

        // `f2(x)` = `x + x + x + x` (4 BinaryOps + 1 Return = 5 insts).
        {
            let x = module.functions[f2.index()].params[3];
            let mut b = V2Builder::new(&mut module, f2);
            let mut acc = x;
            for _ in 0..4 {
                acc = b.emit_val(Op::BinaryOp {
                    op: BinOp::Add,
                    left: acc,
                    right: x,
                });
            }
            b.emit_void(Op::Return { value: Some(acc) });
        }

        // `f1(x)` calls `f2` 4 times (pre-inlining: 4*(DefineFunc+AllocClosure+Call) + Return = 13 insts <= 16).
        // After inlining `f2` 4 times, `f1` grows well above `max_callee_insts = 16`!
        {
            let x = module.functions[f1.index()].params[3];
            let mut b = V2Builder::new(&mut module, f1);
            let mut cur = x;
            for _ in 0..4 {
                cur = emit_closure_call(&mut b, f2, vec![cur]);
            }
            b.emit_void(Op::Return { value: Some(cur) });
        }

        // `f0(x)` calls `f1(x)`.
        {
            let x = module.functions[f0.index()].params[3];
            let mut b = V2Builder::new(&mut module, f0);
            let res = emit_closure_call(&mut b, f1, vec![x]);
            if f0_inlines_f1 {
                b.emit_void(Op::Return { value: Some(res) });
            }
            // When `!f0_inlines_f1`, `Call` is block-terminal (unverified IR test),
            // caching `f1` in `callee_cache` and skipping at `BlockTerminalCall`.
        }

        // `f3(x)` calls `f1(x)` after `f1` has expanded.
        {
            let x = module.functions[f3.index()].params[3];
            let mut b = V2Builder::new(&mut module, f3);
            let res = emit_closure_call(&mut b, f1, vec![x]);
            b.emit_void(Op::Return { value: Some(res) });
        }

        if f0_inlines_f1 {
            verify_ok(&module);
        }

        let policy = InlinePolicy {
            max_callee_insts: 16,
            max_inlined_insts_per_caller: 512,
        };
        let report = inline_module(&mut module, &policy);
        let expected_inlined = if f0_inlines_f1 { 5 } else { 4 };
        assert_eq!(report.sites_inlined, expected_inlined, "{report:?}");
        assert_eq!(
            report.skips.get(&SkipReason::CalleeTooLarge),
            Some(&1),
            "f3 -> f1 must see post-inlining f1 size and skip with CalleeTooLarge: {report:?}"
        );
        assert!(
            func_has_call(&module, f3),
            "f3 must retain its un-inlined Call to expanded f1"
        );

        if f0_inlines_f1 {
            verify_ok(&module);
            let _ = optimize_module(&mut module);
            verify_ok(&module);
        }
    }
}

/// 2. `f0 -> f1`, `f1` inlines `f2` 3 times staying within `max_callee_insts`
///    (`64`) while exceeding `f3`'s `max_inlined_insts_per_caller` (`18`), so
///    `f3 -> f1` skips with `SkipReason::CallerBudgetExhausted`.
#[test]
fn stale_callee_cache_evicted_when_f1_exceeds_caller_inst_budget() {
    let mut module = Module::new();
    let c_sym = module.sym.intern("LGlobal;");
    let cid = ClassId::new(0);
    module.classes.push(ClassData::new(c_sym, c_sym));

    let f0 = create_static_in_class(&mut module, cid, "f0", 1);
    let f2 = create_static_in_class(&mut module, cid, "f2", 1);
    let f1 = create_static_in_class(&mut module, cid, "f1", 1);
    let f3 = create_static_in_class(&mut module, cid, "f3", 1);

    // `f2(x)` = 4 BinaryOps + Return = 5 insts.
    {
        let x = module.functions[f2.index()].params[3];
        let mut b = V2Builder::new(&mut module, f2);
        let mut acc = x;
        for _ in 0..4 {
            acc = b.emit_val(Op::BinaryOp {
                op: BinOp::Add,
                left: acc,
                right: x,
            });
        }
        b.emit_void(Op::Return { value: Some(acc) });
    }

    // `f1(x)` calls `f2` 3 times: initially 10 insts (<= 18 budget); after
    // inlining `f2` 3 times (3 * 5 = 15 <= 18 budget), `f1` has > 18 insts
    // (still <= 64 `max_callee_insts`).
    {
        let x = module.functions[f1.index()].params[3];
        let mut b = V2Builder::new(&mut module, f1);
        let mut cur = x;
        for _ in 0..3 {
            cur = emit_closure_call(&mut b, f2, vec![cur]);
        }
        b.emit_void(Op::Return { value: Some(cur) });
    }

    for caller in [f0, f3] {
        let x = module.functions[caller.index()].params[3];
        let mut b = V2Builder::new(&mut module, caller);
        let res = emit_closure_call(&mut b, f1, vec![x]);
        b.emit_void(Op::Return { value: Some(res) });
    }
    verify_ok(&module);

    let report = inline_module(
        &mut module,
        &InlinePolicy {
            max_callee_insts: 64,
            max_inlined_insts_per_caller: 18,
        },
    );
    assert_eq!(report.sites_inlined, 4, "f0->f1 + 3*(f1->f2): {report:?}");
    assert_eq!(
        report.skips.get(&SkipReason::CallerBudgetExhausted),
        Some(&1),
        "f3 -> f1 must see expanded f1 inst_count and skip with CallerBudgetExhausted: {report:?}"
    );
    assert!(func_has_call(&module, f3));
    verify_ok(&module);
}

/// 3. `f0 -> f1`, `f1` inlines `f2` 4 times inflating `f1`'s `ic8_slots` from
///    `9` to `41`, so `f3` (which already consumes `223` `ic8` slots:
///    `223 - 2 + 41 = 262 > 254 = MAX_CALLER_IC8_SLOTS`) recomputes `f1`'s IC
///    footprint and skips with `SkipReason::CallerBudgetExhausted`.
#[test]
fn stale_callee_cache_evicted_when_f1_grows_past_caller_ic8_slot_limit() {
    let mut module = Module::new();
    let c_sym = module.sym.intern("LGlobal;");
    let cid = ClassId::new(0);
    module.classes.push(ClassData::new(c_sym, c_sym));

    let f0 = create_static_in_class(&mut module, cid, "f0", 1);
    let f2 = create_static_in_class(&mut module, cid, "f2", 1);
    let f1 = create_static_in_class(&mut module, cid, "f1", 1);
    let f3 = create_static_in_class(&mut module, cid, "f3", 1);

    // `f2(x)`: 10 BinaryOps (`10` ic8 slots) + Return.
    {
        let x = module.functions[f2.index()].params[3];
        let mut b = V2Builder::new(&mut module, f2);
        let mut acc = x;
        for _ in 0..10 {
            acc = b.emit_val(Op::BinaryOp {
                op: BinOp::Add,
                left: acc,
                right: x,
            });
        }
        b.emit_void(Op::Return { value: Some(acc) });
    }

    // `f1(x)`: 1 shared closure of `f2` + 4 calls -> initially `1 + 4*2 = 9` ic8 slots;
    // after inlining all 4 calls, `1 + 4*10 = 41` ic8 slots!
    {
        let x = module.functions[f1.index()].params[3];
        let mut b = V2Builder::new(&mut module, f1);
        let df = b.emit_val(Op::DefineFunc {
            body: f2,
            captures: Vec::new(),
            length: 1,
        });
        let cl = b.emit_val(Op::AllocClosure { func: df });
        let mut cur = x;
        for _ in 0..4 {
            cur = b.emit_val(Op::Call {
                callee: cl,
                this: None,
                args: vec![cur],
                kind: CallKind::Dynamic,
            });
        }
        b.emit_void(Op::Return { value: Some(cur) });
    }

    // `f0(x)`: caches pre-inlining `f1` (`ic8_slots == 9`).
    {
        let x = module.functions[f0.index()].params[3];
        let mut b = V2Builder::new(&mut module, f0);
        let res = emit_closure_call(&mut b, f1, vec![x]);
        b.emit_void(Op::Return { value: Some(res) });
    }

    // `f3(x)`: 220 BinaryOps (`220` ic8) + DefineFunc (`1` ic8) + Call (`2` ic8) = `223` ic8.
    // Stale `f1` (`9` ic8) would compute `223 - 2 + 9 = 230 <= 254` and overflow `f3` to `262`!
    // Recomputed `f1` (`41` ic8) computes `223 - 2 + 41 = 262 > 254` -> `CallerBudgetExhausted`.
    {
        let x = module.functions[f3.index()].params[3];
        let mut b = V2Builder::new(&mut module, f3);
        let mut acc = x;
        for _ in 0..220 {
            acc = b.emit_val(Op::BinaryOp {
                op: BinOp::Add,
                left: acc,
                right: x,
            });
        }
        let res = emit_closure_call(&mut b, f1, vec![acc]);
        b.emit_void(Op::Return { value: Some(res) });
    }
    verify_ok(&module);

    let report = inline_module(
        &mut module,
        &InlinePolicy {
            max_callee_insts: 200,
            max_inlined_insts_per_caller: 2_000,
        },
    );
    assert_eq!(report.sites_inlined, 5, "f0->f1 + 4*(f1->f2): {report:?}");
    assert_eq!(
        report.skips.get(&SkipReason::CallerBudgetExhausted),
        Some(&1),
        "f3 -> f1 must recompute f1 ic8_slots and skip with CallerBudgetExhausted: {report:?}"
    );
    assert!(func_has_call(&module, f3));
    verify_ok(&module);
}

/// 4. `f0 -> f1` (in `class_a`), `f1` inlines same-class `f2` containing
///    `Op::LoadModuleVar` (`has_module_ops` transitions `false -> true`), and
///    cross-class `f3` (in `class_b`) calling `f1` recomputes `f1`'s summary
///    and skips with `SkipReason::CalleeForeignValue`.
#[test]
fn stale_callee_cache_evicted_when_f1_acquires_same_class_module_var() {
    let mut module = Module::new();
    let sym_a = module.sym.intern("LModA;");
    let sym_b = module.sym.intern("LModB;");
    let class_a = ClassId::new(0);
    module.classes.push(ClassData::new(sym_a, sym_a));
    let class_b = ClassId::new(1);
    module.classes.push(ClassData::new(sym_b, sym_b));

    // Order `[f0, f2, f1, f3]`:
    // - `f0` (`class_a`) calls `f1` (`class_a`) before `f1` has any module ops -> inlines!
    // - `f1` (`class_a`) calls `f2` (`class_a`, has `LoadModuleVar`) -> same-class, inlines!
    // - `f3` (`class_b`) calls `f1` (`class_a`, now has `LoadModuleVar`!) -> cross-class, MUST skip!
    let f0 = create_static_in_class(&mut module, class_a, "f0", 0);
    let f2 = create_static_in_class(&mut module, class_a, "f2", 0);
    let f1 = create_static_in_class(&mut module, class_a, "f1", 0);
    let f3 = create_static_in_class(&mut module, class_b, "f3", 0);

    {
        let mut b = V2Builder::new(&mut module, f2);
        let mv = b.emit_val(Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::Local,
        });
        b.emit_void(Op::Return { value: Some(mv) });
    }
    {
        let mut b = V2Builder::new(&mut module, f1);
        let res = emit_closure_call(&mut b, f2, Vec::new());
        b.emit_void(Op::Return { value: Some(res) });
    }
    {
        let mut b = V2Builder::new(&mut module, f0);
        let res = emit_closure_call(&mut b, f1, Vec::new());
        b.emit_void(Op::Return { value: Some(res) });
    }
    {
        let mut b = V2Builder::new(&mut module, f3);
        let res = emit_closure_call(&mut b, f1, Vec::new());
        b.emit_void(Op::Return { value: Some(res) });
    }
    verify_ok(&module);

    let report = inline_module(&mut module, &InlinePolicy::default());
    assert_eq!(
        report.sites_inlined, 2,
        "f0->f1 and f1->f2 inline: {report:?}"
    );
    assert_eq!(
        report.skips.get(&SkipReason::CalleeForeignValue),
        Some(&1),
        "cross-class f3 -> f1 must reject post-inlining LoadModuleVar: {report:?}"
    );
    let f3_has_module_op = module.functions[f3.index()].blocks.iter().any(|&bb| {
        module.blocks[bb.index()]
            .insts
            .iter()
            .any(|&iid| matches!(module.insts[iid.index()].op, Op::LoadModuleVar { .. }))
    });
    assert!(
        !f3_has_module_op,
        "class_a LoadModuleVar must never be spliced into class_b caller f3"
    );
    verify_ok(&module);
}

/// 5. `env_reads_cache` eviction: `f0` queries `f_outer_early` (which defines
///    `f1`), caching `env_reads_cache[f1] = true` because `f1`'s `DefineMethod`
///    func operand is an unresolved `Call(f_make_clean)`. Once `f1` inlines
///    `f_make_clean`, `f1`'s `DefineMethod` operand resolves to env-clean
///    `f_clean`, `env_reads_cache[f1]` is evicted, and `f3` successfully
///    inlines `f_outer_late` (which also defines `f1`).
#[test]
fn stale_env_reads_cache_evicted_after_f1_resolves_closure_operand() {
    let mut module = Module::new();
    let c_sym = module.sym.intern("LGlobal;");
    let cid = ClassId::new(0);
    module.classes.push(ClassData::new(c_sym, c_sym));

    let f_clean = create_static_in_class(&mut module, cid, "f_clean", 0);
    let f_make_clean = create_static_in_class(&mut module, cid, "f_make_clean", 0);
    let f0 = create_static_in_class(&mut module, cid, "f0", 0);
    let f_outer_early = create_static_in_class(&mut module, cid, "f_outer_early", 0);
    let f1 = create_static_in_class(&mut module, cid, "f1", 0);
    let f_outer_late = create_static_in_class(&mut module, cid, "f_outer_late", 0);
    let f3 = create_static_in_class(&mut module, cid, "f3", 0);

    {
        let mut b = V2Builder::new(&mut module, f_clean);
        let n = b.emit_number(1.0);
        b.emit_void(Op::Return { value: Some(n) });
    }
    {
        let mut b = V2Builder::new(&mut module, f_make_clean);
        let df = b.emit_val(Op::DefineFunc {
            body: f_clean,
            captures: Vec::new(),
            length: 0,
        });
        b.emit_void(Op::Return { value: Some(df) });
    }
    {
        let mut b = V2Builder::new(&mut module, f1);
        let empty_shape = b.konst(Const::ObjectLiteral {
            keys: Vec::new(),
            values: Vec::new(),
        });
        let home = b.emit_val(Op::AllocObject { shape: empty_shape });
        let m_sym = b.sym("m");
        let tmp = emit_closure_call(&mut b, f_make_clean, Vec::new());
        let dm = b.emit_val(Op::DefineMethod {
            object: home,
            name: m_sym,
            func: tmp,
            length: 0,
        });
        b.emit_void(Op::Return { value: Some(dm) });
    }
    for outer in [f_outer_early, f_outer_late] {
        let mut b = V2Builder::new(&mut module, outer);
        let df = b.emit_val(Op::DefineFunc {
            body: f1,
            captures: Vec::new(),
            length: 0,
        });
        let cl = b.emit_val(Op::AllocClosure { func: df });
        b.emit_void(Op::Return { value: Some(cl) });
    }
    {
        let mut b = V2Builder::new(&mut module, f0);
        let res = emit_closure_call(&mut b, f_outer_early, Vec::new());
        b.emit_void(Op::Return { value: Some(res) });
    }
    {
        let mut b = V2Builder::new(&mut module, f3);
        let res = emit_closure_call(&mut b, f_outer_late, Vec::new());
        b.emit_void(Op::Return { value: Some(res) });
    }
    verify_ok(&module);

    let report = inline_module(&mut module, &InlinePolicy::default());
    // `f0 -> f_outer_early` skips (`CalleeDefinesClosure` before `f1` inlined `f_make_clean`),
    // `f1 -> f_make_clean` inlines (evicting `env_reads_cache[f1]`), and
    // `f3 -> f_outer_late` now sees `env_reads(f1) == false` and inlines!
    assert_eq!(report.sites_inlined, 2, "{report:?}");
    assert_eq!(
        report.skips.get(&SkipReason::CalleeDefinesClosure),
        Some(&1),
        "{report:?}"
    );
    assert!(!func_has_call(&module, f3), "f3 must inline f_outer_late");
    verify_ok(&module);
}

/// 6. Deep 600-level binary diamond `ConstId` literal DAG (`2^600` paths if
///    unmemoized) referenced across multiple functions executes in linear time
///    inside a `256 KiB` stack thread without overflowing or mis-classifying
///    nested `MethodRef` lexical captures.
#[test]
fn deep_diamond_const_method_ref_dag_memoizes_on_256kib_stack() {
    let handle = std::thread::Builder::new()
        .name("inline-const-dag-256k".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut module = Module::new();
            let c_sym = module.sym.intern("LGlobal;");
            let cid = ClassId::new(0);
            module.classes.push(ClassData::new(c_sym, c_sym));

            let nested_lex = create_static_in_class(&mut module, cid, "nested_lex", 0);
            {
                let mut b = V2Builder::new(&mut module, nested_lex);
                let v = b.emit_val(Op::GetLexVar {
                    level: 0,
                    slot: 0,
                    kind: LexEnvKind::Plain,
                });
                b.emit_void(Op::Return { value: Some(v) });
            }

            let nested_clean = create_static_in_class(&mut module, cid, "nested_clean", 0);
            {
                let mut b = V2Builder::new(&mut module, nested_clean);
                let v = b.emit_number(42.0);
                b.emit_void(Op::Return { value: Some(v) });
            }

            let k_sym = module.sym.intern("m");
            let k_cid = module.consts.push(Const::String(k_sym));
            let mr_lex = module.consts.push(Const::method_ref(nested_lex));
            let mr_clean = module.consts.push(Const::method_ref(nested_clean));

            let mut cur_lex = module.consts.push(Const::ObjectLiteral {
                keys: vec![k_cid],
                values: vec![mr_lex],
            });
            let mut cur_clean = module.consts.push(Const::ObjectLiteral {
                keys: vec![k_cid],
                values: vec![mr_clean],
            });
            for _ in 0..600 {
                cur_lex = module
                    .consts
                    .push(Const::ArrayLiteral(vec![cur_lex, cur_lex]));
                cur_clean = module
                    .consts
                    .push(Const::ArrayLiteral(vec![cur_clean, cur_clean]));
            }

            let mut lex_callees = Vec::new();
            let mut clean_callees = Vec::new();
            for idx in 0..8 {
                let g_lex = create_static_in_class(&mut module, cid, &format!("g_lex_{idx}"), 0);
                {
                    let mut b = V2Builder::new(&mut module, g_lex);
                    let arr = b.emit_val(Op::AllocArray {
                        shape: Some(cur_lex),
                    });
                    b.emit_void(Op::Return { value: Some(arr) });
                }
                lex_callees.push(g_lex);

                let g_clean =
                    create_static_in_class(&mut module, cid, &format!("g_clean_{idx}"), 0);
                {
                    let mut b = V2Builder::new(&mut module, g_clean);
                    let arr = b.emit_val(Op::AllocArray {
                        shape: Some(cur_clean),
                    });
                    b.emit_void(Op::Return { value: Some(arr) });
                }
                clean_callees.push(g_clean);
            }

            let caller = create_static_in_class(&mut module, cid, "caller", 0);
            {
                let mut b = V2Builder::new(&mut module, caller);
                let mut last = None;
                for g in lex_callees.iter().chain(clean_callees.iter()) {
                    last = Some(emit_closure_call(&mut b, *g, Vec::new()));
                }
                b.emit_void(Op::Return { value: last });
            }
            verify_ok(&module);

            let report = inline_module(&mut module, &InlinePolicy::default());
            assert_eq!(report.sites_inlined, 8, "{report:?}");
            assert_eq!(
                report.skips.get(&SkipReason::CalleeDefinesClosure),
                Some(&8),
                "{report:?}"
            );
            verify_ok(&module);
        })
        .expect("spawn 256 KiB stack thread");
    handle.join().expect("256 KiB thread must not overflow");
}
