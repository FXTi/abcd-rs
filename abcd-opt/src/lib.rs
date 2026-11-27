//! # abcd-opt — optimization passes for the SSA IR (`abcd-ir`)
//!
//! Format-independent optimization pipeline over [`abcd_ir::Module`]:
//! [`peephole`] (local constant and branch folding), [`sccp`] (sparse
//! conditional constant propagation), [`dce`] (effects-driven aggressive dead
//! code elimination + `DebugData` sweep + CFG simplification), and [`copyprop`]
//! (trivial-phi and `Mov`-chain propagation), all backed by the shared ECMA-262
//! constant-evaluation kernel in [`const_eval`]. [`inline`] provides a guarded
//! single-callee SSA function inliner on an **opt-in** basis (never run by
//! [`optimize_module`], preserving function boundaries for callers such as
//! `abcd-decompile`).
//!
//! ## Format independence (structurally enforced)
//!
//! Every pass operates on [`abcd_ir::Module`] alone (`design/ir.md`). This
//! crate's `Cargo.toml` `[dependencies]` list **only** `abcd-ir` and pure-Rust
//! zero-dep `libm` (for cross-platform deterministic IEEE-754 math) — never
//! `abcd-file`, `abcd-isa`, `abcd-file-sys`, `abcd-isa-sys`, `abcd-lift`, or
//! `abcd-lower`.
//!
//! ## ECMAScript & exception soundness invariants (`design/decisions.md`)
//!
//! - **Single shared ECMA-262 fold kernel**: [`peephole`] and [`sccp`] share
//!   [`const_eval`], evaluating non-commutative binary/comparison operators in
//!   ArkCompiler's operand order (`vreg OP acc`, encoded on IR instructions as
//!   `right OP left`, `N36`).
//! - **Signed zero, canonical `NaN`, & ECMA-262 `**`**: folds preserve `-0.0`
//!   bit-exactly via [`abcd_ir::Const::Number`] while canonicalizing computed
//!   `NaN` values to `0x7ff8_0000_0000_0000` (`#60`) and evaluating
//!   exponentiation per ECMA-262 `Number::exponentiate` over `libm::pow`
//!   (`R3-H6`). `Sccp`'s lattice meet compares numbers bitwise (`+0.0` and
//!   `-0.0` meet to `Bottom`, `R3-H5`), whereas `StrictEq` compares numbers
//!   with IEEE `==` (`0 === -0` is `true`, `NaN !== NaN`, `N40`).
//! - **Nullish & coercion semantics**: loose `Eq`/`NotEq` never mis-coerces
//!   `null` or `undefined` through `ToNumber` (`N38(iii)` / `N41`), arithmetic
//!   coerces `undefined -> NaN` and `null -> +0.0`, `ToBoolean` handles all
//!   primitive scalar constants (`Bool`, `Int8`, `Int32`, `Int64`, `UInt64`,
//!   `Float32`, `Number`, `String`, `BigInt`, `Null`, `Undefined`) plus
//!   allocation shapes, and instructions carrying [`abcd_ir::Ty::Static`] skip
//!   dynamic JS `f64` folding (`R3-A11`).
//! - **Unary, `jeqz`/`jnez`, & bitwise semantics**: `UnOp::BitNot` performs
//!   32-bit bitwise NOT, `UnOp::LogicalNot` performs boolean negation, and
//!   [`abcd_ir::UnOp::JumpEqz`] / [`abcd_ir::UnOp::JumpNez`] match ArkCompiler's
//!   exact raw branch predicates (`R3-X1`); bitwise and shift folds apply
//!   ECMA-262 `ToInt32` / `ToUint32` (`N42`), never Rust's saturating casts.
//! - **SCCP exception soundness**: reachability traverses [`abcd_ir::cfg`]
//!   exception-augmented edges (`ExceptionHandlerMap`, including blocks ending
//!   in `Return`/`Unreachable`), seeds entry `CondBranch` edges accurately, and
//!   forces [`abcd_ir::ValueDef::ExceptionParam`] plus handler-block phis to
//!   lattice `Bottom`.
//! - **Effects-derived ADCE & `DebugData` hygiene**: instruction essentiality
//!   derives solely from [`abcd_ir::Op::effects_in`] and
//!   [`abcd_ir::Effects::is_removable_if_unused`] (`T3` / `R2-D2`), sweeping
//!   dead `frame_init_consts` and dead `DebugData` instruction rows so
//!   [`abcd_ir::verify_module`] stays clean after every pass.
//!
//! ## Library rule
//!
//! No panics on data: arena lookups return `Option`; passes skip what
//! they cannot soundly rewrite.

#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]

pub mod const_eval;
pub mod copyprop;
pub mod dce;
pub mod inline;
pub mod peephole;
pub mod sccp;

use abcd_ir::{FuncId, Module};

/// A function-level optimization pass.
pub trait FuncPass {
    /// Run the pass on `func` within `module`.
    /// Returns `true` if the IR was modified.
    fn run(&self, module: &mut Module, func: FuncId) -> bool;
}

/// Run the full optimization pipeline on a single function.
/// Pipeline: peephole → sccp → adce + cfg-simplify → copyprop → peephole
/// → adce + cfg-simplify → trailing copyprop (+ adce).
/// Returns `true` if any pass modified the IR.
pub fn optimize_func(module: &mut Module, func: FuncId) -> bool {
    let mut changed = false;

    // Round 1: peephole → sccp → adce + cfg simplify → copyprop
    changed |= peephole::Peephole.run(module, func);
    changed |= sccp::Sccp.run(module, func);
    changed |= dce::Adce.run(module, func);
    changed |= dce::CfgSimplify.run(module, func);
    changed |= copyprop::CopyProp.run(module, func);

    // Round 2: peephole → adce + cfg simplify → trailing copyprop (`R3-A12`)
    changed |= peephole::Peephole.run(module, func);
    changed |= dce::Adce.run(module, func);
    changed |= dce::CfgSimplify.run(module, func);
    if copyprop::CopyProp.run(module, func) {
        changed = true;
        let _ = dce::Adce.run(module, func);
    }

    changed
}

/// Run the optimization pipeline on all functions in the module. Bodyless
/// functions (external/native declarations) are skipped.
pub fn optimize_module(module: &mut Module) -> bool {
    let func_count = module.functions.len();
    let mut changed = false;
    for i in 0..func_count {
        let func_id = FuncId::new(i as u32);
        let Some(func) = module.func(func_id) else {
            continue;
        };
        if func.blocks.is_empty() {
            continue;
        }
        changed |= optimize_func(module, func_id);
    }
    changed
}

#[cfg(test)]
mod tests {
    use abcd_ir::{
        BinOp, Block, BlockId, CallKind, ClassData, ClassId, CmpOp, ColumnEntry, Const, DebugData,
        Edge, EdgeKind, FuncId, FunctionData, FunctionKind, Inst, InstId, LexEnvKind, LineEntry,
        LocalName, LocalScope, Modifiers, Module, Op, Ty, UnOp, Value, ValueDef, ValueId,
        verify_module,
    };

    use super::*;
    use crate::const_eval::CANONICAL_NAN_BITS;
    use crate::inline::{InlinePolicy, SkipReason, inline_module};

    fn new_func(module: &mut Module, class_id: ClassId, name: &str) -> (FuncId, BlockId) {
        let sym = module.sym.intern(name);
        let fid = FuncId::new(module.functions.len() as u32);
        let mut fdata = FunctionData::new(class_id, sym, FunctionKind::Function);
        fdata.modifiers = Modifiers::STATIC;
        let entry = BlockId::new(module.blocks.len() as u32);
        module.blocks.push(Block::default());
        fdata.blocks.push(entry);
        module.functions.push(fdata);
        module.classes[class_id.index()].methods.push(fid);
        (fid, entry)
    }

    fn emit_val(module: &mut Module, block: BlockId, op: Op) -> (InstId, ValueId) {
        let iid = InstId::new(module.insts.len() as u32);
        let vid = ValueId::new(module.values.len() as u32);
        module.values.push(Value {
            def: ValueDef::Inst(iid),
            ty: Ty::Any,
        });
        module.insts.push(Inst {
            op,
            result: Some(vid),
            block,
            loc: None,
        });
        module.blocks[block.index()].insts.push(iid);
        (iid, vid)
    }

    fn emit_void(module: &mut Module, block: BlockId, op: Op) -> InstId {
        let iid = InstId::new(module.insts.len() as u32);
        module.insts.push(Inst {
            op,
            result: None,
            block,
            loc: None,
        });
        module.blocks[block.index()].insts.push(iid);
        iid
    }

    #[test]
    fn unit_copyprop_mov_chain_and_adce_debug_pruning_verify() {
        let mut module = Module::new();
        let cname = module.sym.intern("L_GLOBAL;");
        let cid = ClassId::new(0);
        module.classes.push(ClassData::new(cname, cname));

        let (fid, entry) = new_func(&mut module, cid, "main");
        let c42 = module.consts.intern(Const::number(42.0));
        let (i_ld, v0) = emit_val(&mut module, entry, Op::LoadConst(c42));
        let (i_m1, v1) = emit_val(&mut module, entry, Op::Mov { src: v0 });
        let (i_m2, v2) = emit_val(&mut module, entry, Op::Mov { src: v1 });
        let i_ret = emit_void(&mut module, entry, Op::Return { value: Some(v2) });

        let dead_bb = BlockId::new(module.blocks.len() as u32);
        module.blocks.push(Block::default());
        module.functions[fid.index()].blocks.push(dead_bb);
        let i_dead = emit_void(&mut module, dead_bb, Op::Return { value: None });

        let x_sym = module.sym.intern("x");
        let y_sym = module.sym.intern("y");
        module.functions[fid.index()].debug = Some(DebugData {
            source_file: None,
            source_code: None,
            line_table: vec![
                LineEntry {
                    inst: i_ld,
                    line: 1,
                },
                LineEntry {
                    inst: i_m1,
                    line: 2,
                },
                LineEntry {
                    inst: i_dead,
                    line: 99,
                },
            ],
            column_table: vec![
                ColumnEntry {
                    inst: i_m2,
                    column: 4,
                },
                ColumnEntry {
                    inst: i_ret,
                    column: 8,
                },
            ],
            param_names: Vec::new(),
            local_names: vec![
                LocalName {
                    name: x_sym,
                    ty: None,
                    scope: Some(LocalScope {
                        start: i_m1,
                        end: i_ret,
                    }),
                },
                LocalName {
                    name: y_sym,
                    ty: None,
                    scope: Some(LocalScope {
                        start: i_dead,
                        end: i_dead,
                    }),
                },
            ],
            scope_names: None,
        });
        assert!(verify_module(&module).is_ok());

        assert!(optimize_func(&mut module, fid));
        let rep = verify_module(&module);
        assert!(rep.is_ok(), "verify errors: {:?}", rep.errors);

        let ret_op = &module.insts[i_ret.index()].op;
        assert!(matches!(*ret_op, Op::Return { value: Some(v) } if v == v0));

        let dbg = module.functions[fid.index()].debug.as_ref().unwrap();
        assert_eq!(dbg.line_table.len(), 1);
        assert_eq!(dbg.line_table[0].inst, i_ld);
        assert_eq!(dbg.column_table.len(), 1);
        assert_eq!(dbg.column_table[0].inst, i_ret);
        assert_eq!(
            dbg.local_names[0].scope,
            Some(LocalScope {
                start: i_ret,
                end: i_ret
            })
        );
        assert_eq!(dbg.local_names[1].scope, None);
    }

    #[test]
    fn unit_peephole_and_sccp_parity_and_inline_methodref_guard() {
        for run_sccp in [false, true] {
            let mut module = Module::new();
            let cname = module.sym.intern("L_GLOBAL;");
            let cid = ClassId::new(0);
            module.classes.push(ClassData::new(cname, cname));
            let (fid, entry) = new_func(&mut module, cid, "f");

            let empty_s = module.sym.intern("");
            let hi_s = module.sym.intern("hi");
            let c_empty = module.consts.intern(Const::String(empty_s));
            let c_hi = module.consts.intern(Const::String(hi_s));
            let c_undef = module.consts.intern(Const::Undefined);
            let c_two = module.consts.intern(Const::number(2.0));
            let c_ten = module.consts.intern(Const::number(10.0));

            let (_, v_empty) = emit_val(&mut module, entry, Op::LoadConst(c_empty));
            let (_, v_hi) = emit_val(&mut module, entry, Op::LoadConst(c_hi));
            let (_, v_undef) = emit_val(&mut module, entry, Op::LoadConst(c_undef));
            let (_, v_two) = emit_val(&mut module, entry, Op::LoadConst(c_two));
            let (_, v_ten) = emit_val(&mut module, entry, Op::LoadConst(c_ten));

            let (i_pow, _) = emit_val(
                &mut module,
                entry,
                Op::BinaryOp {
                    op: BinOp::Exp,
                    left: v_ten,
                    right: v_two,
                },
            );
            let (i_nan, _) = emit_val(
                &mut module,
                entry,
                Op::BinaryOp {
                    op: BinOp::Add,
                    left: v_two,
                    right: v_undef,
                },
            );
            let (i_t_empty, _) = emit_val(
                &mut module,
                entry,
                Op::UnaryOp {
                    op: UnOp::IsTrue,
                    operand: v_empty,
                },
            );
            let (i_t_hi, _) = emit_val(
                &mut module,
                entry,
                Op::UnaryOp {
                    op: UnOp::IsTrue,
                    operand: v_hi,
                },
            );
            let (i_seq, v_seq) = emit_val(
                &mut module,
                entry,
                Op::Compare {
                    op: CmpOp::StrictEq,
                    left: v_empty,
                    right: v_hi,
                },
            );
            let b_true = BlockId::new(module.blocks.len() as u32);
            module.blocks.push(Block {
                preds: vec![Edge {
                    from: entry,
                    kind: EdgeKind::Normal,
                }],
                insts: Vec::new(),
            });
            module.functions[fid.index()].blocks.push(b_true);
            emit_void(
                &mut module,
                entry,
                Op::CondBranch {
                    cond: v_seq,
                    true_dest: b_true,
                    false_dest: b_true,
                },
            );
            let (_, p_val) = emit_val(
                &mut module,
                b_true,
                Op::Phi {
                    entries: vec![(
                        Edge {
                            from: entry,
                            kind: EdgeKind::Normal,
                        },
                        v_two,
                    )],
                },
            );
            emit_void(&mut module, b_true, Op::Return { value: Some(p_val) });
            assert!(verify_module(&module).is_ok());

            if run_sccp {
                sccp::Sccp.run(&mut module, fid);
            } else {
                peephole::Peephole.run(&mut module, fid);
            }
            assert!(verify_module(&module).is_ok());

            let get_c = |iid: InstId| match &module.insts[iid.index()].op {
                Op::LoadConst(k) => module.consts.get(*k).cloned(),
                other => panic!("expected LoadConst, got {other:?}"),
            };
            assert_eq!(get_c(i_pow), Some(Const::number(1024.0)));
            assert_eq!(get_c(i_nan), Some(Const::Number(CANONICAL_NAN_BITS)));
            assert_eq!(get_c(i_t_empty), Some(Const::Bool(false)));
            assert_eq!(get_c(i_t_hi), Some(Const::Bool(true)));
            assert_eq!(get_c(i_seq), Some(Const::Bool(false)));
            assert_eq!(module.blocks[b_true.index()].preds.len(), 1);
        }

        // Inline guard: MethodRef inside ObjectLiteral referencing a nested
        // function that reads outer lexenv must reject with CalleeDefinesClosure.
        let mut module = Module::new();
        let cname = module.sym.intern("L_GLOBAL;");
        let cid = ClassId::new(0);
        module.classes.push(ClassData::new(cname, cname));

        let (nested, nested_entry) = new_func(&mut module, cid, "nested");
        for i in 0..3 {
            let pv = ValueId::new(module.values.len() as u32);
            module.values.push(Value {
                def: ValueDef::Param(i),
                ty: Ty::Any,
            });
            module.functions[nested.index()].params.push(pv);
        }
        let (_, lex_v) = emit_val(
            &mut module,
            nested_entry,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: LexEnvKind::Plain,
            },
        );
        emit_void(&mut module, nested_entry, Op::Return { value: Some(lex_v) });

        let (callee, callee_entry) = new_func(&mut module, cid, "callee");
        for i in 0..3 {
            let pv = ValueId::new(module.values.len() as u32);
            module.values.push(Value {
                def: ValueDef::Param(i),
                ty: Ty::Any,
            });
            module.functions[callee.index()].params.push(pv);
        }
        let m_sym = module.sym.intern("m");
        let k_cid = module.consts.intern(Const::String(m_sym));
        let mref_cid = module.consts.intern(Const::method_ref(nested));
        let obj_cid = module.consts.intern(Const::ObjectLiteral {
            keys: vec![k_cid],
            values: vec![mref_cid],
        });
        let (_, obj_v) = emit_val(
            &mut module,
            callee_entry,
            Op::AllocObject { shape: obj_cid },
        );
        emit_void(&mut module, callee_entry, Op::Return { value: Some(obj_v) });

        let (_caller, caller_entry) = new_func(&mut module, cid, "caller");
        let (_, df) = emit_val(
            &mut module,
            caller_entry,
            Op::DefineFunc {
                body: callee,
                captures: Vec::new(),
                length: 0,
            },
        );
        let (_, cl) = emit_val(&mut module, caller_entry, Op::AllocClosure { func: df });
        let (_, call_v) = emit_val(
            &mut module,
            caller_entry,
            Op::Call {
                callee: cl,
                this: None,
                args: Vec::new(),
                kind: CallKind::Dynamic,
            },
        );
        emit_void(
            &mut module,
            caller_entry,
            Op::Return {
                value: Some(call_v),
            },
        );
        assert!(verify_module(&module).is_ok());

        let rep = inline_module(&mut module, &InlinePolicy::default());
        assert_eq!(rep.sites_inlined, 0);
        assert_eq!(rep.skips.get(&SkipReason::CalleeDefinesClosure), Some(&1));
        assert!(verify_module(&module).is_ok());
    }

    #[test]
    fn unit_condbranch_throwing_cond_entry_seeding_and_ic8_budget() {
        // 1a) Verified CondBranch(throwing_cond, T, T) -> Branch(T), preserving
        //     TryGetGlobal side effects after Adce + CfgSimplify!
        let mut module = Module::new();
        let cname = module.sym.intern("L_GLOBAL;");
        let cid = ClassId::new(0);
        module.classes.push(ClassData::new(cname, cname));
        let (fid, entry) = new_func(&mut module, cid, "f_same_arm");
        let g_sym = module.sym.intern("maybeGetter");
        let (get_iid, cond_v) = emit_val(
            &mut module,
            entry,
            Op::TryGetGlobal {
                name: g_sym,
                default: None,
            },
        );
        let c10 = module.consts.intern(Const::number(10.0));
        let (_, v10) = emit_val(&mut module, entry, Op::LoadConst(c10));
        let target = BlockId::new(module.blocks.len() as u32);
        module.blocks.push(Block {
            preds: vec![Edge {
                from: entry,
                kind: EdgeKind::Normal,
            }],
            insts: Vec::new(),
        });
        module.functions[fid.index()].blocks.push(target);
        emit_void(
            &mut module,
            entry,
            Op::CondBranch {
                cond: cond_v,
                true_dest: target,
                false_dest: target,
            },
        );
        let (_, pv) = emit_val(
            &mut module,
            target,
            Op::Phi {
                entries: vec![(
                    Edge {
                        from: entry,
                        kind: EdgeKind::Normal,
                    },
                    v10,
                )],
            },
        );
        emit_void(&mut module, target, Op::Return { value: Some(pv) });
        assert!(verify_module(&module).is_ok());
        assert!(optimize_func(&mut module, fid));
        assert!(verify_module(&module).is_ok());
        let has_getter = module.functions[fid.index()]
            .blocks
            .iter()
            .any(|&bb| module.blocks[bb.index()].insts.contains(&get_iid));
        assert!(has_getter, "throwing cond producer must survive Adce");

        // 1b) Unverified duplicate-pred CondBranch(c, T, T) deduplicates both
        //     `preds` and `Phi` entries into a verifier-clean `Branch(T)`!
        let mut dup_mod = Module::new();
        let cname = dup_mod.sym.intern("L_GLOBAL;");
        dup_mod.classes.push(ClassData::new(cname, cname));
        let (dfid, d_entry) = new_func(&mut dup_mod, ClassId::new(0), "f_dup_arm");
        let c1 = dup_mod.consts.intern(Const::Bool(true));
        let (_, dc) = emit_val(&mut dup_mod, d_entry, Op::LoadConst(c1));
        let d_target = BlockId::new(dup_mod.blocks.len() as u32);
        dup_mod.blocks.push(Block {
            preds: vec![
                Edge {
                    from: d_entry,
                    kind: EdgeKind::Normal,
                },
                Edge {
                    from: d_entry,
                    kind: EdgeKind::Normal,
                },
            ],
            insts: Vec::new(),
        });
        dup_mod.functions[dfid.index()].blocks.push(d_target);
        emit_void(
            &mut dup_mod,
            d_entry,
            Op::CondBranch {
                cond: dc,
                true_dest: d_target,
                false_dest: d_target,
            },
        );
        let (_, dpv) = emit_val(
            &mut dup_mod,
            d_target,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: d_entry,
                            kind: EdgeKind::Normal,
                        },
                        dc,
                    ),
                    (
                        Edge {
                            from: d_entry,
                            kind: EdgeKind::Normal,
                        },
                        dc,
                    ),
                ],
            },
        );
        emit_void(&mut dup_mod, d_target, Op::Return { value: Some(dpv) });
        assert!(peephole::Peephole.run(&mut dup_mod, dfid));
        assert!(verify_module(&dup_mod).is_ok());

        // 2) Sccp entry CondBranch seeding folds downstream diamond phi in Round 1.
        let mut s_mod = Module::new();
        let cname = s_mod.sym.intern("L_GLOBAL;");
        s_mod.classes.push(ClassData::new(cname, cname));
        let (sf, s_entry) = new_func(&mut s_mod, ClassId::new(0), "f_seed");
        let live_bb = BlockId::new(s_mod.blocks.len() as u32);
        s_mod.blocks.push(Block {
            preds: vec![Edge {
                from: s_entry,
                kind: EdgeKind::Normal,
            }],
            insts: Vec::new(),
        });
        let dead_bb = BlockId::new(s_mod.blocks.len() as u32);
        s_mod.blocks.push(Block {
            preds: vec![Edge {
                from: s_entry,
                kind: EdgeKind::Normal,
            }],
            insts: Vec::new(),
        });
        let join_bb = BlockId::new(s_mod.blocks.len() as u32);
        s_mod.blocks.push(Block {
            preds: vec![
                Edge {
                    from: live_bb,
                    kind: EdgeKind::Normal,
                },
                Edge {
                    from: dead_bb,
                    kind: EdgeKind::Normal,
                },
            ],
            insts: Vec::new(),
        });
        s_mod.functions[sf.index()]
            .blocks
            .extend([live_bb, dead_bb, join_bb]);
        let c_true = s_mod.consts.intern(Const::Bool(true));
        let (_, cond_true) = emit_val(&mut s_mod, s_entry, Op::LoadConst(c_true));
        emit_void(
            &mut s_mod,
            s_entry,
            Op::CondBranch {
                cond: cond_true,
                true_dest: live_bb,
                false_dest: dead_bb,
            },
        );
        let c100 = s_mod.consts.intern(Const::number(100.0));
        let (_, v_live) = emit_val(&mut s_mod, live_bb, Op::LoadConst(c100));
        emit_void(&mut s_mod, live_bb, Op::Branch { dest: join_bb });
        let c999 = s_mod.consts.intern(Const::number(999.0));
        let (_, v_dead) = emit_val(&mut s_mod, dead_bb, Op::LoadConst(c999));
        emit_void(&mut s_mod, dead_bb, Op::Branch { dest: join_bb });
        let (phi_iid, phi_v) = emit_val(
            &mut s_mod,
            join_bb,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: live_bb,
                            kind: EdgeKind::Normal,
                        },
                        v_live,
                    ),
                    (
                        Edge {
                            from: dead_bb,
                            kind: EdgeKind::Normal,
                        },
                        v_dead,
                    ),
                ],
            },
        );
        emit_void(&mut s_mod, join_bb, Op::Return { value: Some(phi_v) });
        assert!(verify_module(&s_mod).is_ok());
        assert!(sccp::Sccp.run(&mut s_mod, sf));
        assert!(verify_module(&s_mod).is_ok());
        assert!(
            matches!(s_mod.insts[phi_iid.index()].op, Op::LoadConst(k) if s_mod.consts.get(k) == Some(&Const::number(100.0))),
            "entry CondBranch seeding must fold join phi in a single Sccp run"
        );

        // 3) Inline fresh caller const materialization + ic8 (254) budget check.
        let mut i_mod = Module::new();
        let cname = i_mod.sym.intern("L_GLOBAL;");
        i_mod.classes.push(ClassData::new(cname, cname));
        let (callee, c_entry) = new_func(&mut i_mod, ClassId::new(0), "callee_const");
        for idx in 0..4 {
            let pv = ValueId::new(i_mod.values.len() as u32);
            i_mod.values.push(Value {
                def: ValueDef::Param(idx),
                ty: Ty::Any,
            });
            i_mod.functions[callee.index()].params.push(pv);
        }
        let x_param = i_mod.functions[callee.index()].params[3];
        let c7 = i_mod.consts.intern(Const::number(7.0));
        let frame_c7 = ValueId::new(i_mod.values.len() as u32);
        i_mod.values.push(Value {
            def: ValueDef::Const(c7),
            ty: Ty::Any,
        });
        i_mod.functions[callee.index()]
            .frame_init_consts
            .push(frame_c7);
        let (_, sum_v) = emit_val(
            &mut i_mod,
            c_entry,
            Op::BinaryOp {
                op: BinOp::Add,
                left: frame_c7,
                right: x_param,
            },
        );
        emit_void(&mut i_mod, c_entry, Op::Return { value: Some(sum_v) });

        let (_caller, caller_entry) = new_func(&mut i_mod, ClassId::new(0), "caller_const");
        let (_, df) = emit_val(
            &mut i_mod,
            caller_entry,
            Op::DefineFunc {
                body: callee,
                captures: Vec::new(),
                length: 1,
            },
        );
        let (_, cl) = emit_val(&mut i_mod, caller_entry, Op::AllocClosure { func: df });
        let c5 = i_mod.consts.intern(Const::number(5.0));
        let (_, v5) = emit_val(&mut i_mod, caller_entry, Op::LoadConst(c5));
        let (_, r1) = emit_val(
            &mut i_mod,
            caller_entry,
            Op::Call {
                callee: cl,
                this: None,
                args: vec![v5],
                kind: CallKind::Dynamic,
            },
        );
        let (_, r2) = emit_val(
            &mut i_mod,
            caller_entry,
            Op::Call {
                callee: cl,
                this: None,
                args: vec![r1],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut i_mod, caller_entry, Op::Return { value: Some(r2) });
        assert!(verify_module(&i_mod).is_ok());
        let rep = inline_module(&mut i_mod, &InlinePolicy::default());
        assert_eq!(rep.sites_inlined, 2);
        assert!(verify_module(&i_mod).is_ok());
        assert!(optimize_module(&mut i_mod));
        assert!(verify_module(&i_mod).is_ok());

        // ic8 overflow (> 254) -> CallerBudgetExhausted.
        // Caller: 251 BinaryOps (251 ic8) + DefineFunc (1 ic8) + Call (2 ic8) = 254 ic8.
        // Callee: 3 BinaryOps (3 ic8) -> 254 - 2 + 3 = 255 > 254!
        let mut b_mod = Module::new();
        let cname = b_mod.sym.intern("L_GLOBAL;");
        b_mod.classes.push(ClassData::new(cname, cname));
        let (ic_callee, ic_c_entry) = new_func(&mut b_mod, ClassId::new(0), "ic_callee");
        for idx in 0..4 {
            let pv = ValueId::new(b_mod.values.len() as u32);
            b_mod.values.push(Value {
                def: ValueDef::Param(idx),
                ty: Ty::Any,
            });
            b_mod.functions[ic_callee.index()].params.push(pv);
        }
        let arg0 = b_mod.functions[ic_callee.index()].params[3];
        let mut acc = arg0;
        for _ in 0..3 {
            let (_, next) = emit_val(
                &mut b_mod,
                ic_c_entry,
                Op::BinaryOp {
                    op: BinOp::Add,
                    left: acc,
                    right: arg0,
                },
            );
            acc = next;
        }
        emit_void(&mut b_mod, ic_c_entry, Op::Return { value: Some(acc) });

        let (ic_caller, ic_caller_entry) = new_func(&mut b_mod, ClassId::new(0), "ic_caller");
        let pv0 = ValueId::new(b_mod.values.len() as u32);
        b_mod.values.push(Value {
            def: ValueDef::Param(0),
            ty: Ty::Any,
        });
        b_mod.functions[ic_caller.index()].params.push(pv0);
        let mut cur = pv0;
        for _ in 0..251 {
            let (_, next) = emit_val(
                &mut b_mod,
                ic_caller_entry,
                Op::BinaryOp {
                    op: BinOp::Add,
                    left: cur,
                    right: pv0,
                },
            );
            cur = next;
        }
        let (_, df) = emit_val(
            &mut b_mod,
            ic_caller_entry,
            Op::DefineFunc {
                body: ic_callee,
                captures: Vec::new(),
                length: 1,
            },
        );
        let (_, cl) = emit_val(&mut b_mod, ic_caller_entry, Op::AllocClosure { func: df });
        let (_, res) = emit_val(
            &mut b_mod,
            ic_caller_entry,
            Op::Call {
                callee: cl,
                this: None,
                args: vec![cur],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut b_mod, ic_caller_entry, Op::Return { value: Some(res) });
        assert!(verify_module(&b_mod).is_ok());
        let ic_rep = inline_module(
            &mut b_mod,
            &InlinePolicy {
                max_callee_insts: 64,
                max_inlined_insts_per_caller: 10_000,
            },
        );
        assert_eq!(ic_rep.sites_inlined, 0);
        assert_eq!(
            ic_rep.skips.get(&SkipReason::CallerBudgetExhausted),
            Some(&1)
        );
        assert!(verify_module(&b_mod).is_ok());
    }
}
