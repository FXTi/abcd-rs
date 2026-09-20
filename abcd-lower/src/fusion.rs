//! Emission-fusion analysis: find the v0.2 instructions that lowering
//! fuses into an adjacent consumer, exactly inverting the lift's
//! expansion mappings (compare.rs divergence rule 3).
//!
//! v0.2's lift MATERIALIZES what v0.1 packs into one instruction:
//!
//! - `definefunc` → `DefineFunc` + `AllocClosure`;
//! - `definemethod` → `DefineFunc` + `AllocClosure` + `DefineMethod`;
//! - constant property indices → `LoadConst` + `LoadPropIdx`/`StorePropIdx`;
//! - tolerant global loads → `LoadConst(undefined)` + `TryGetGlobal`.
//!
//! The materialized values are v0.1-invisible: v0.1's register allocator
//! never sees them, so if the v0.2 allocator colored them they would
//! perturb every other value's coloring and break byte identity with the
//! v0.1 pipeline. This module computes, BEFORE register allocation, the
//! set of instructions whose emission fuses into their consumer
//! ([`Suppression::insts`]) and whose results must never be colored
//! ([`Suppression::values`]). Register allocation then sees exactly the
//! value universe v0.1 sees, and isel skips the suppressed instructions,
//! emitting the fused bytecode at the consumer.
//!
//! The fusion conditions are STATIC (adjacency, single-use, constant
//! payload) — the pre-regalloc computation and the isel-time check always
//! agree.

use std::collections::HashSet;

use abcd_ir2::{Const, InstId, Module, Op, ValueDef, ValueId};

/// The result of fusion analysis for one function.
#[derive(Debug, Default)]
pub struct Suppression {
    /// Instructions that must not emit (their bytecodes fold into an
    /// adjacent consumer's).
    pub insts: HashSet<InstId>,
    /// Values that must never be colored (results of suppressed
    /// instructions) nor read from a register home.
    pub values: HashSet<ValueId>,
}

/// Count the uses of every value in the function (all op operands,
/// including phi entries).
fn use_counts(module: &Module, blocks: &[abcd_ir2::BlockId]) -> std::collections::HashMap<ValueId, usize> {
    let mut counts: std::collections::HashMap<ValueId, usize> = std::collections::HashMap::new();
    for &bb in blocks {
        let Some(block) = module.block(bb) else { continue };
        for &iid in &block.insts {
            let Some(inst) = module.inst(iid) else { continue };
            for v in inst.op.operands() {
                *counts.entry(v).or_default() += 1;
            }
        }
    }
    counts
}

/// The payload of a [`Op::LoadConst`] when it is a number constant.
fn number_const(module: &Module, iid: InstId) -> Option<f64> {
    let inst = module.inst(iid)?;
    let Op::LoadConst(cid) = &inst.op else {
        return None;
    };
    module.consts.get(*cid)?.as_f64()
}

/// The payload of a [`Op::LoadConst`] when it is the `undefined` constant.
fn is_undefined_const_load(module: &Module, iid: InstId) -> bool {
    let Some(inst) = module.inst(iid) else {
        return false;
    };
    let Op::LoadConst(cid) = &inst.op else {
        return false;
    };
    matches!(module.consts.get(*cid), Some(Const::Undefined))
}

/// The defining instruction of a value, when it is an instruction result.
fn def_inst(module: &Module, v: ValueId) -> Option<InstId> {
    match module.value(v)?.def {
        ValueDef::Inst(iid) => Some(iid),
        _ => None,
    }
}

/// Whether `v` is used exactly once, by `consumer`.
fn single_use(
    counts: &std::collections::HashMap<ValueId, usize>,
    v: ValueId,
    consumer: InstId,
    module: &Module,
) -> bool {
    if counts.get(&v).copied().unwrap_or(0) != 1 {
        return false;
    }
    module
        .inst(consumer)
        .is_some_and(|inst| inst.op.operands().contains(&v))
}

/// Compute the suppression set for one function.
pub fn analyze(module: &Module, blocks: &[abcd_ir2::BlockId]) -> Suppression {
    let mut out = Suppression::default();
    let counts = use_counts(module, blocks);

    for &bb in blocks {
        let Some(block) = module.block(bb) else { continue };
        for (pos, &iid) in block.insts.iter().enumerate() {
            let Some(inst) = module.inst(iid) else { continue };
            match &inst.op {
                // `LoadConst(number)` + `LoadPropIdx`/`StorePropIdx` →
                // ld/stobjbyindex. The fused immediate round-trips any
                // integral f64 (the vendor imm is i64; the lift stored it
                // as f64), so no range check is needed for EXACTNESS —
                // but the const must be integral, or the source could
                // never have been a by-index bytecode.
                Op::LoadPropIdx { index, .. }
                | Op::StorePropIdx { index, .. }
                | Op::StoreOwnPropIdx { index, .. } => {
                    let Some(const_inst) = def_inst(module, *index) else {
                        continue;
                    };
                    if pos == 0 || block.insts[pos - 1] != const_inst {
                        continue; // not adjacent in this block
                    }
                    let Some(num) = number_const(module, const_inst) else {
                        continue;
                    };
                    if num.fract() != 0.0 {
                        continue; // a by-index immediate is always integral
                    }
                    if !single_use(&counts, *index, iid, module) {
                        continue;
                    }
                    out.insts.insert(const_inst);
                    out.values.insert(*index);
                }
                // `LoadConst(undefined)` + `TryGetGlobal` →
                // tryldglobalbyname.
                Op::TryGetGlobal {
                    default: Some(dflt),
                    ..
                } => {
                    let Some(const_inst) = def_inst(module, *dflt) else {
                        continue;
                    };
                    if pos == 0 || block.insts[pos - 1] != const_inst {
                        continue;
                    }
                    if !is_undefined_const_load(module, const_inst) {
                        continue;
                    }
                    if !single_use(&counts, *dflt, iid, module) {
                        continue;
                    }
                    out.insts.insert(const_inst);
                    out.values.insert(*dflt);
                }
                _ => {}
            }
        }
    }

    // The define chains: `DefineFunc` + `AllocClosure` → definefunc, and
    // `DefineFunc` + `AllocClosure` + `DefineMethod` → definemethod.
    // Chains suppress from the CONSUMER side: an AllocClosure suppresses
    // its adjacent single-use DefineFunc; a DefineMethod suppresses its
    // adjacent single-use AllocClosure when that closure's DefineFunc is
    // itself suppressible (adjacent, single-use).
    for &bb in blocks {
        let Some(block) = module.block(bb) else { continue };
        for (pos, &iid) in block.insts.iter().enumerate() {
            let Some(inst) = module.inst(iid) else { continue };
            let func_val = match &inst.op {
                Op::AllocClosure { func } => Some((*func, None::<InstId>)),
                Op::DefineMethod { func, .. } => Some((*func, Some(iid))),
                _ => None,
            };
            let Some((func_val, define_method)) = func_val else {
                continue;
            };

            // Resolve the chain: DefineFunc → AllocClosure → (DefineMethod).
            let (closure_inst, definefunc_value) = match define_method {
                Some(_) => {
                    // func must be the result of an adjacent AllocClosure.
                    let Some(closure_iid) = def_inst(module, func_val) else {
                        continue;
                    };
                    if pos == 0 || block.insts[pos - 1] != closure_iid {
                        continue;
                    }
                    let Some(closure) = module.inst(closure_iid) else {
                        continue;
                    };
                    let Op::AllocClosure { func } = &closure.op else {
                        continue;
                    };
                    if !single_use(&counts, func_val, iid, module) {
                        continue;
                    }
                    (Some(closure_iid), *func)
                }
                None => (None, func_val),
            };

            // The DefineFunc must be adjacent (before the closure, or
            // before the closure's consumer) and single-use.
            let Some(definefunc_iid) = def_inst(module, definefunc_value) else {
                continue;
            };
            let chain_consumer = closure_inst.unwrap_or(iid);
            let Some(definefunc) = module.inst(definefunc_iid) else {
                continue;
            };
            let Op::DefineFunc { captures, .. } = &definefunc.op else {
                continue;
            };
            if !captures.is_empty() {
                continue; // no vendor encoding for explicit captures
            }
            if !single_use(&counts, definefunc_value, chain_consumer, module) {
                continue;
            }
            // Adjacency: the DefineFunc must immediately precede the
            // closure (or the closure's own consumer position).
            let consumer_pos = match closure_inst {
                Some(ciid) => block.insts.iter().position(|&x| x == ciid),
                None => Some(pos),
            };
            match consumer_pos {
                Some(cpos) if cpos > 0 && block.insts[cpos - 1] == definefunc_iid => {}
                _ => continue,
            }

            out.insts.insert(definefunc_iid);
            out.values.insert(definefunc_value);
            if let Some(ciid) = closure_inst {
                out.insts.insert(ciid);
                out.values.insert(func_val);
            }
        }
    }

    out
}
