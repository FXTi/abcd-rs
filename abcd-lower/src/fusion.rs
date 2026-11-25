//! Emission-fusion pre-pass (`design/ir.md` §5): identifies single-use IR
//! expansion instructions whose emission folds directly into an adjacent
//! consumer bytecode.
//!
//! `abcd-lift` decomposes several composite bytecodes into orthogonal IR ops:
//!
//! - `definefunc` → `DefineFunc` + `AllocClosure`;
//! - `definemethod` → `DefineFunc` + `AllocClosure` + `DefineMethod`;
//! - constant property indices → `LoadConst` + `LoadPropIdx`/`StorePropIdx`/`StoreOwnPropIdx`;
//! - tolerant global loads → `LoadConst(undefined)` + `TryGetGlobal`.
//!
//! If the register allocator colored those intermediate expansion values, they
//! would consume registers and perturb interference coloring. This module
//! computes, BEFORE register allocation, the set of instructions whose
//! emission fuses into their consumer ([`Suppression::insts`]) and whose
//! results must never be colored ([`Suppression::values`]). Instruction
//! selection then skips the suppressed instructions and emits the single
//! composite bytecode at the consumer.
//!
//! The fusion conditions are STATIC (adjacency, single-use, constant
//! payload) — the pre-regalloc computation and the isel-time check always
//! agree.

use std::collections::{HashMap, HashSet};

use abcd_ir::{BlockId, Const, InstId, Module, Op, UnOp, ValueDef, ValueId};

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

/// Extract an exact `0..=u32::MAX` element index from `c`, excluding `-0.0`,
/// negative integers, fractional floats, and values `>= 2^32` (`#61` `R3-X5`).
#[must_use]
pub(crate) fn const_u32_index(c: &Const) -> Option<u32> {
    match c {
        Const::Int8(n) => Some(u32::from(*n)),
        Const::Int32(n) if (*n as i32) >= 0 => Some(*n),
        Const::Number(bits) => {
            let n = f64::from_bits(*bits);
            if !n.is_finite()
                || (n == 0.0 && n.is_sign_negative())
                || n < 0.0
                || n > f64::from(u32::MAX)
                || n.fract() != 0.0
            {
                return None;
            }
            Some(n as u32)
        }
        _ => None,
    }
}

type SingleConsumerMap = HashMap<ValueId, Option<InstId>>;
type InstPosMap = HashMap<InstId, (BlockId, usize)>;

/// Precompute single-use consumers and `(BlockId, pos)` instruction positions
/// in a single `O(B + I)` pass (`#61` `R3-X7`).
fn index_uses_and_positions(
    module: &Module,
    blocks: &[BlockId],
) -> (SingleConsumerMap, InstPosMap) {
    let mut single_consumer: SingleConsumerMap = HashMap::new();
    let mut inst_pos: InstPosMap = HashMap::new();
    for &bb in blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for (pos, &iid) in block.insts.iter().enumerate() {
            inst_pos.entry(iid).or_insert((bb, pos));
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            inst.op.for_each_operand(|v| {
                single_consumer
                    .entry(v)
                    .and_modify(|slot| *slot = None)
                    .or_insert(Some(iid));
            });
        }
    }
    (single_consumer, inst_pos)
}

/// The payload of a [`Op::LoadConst`] when it is a valid `0..=u32::MAX` index.
fn u32_index_const_load(module: &Module, iid: InstId) -> Option<u32> {
    let inst = module.inst(iid)?;
    let Op::LoadConst(cid) = &inst.op else {
        return None;
    };
    const_u32_index(module.consts.get(*cid)?)
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

/// Whether `v` is used once across the whole function, by `consumer`.
#[inline]
fn single_use(
    single_consumer: &HashMap<ValueId, Option<InstId>>,
    v: ValueId,
    consumer: InstId,
) -> bool {
    single_consumer.get(&v).copied().flatten() == Some(consumer)
}

/// Compute the suppression set for one function.
pub fn analyze(module: &Module, blocks: &[BlockId]) -> Suppression {
    let mut out = Suppression::default();
    let (single_consumer, inst_pos) = index_uses_and_positions(module, blocks);

    for &bb in blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for (pos, &iid) in block.insts.iter().enumerate() {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            match &inst.op {
                // `LoadConst(0..=u32::MAX)` + `*PropIdx` → `*byindex` (`R3-X5`).
                // Non-constant, negative, `-0.0`, fractional, multi-use, or
                // `>= 2^32` indices stay unfused and lower via `*byvalue`.
                Op::LoadPropIdx { index, .. }
                | Op::StorePropIdx { index, .. }
                | Op::StoreOwnPropIdx { index, .. } => {
                    let Some(const_inst) = def_inst(module, *index) else {
                        continue;
                    };
                    if pos == 0 || block.insts[pos - 1] != const_inst {
                        continue;
                    }
                    if u32_index_const_load(module, const_inst).is_none() {
                        continue;
                    }
                    if !single_use(&single_consumer, *index, iid) {
                        continue;
                    }
                    out.insts.insert(const_inst);
                    out.values.insert(*index);
                }
                // `LoadConst(undefined)` + `TryGetGlobal` → `tryldglobalbyname`.
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
                    if !single_use(&single_consumer, *dflt, iid) {
                        continue;
                    }
                    out.insts.insert(const_inst);
                    out.values.insert(*dflt);
                }
                // `UnaryOp(JumpEqz | JumpNez)` + `CondBranch` → raw `jeqz`/`jnez` (`R3-X1`).
                Op::CondBranch { cond, .. } => {
                    let Some(pred_inst) = def_inst(module, *cond) else {
                        continue;
                    };
                    if pos == 0 || block.insts[pos - 1] != pred_inst {
                        continue;
                    }
                    let is_raw_jump_pred = module.inst(pred_inst).is_some_and(|i| {
                        matches!(
                            i.op,
                            Op::UnaryOp {
                                op: UnOp::JumpEqz | UnOp::JumpNez,
                                ..
                            }
                        )
                    });
                    if !is_raw_jump_pred || !single_use(&single_consumer, *cond, iid) {
                        continue;
                    }
                    out.insts.insert(pred_inst);
                    out.values.insert(*cond);
                }
                _ => {}
            }
        }
    }

    // The define chains: `DefineFunc` + `AllocClosure` → definefunc, and
    // `DefineFunc` + `AllocClosure` + `DefineMethod` → definemethod.
    for &bb in blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for (pos, &iid) in block.insts.iter().enumerate() {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            let func_val = match &inst.op {
                Op::AllocClosure { func } => Some((*func, None::<InstId>)),
                Op::DefineMethod { func, .. } => Some((*func, Some(iid))),
                _ => None,
            };
            let Some((func_val, define_method)) = func_val else {
                continue;
            };

            let (closure_inst, definefunc_value) = match define_method {
                Some(_) => {
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
                    if !single_use(&single_consumer, func_val, iid) {
                        continue;
                    }
                    (Some(closure_iid), *func)
                }
                None => (None, func_val),
            };

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
                continue;
            }
            if !single_use(&single_consumer, definefunc_value, chain_consumer) {
                continue;
            }
            let consumer_pos = match closure_inst {
                Some(ciid) => inst_pos
                    .get(&ciid)
                    .and_then(|&(cbb, cpos)| (cbb == bb).then_some(cpos)),
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
