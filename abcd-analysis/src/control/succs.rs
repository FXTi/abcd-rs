//! CFG successor relations re-exported from [`abcd_ir::cfg`] (`D1`) plus
//! cross-block async/generator resumption pairing (`#81`, `#82`, `#83`).

use std::collections::{HashMap, HashSet};

pub use abcd_ir::cfg::{augmented_succs, augmented_succs_with_map, block_succs, inst_succs};
use abcd_ir::{BlockId, EdgeKind, FuncId, InstId, Module, Op, ValueId};

use crate::dataflow::heap::peel_movs;

/// Walk backward from `resume_iid` within its block and across
/// [`EdgeKind::Normal`] predecessor blocks (iterative workstack + visited
/// `BlockId` guard, cycle-safe) to collect awaited/yielded [`ValueId`]s paired
/// with `genobj` (`#81` `R4-H5`).
///
/// Along each backward path, records `value` on matching
/// [`Op::SuspendGenerator`] (`genobj`) and stops at the nearest preceding
/// matching [`Op::AwaitUncaught`] (`funcobj == genobj`) or intervening
/// [`Op::ResumeGenerator`] (`genobj`), returning deduplicated values in
/// deterministic encounter order.
#[must_use]
pub fn awaited_values_for_resume(
    module: &Module,
    func: FuncId,
    resume_iid: InstId,
    genobj: ValueId,
) -> Vec<ValueId> {
    let Some(func_data) = module.func(func) else {
        return Vec::new();
    };
    let Some(resume_inst) = module.inst(resume_iid) else {
        return Vec::new();
    };
    let start_block = resume_inst.block;
    let Some(start_bb) = module.block(start_block) else {
        return Vec::new();
    };
    let Some(pos) = start_bb.insts.iter().position(|&id| id == resume_iid) else {
        return Vec::new();
    };

    let target_gen = peel_movs(module, genobj);
    let mut out = Vec::new();
    let push_unique = |out: &mut Vec<ValueId>, v: ValueId| {
        if !out.contains(&v) {
            out.push(v);
        }
    };

    // Scan instructions preceding `resume_iid` in `start_block`.
    for &prev_iid in start_bb.insts[..pos].iter().rev() {
        let Some(inst) = module.inst(prev_iid) else {
            continue;
        };
        match &inst.op {
            Op::AwaitUncaught { funcobj, value } if peel_movs(module, *funcobj) == target_gen => {
                push_unique(&mut out, *value);
                return out;
            }
            Op::SuspendGenerator { genobj: g, value } if peel_movs(module, *g) == target_gen => {
                push_unique(&mut out, *value);
            }
            Op::ResumeGenerator { genobj: g } if peel_movs(module, *g) == target_gen => {
                return out;
            }
            _ => {}
        }
    }

    let func_blocks: HashSet<BlockId> = func_data.blocks.iter().copied().collect();
    if !func_blocks.contains(&start_block) {
        return out;
    }

    let mut visited: HashSet<BlockId> = HashSet::new();
    let mut stack: Vec<BlockId> = Vec::new();
    for edge in start_bb.preds.iter().rev() {
        if edge.kind == EdgeKind::Normal && func_blocks.contains(&edge.from) {
            stack.push(edge.from);
        }
    }

    while let Some(bb_id) = stack.pop() {
        if !visited.insert(bb_id) {
            continue;
        }
        let Some(bb) = module.block(bb_id) else {
            continue;
        };
        let mut stopped = false;
        for &prev_iid in bb.insts.iter().rev() {
            let Some(inst) = module.inst(prev_iid) else {
                continue;
            };
            match &inst.op {
                Op::AwaitUncaught { funcobj, value }
                    if peel_movs(module, *funcobj) == target_gen =>
                {
                    push_unique(&mut out, *value);
                    stopped = true;
                    break;
                }
                Op::SuspendGenerator { genobj: g, value }
                    if peel_movs(module, *g) == target_gen =>
                {
                    push_unique(&mut out, *value);
                }
                Op::ResumeGenerator { genobj: g } if peel_movs(module, *g) == target_gen => {
                    stopped = true;
                    break;
                }
                _ => {}
            }
        }
        if !stopped {
            for edge in bb.preds.iter().rev() {
                if edge.kind == EdgeKind::Normal
                    && func_blocks.contains(&edge.from)
                    && !visited.contains(&edge.from)
                {
                    stack.push(edge.from);
                }
            }
        }
    }

    out
}

/// Pre-index every [`Op::ResumeGenerator`] instruction across
/// `module.functions` to its backward-paired awaited/yielded [`ValueId`]s.
#[must_use]
pub fn build_await_resume_map(module: &Module) -> HashMap<InstId, Vec<ValueId>> {
    let mut map = HashMap::new();
    for (fi, f) in module.functions.iter().enumerate() {
        let fid = FuncId::new(fi as u32);
        for &b in &f.blocks {
            let Some(bb) = module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                if let Some(Op::ResumeGenerator { genobj }) = module.inst(iid).map(|i| &i.op) {
                    let vals = awaited_values_for_resume(module, fid, iid, *genobj);
                    if !vals.is_empty() {
                        map.insert(iid, vals);
                    }
                }
            }
        }
    }
    map
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::*;

    #[test]
    fn cond_branch_same_target_is_deduplicated() {
        let b = BlockId::new(3);
        let cond = ValueId::new(0);
        assert_eq!(
            inst_succs(&Op::CondBranch {
                cond,
                true_dest: b,
                false_dest: b,
            }),
            vec![b]
        );
    }

    #[test]
    fn cross_block_awaited_values_for_resume_across_split_try() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let b0 = entry_of(&m, f);
        let b1 = add_block(&mut m, f);
        let b2 = add_block(&mut m, f);
        let handler = add_block(&mut m, f);

        let genobj = emit(&mut m, b0, Op::AsyncFunctionEnter);
        let promised = load_string(&mut m, b0, "payload");
        let aw = emit(
            &mut m,
            b0,
            Op::AwaitUncaught {
                funcobj: genobj,
                value: promised,
            },
        );
        emit_void(&mut m, b0, Op::Branch { dest: b1 });

        let _ = emit(&mut m, b1, Op::SuspendGenerator { genobj, value: aw });
        emit_void(&mut m, b1, Op::Branch { dest: b2 });

        let resumed = emit(&mut m, b2, Op::ResumeGenerator { genobj });
        let resume_iid = match m.value(resumed).unwrap().def {
            abcd_ir::ValueDef::Inst(i) => i,
            _ => unreachable!(),
        };
        emit_void(
            &mut m,
            b2,
            Op::Return {
                value: Some(resumed),
            },
        );

        let exc = add_exception_param(&mut m, handler);
        emit_void(&mut m, handler, Op::Return { value: Some(exc) });

        link(&mut m, b0, b1);
        link(&mut m, b1, b2);
        add_try(&mut m, f, vec![b0, b1, b2], handler, exc);

        let vals = awaited_values_for_resume(&m, f, resume_iid, genobj);
        assert_eq!(vals, vec![aw, promised]);

        let map = build_await_resume_map(&m);
        assert_eq!(map.get(&resume_iid), Some(&vec![aw, promised]));
    }
}
