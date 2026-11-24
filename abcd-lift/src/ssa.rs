//! Braun SSA construction: register/accumulator → SSA values (ported
//! from v0.1 `abcd-ir/src/lift/ssa.rs` — "Simple and Efficient
//! Construction of SSA Form", Braun et al. 2013).
//!
//! The v0.2 adaptations:
//!
//! - phi entries key on [`Edge`] (kind-qualified), not bare blocks —
//!   exception edges are first-class (T5);
//! - frame-initial values are CONSTANTS
//!   ([`ValueDef::Const`](abcd_ir::ValueDef)) — no seeding
//!   instructions; the v0.1 entry-block `LiteralUndefined`/`LiteralHole`
//!   materialization stays a v0.1 detail (design/ir-v0.2.md §5.1). One
//!   shared `Const::Undefined` for vregs, one shared `Const::Hole` for
//!   the accumulator (vendor: `CALL_PUSH_UNDEFINED(numVregs)` +
//!   `state->acc = JSTaggedValue::Hole()` at frame creation —
//!   interpreter-inl.cpp:285-291/:731-732/:1471-1472, :739/:1482;
//!   interpreter_assembly.cpp:3653-3657, :3695).

use std::collections::{HashMap, HashSet};

use abcd_ir::{BlockId, ConstId, Edge, InstId, Module, Op, Ty, Value, ValueDef, ValueId};

use crate::emit_inst;

/// Identifies a virtual location: either the accumulator or a register.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RegOrAcc {
    /// The accumulator.
    Acc,
    /// A virtual register.
    Reg(u16),
}

/// Per-block SSA state: maps each virtual location to its current SSA
/// value.
type BlockDefs = HashMap<RegOrAcc, ValueId>;

/// Explicit stack frame for iterative Braun SSA resolution.
enum SsaFrame {
    /// Begin reading `loc` in `block` (walks sealed single-predecessor
    /// chains iteratively in O(1) stack space).
    EnterRead { loc: RegOrAcc, block: BlockId },
    /// After resolving the value at the head of a single-predecessor chain
    /// `[b_0, b_1, ..., b_k]`, record `write_variable(loc, b_i, val)` in
    /// reverse order (`b_k` down to `b_0`) to match recursive unwinding.
    FinishChain { loc: RegOrAcc, chain: Vec<BlockId> },
    /// Iteratively populate `Op::Phi` operands across `preds` for `phi_val`.
    FillPhi {
        loc: RegOrAcc,
        phi_val: ValueId,
        preds: Vec<Edge>,
        next_idx: usize,
        entries: Vec<(Edge, ValueId)>,
    },
}

/// SSA construction context using the Braun algorithm.
pub struct SsaBuilder {
    /// Per-block definition maps.
    defs: HashMap<BlockId, BlockDefs>,
    /// Tracks which blocks are "sealed" (all predecessors known).
    sealed: HashMap<BlockId, bool>,
    /// Incomplete phis: block → [(location, phi_value)] for unsealed
    /// blocks.
    incomplete_phis: HashMap<BlockId, Vec<(RegOrAcc, ValueId)>>,
    /// Lazily materialized frame-initial constants, one shared value per
    /// location kind (minimal liveness perturbation; vendor citations in
    /// the module docs). The underlying pool constants come from the
    /// lifter's deduplicated scalar pool, so frame-initial values share
    /// their `ConstId` with literal loads of the same constant.
    frame_initial_undefined: Option<ValueId>,
    frame_initial_hole: Option<ValueId>,
    /// Frame-initial constant `ValueId`s materialized for this function, in
    /// creation order (#30).
    pub frame_init_consts: Vec<ValueId>,
    undefined_const: ConstId,
    hole_const: ConstId,
}

impl SsaBuilder {
    /// A fresh builder; `undefined_const`/`hole_const` are the pooled
    /// frame-initial constants (deduplicated module-wide).
    pub fn new(undefined_const: ConstId, hole_const: ConstId) -> Self {
        Self {
            defs: HashMap::new(),
            sealed: HashMap::new(),
            incomplete_phis: HashMap::new(),
            frame_initial_undefined: None,
            frame_initial_hole: None,
            frame_init_consts: Vec::new(),
            undefined_const,
            hole_const,
        }
    }

    /// Record a definition: `loc` is defined as `val` in `block`.
    pub fn write_variable(&mut self, loc: RegOrAcc, block: BlockId, val: ValueId) {
        self.defs.entry(block).or_default().insert(loc, val);
    }

    /// Read a variable in `block`. If not locally defined, iteratively
    /// searches predecessors on an explicit heap stack and inserts phi
    /// nodes as needed.
    pub fn read_variable(&mut self, loc: RegOrAcc, block: BlockId, module: &mut Module) -> ValueId {
        if let Some(val) = self.defs.get(&block).and_then(|m| m.get(&loc)).copied() {
            return val;
        }
        self.run_ssa_stack(vec![SsaFrame::EnterRead { loc, block }], module)
    }

    /// Drive Braun SSA resolution and phi-operand filling without native
    /// call-stack recursion.
    fn run_ssa_stack(&mut self, mut stack: Vec<SsaFrame>, module: &mut Module) -> ValueId {
        let mut returned: Option<ValueId> = None;

        'frames: while let Some(frame) = stack.pop() {
            match frame {
                SsaFrame::EnterRead { loc, block } => {
                    debug_assert!(returned.is_none());
                    let mut cur = block;
                    let mut chain: Vec<BlockId> = Vec::new();
                    let mut seen_large: Option<HashSet<BlockId>> = None;

                    let resolved = loop {
                        if let Some(val) = self.defs.get(&cur).and_then(|m| m.get(&loc)).copied() {
                            break Some(val);
                        }

                        let in_chain = if let Some(set) = &seen_large {
                            set.contains(&cur)
                        } else {
                            chain.contains(&cur)
                        };
                        if in_chain {
                            // Unreachable sealed single-predecessor cycle: break
                            // the cycle with a self-referential 1-entry phi on `cur`.
                            let phi_val = self.emit_empty_phi(cur, module);
                            let pred_edge = module.blocks[cur.index()].preds[0];
                            let phi_inst = match module.values[phi_val.index()].def {
                                ValueDef::Inst(inst) => inst,
                                _ => unreachable!("phi_val must be an instruction result"),
                            };
                            module.insts[phi_inst.index()].op = Op::Phi {
                                entries: vec![(pred_edge, phi_val)],
                            };
                            self.write_variable(loc, cur, phi_val);
                            break Some(phi_val);
                        }

                        let preds_len = module.blocks[cur.index()].preds.len();
                        if preds_len == 0 {
                            // Predecessor edges are fully built before SSA
                            // construction starts, so a zero-predecessor block
                            // (entry, or unreachable island head) resolves to
                            // the Ark frame-initial constant instead of an
                            // invalid zero-entry phi.
                            let val = self.frame_initial(loc, module);
                            self.write_variable(loc, cur, val);
                            break Some(val);
                        } else if !self.is_sealed(cur) {
                            let phi_val = self.emit_empty_phi(cur, module);
                            self.incomplete_phis
                                .entry(cur)
                                .or_default()
                                .push((loc, phi_val));
                            self.write_variable(loc, cur, phi_val);
                            break Some(phi_val);
                        } else if preds_len == 1 {
                            let next = module.blocks[cur.index()].preds[0].from;
                            if let Some(set) = &mut seen_large {
                                set.insert(cur);
                            } else if chain.len() == 64 {
                                let mut set: HashSet<BlockId> = chain.iter().copied().collect();
                                set.insert(cur);
                                seen_large = Some(set);
                            }
                            chain.push(cur);
                            cur = next;
                        } else {
                            // Multiple predecessors on a sealed block: insert an
                            // empty phi and write before recursing to break cycles.
                            let phi_val = self.emit_empty_phi(cur, module);
                            self.write_variable(loc, cur, phi_val);
                            chain.push(cur);
                            let preds = module.blocks[cur.index()].preds.clone();
                            let cap = preds.len();
                            stack.push(SsaFrame::FinishChain {
                                loc,
                                chain: std::mem::take(&mut chain),
                            });
                            stack.push(SsaFrame::FillPhi {
                                loc,
                                phi_val,
                                preds,
                                next_idx: 0,
                                entries: Vec::with_capacity(cap),
                            });
                            break None;
                        }
                    };

                    if let Some(val) = resolved {
                        for &b in chain.iter().rev() {
                            self.write_variable(loc, b, val);
                        }
                        returned = Some(val);
                    }
                }
                SsaFrame::FinishChain { loc, chain } => {
                    let Some(val) = returned else {
                        unreachable!("FinishChain resumed without child return value");
                    };
                    for &b in chain.iter().rev() {
                        self.write_variable(loc, b, val);
                    }
                }
                SsaFrame::FillPhi {
                    loc,
                    phi_val,
                    preds,
                    mut next_idx,
                    mut entries,
                } => {
                    if let Some(val) = returned.take() {
                        entries.push((preds[next_idx - 1], val));
                    }

                    while next_idx < preds.len() {
                        let edge = preds[next_idx];
                        next_idx += 1;
                        if let Some(val) =
                            self.defs.get(&edge.from).and_then(|m| m.get(&loc)).copied()
                        {
                            entries.push((edge, val));
                        } else {
                            let child_block = edge.from;
                            stack.push(SsaFrame::FillPhi {
                                loc,
                                phi_val,
                                preds,
                                next_idx,
                                entries,
                            });
                            stack.push(SsaFrame::EnterRead {
                                loc,
                                block: child_block,
                            });
                            continue 'frames;
                        }
                    }

                    let phi_inst = match module.values[phi_val.index()].def {
                        ValueDef::Inst(inst) => inst,
                        _ => unreachable!("phi_val must be an instruction result"),
                    };
                    module.insts[phi_inst.index()].op = Op::Phi { entries };
                    returned = Some(self.try_remove_trivial_phi(phi_val, phi_inst, module));
                }
            }
        }

        match returned {
            Some(val) => val,
            None => unreachable!("SSA stack finished without producing a ValueId"),
        }
    }

    /// The frame-initial value for a location with no reaching
    /// definition: one shared `Const::Undefined` for vregs, one shared
    /// `Const::Hole` for the accumulator. v0.2 represents these as
    /// `ValueDef::Const` — constants dominate everything and need no
    /// materializing instruction.
    fn frame_initial(&mut self, loc: RegOrAcc, module: &mut Module) -> ValueId {
        let cached = match loc {
            RegOrAcc::Acc => self.frame_initial_hole,
            RegOrAcc::Reg(_) => self.frame_initial_undefined,
        };
        if let Some(val) = cached {
            return val;
        }

        let const_id = match loc {
            RegOrAcc::Acc => self.hole_const,
            RegOrAcc::Reg(_) => self.undefined_const,
        };
        let val = ValueId::new(module.values.len() as u32);
        module.values.push(Value {
            def: ValueDef::Const(const_id),
            ty: Ty::Any,
        });

        match loc {
            RegOrAcc::Acc => self.frame_initial_hole = Some(val),
            RegOrAcc::Reg(_) => self.frame_initial_undefined = Some(val),
        }
        self.frame_init_consts.push(val);
        val
    }

    /// Mark a block as sealed (all predecessors are known). Completes
    /// any incomplete phis.
    pub fn seal_block(&mut self, block: BlockId, module: &mut Module) {
        self.sealed.insert(block, true);
        if let Some(incomplete) = self.incomplete_phis.remove(&block) {
            for (loc, phi_val) in incomplete {
                self.add_phi_operands(loc, block, phi_val, module);
            }
        }
    }

    /// Whether the block is sealed.
    pub fn is_sealed(&self, block: BlockId) -> bool {
        self.sealed.get(&block).copied().unwrap_or(false)
    }

    /// Emit an empty phi node in `block` and return its result value.
    fn emit_empty_phi(&self, block: BlockId, module: &mut Module) -> ValueId {
        let (_inst_id, result) = emit_inst(
            module,
            block,
            Op::Phi {
                entries: Vec::new(),
            },
            None,
        );
        result.expect("phi has a result")
    }

    /// Fill phi operands by reading the variable from each predecessor
    /// edge on the explicit SSA stack.
    fn add_phi_operands(
        &mut self,
        loc: RegOrAcc,
        block: BlockId,
        phi_val: ValueId,
        module: &mut Module,
    ) -> ValueId {
        let preds = module.blocks[block.index()].preds.clone();
        let cap = preds.len();
        self.run_ssa_stack(
            vec![SsaFrame::FillPhi {
                loc,
                phi_val,
                preds,
                next_idx: 0,
                entries: Vec::with_capacity(cap),
            }],
            module,
        )
    }

    /// If a phi is trivial (all operands are the same value or the phi
    /// itself), remove it and replace uses with the single value.
    fn try_remove_trivial_phi(
        &mut self,
        phi_val: ValueId,
        phi_inst: InstId,
        module: &mut Module,
    ) -> ValueId {
        let entries = match &module.insts[phi_inst.index()].op {
            Op::Phi { entries } => entries.clone(),
            _ => return phi_val,
        };

        let mut same: Option<ValueId> = None;
        for (_, val) in &entries {
            if *val == phi_val {
                continue; // self-reference
            }
            if let Some(s) = same {
                if *val == s {
                    continue; // same as existing
                }
                return phi_val; // non-trivial: at least two distinct values
            }
            same = Some(*val);
        }

        // If same is None, all operands are self-references (unreachable
        // in practice).
        let replacement = match same {
            Some(v) => v,
            None => return phi_val,
        };

        // Replace all uses of phi_val with replacement in the definition
        // maps.
        for block_defs in self.defs.values_mut() {
            for val in block_defs.values_mut() {
                if *val == phi_val {
                    *val = replacement;
                }
            }
        }

        // Keep the phi in the block during SSA construction. Earlier
        // instructions may already refer to its value; removing it here
        // without a function-wide use rewrite would create an undefined
        // SSA value. (CopyProp performs that rewrite before removing
        // dead phis — a pass-layer concern.)

        replacement
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use abcd_ir::{Block, Const, EdgeKind};

    fn fresh_builder() -> (Module, SsaBuilder) {
        let mut module = Module::new();
        let undef = module.consts.push(Const::Undefined);
        let hole = module.consts.push(Const::Hole);
        let ssa = SsaBuilder::new(undef, hole);
        (module, ssa)
    }

    fn push_block(module: &mut Module) -> BlockId {
        let id = BlockId::new(module.blocks.len() as u32);
        module.blocks.push(Block::default());
        id
    }

    fn add_normal_edge(module: &mut Module, from: BlockId, to: BlockId) {
        module.blocks[to.index()].preds.push(Edge {
            from,
            kind: EdgeKind::Normal,
        });
    }

    #[test]
    fn deep_linear_chain_uses_constant_stack() {
        let handle = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let (mut module, mut ssa) = fresh_builder();
                let n = 5_000usize;
                let mut blocks = Vec::with_capacity(n);
                for i in 0..n {
                    let bb = push_block(&mut module);
                    if i > 0 {
                        add_normal_edge(&mut module, blocks[i - 1], bb);
                    }
                    blocks.push(bb);
                }
                let param = ValueId::new(module.values.len() as u32);
                module.values.push(Value {
                    def: ValueDef::Param(0),
                    ty: Ty::Any,
                });
                ssa.write_variable(RegOrAcc::Reg(0), blocks[0], param);
                for &bb in &blocks {
                    ssa.seal_block(bb, &mut module);
                }

                let tail = blocks[n - 1];
                assert_eq!(
                    ssa.read_variable(RegOrAcc::Reg(0), tail, &mut module),
                    param
                );
                let uninit = ssa.read_variable(RegOrAcc::Reg(1), tail, &mut module);
                assert!(matches!(
                    module.values[uninit.index()].def,
                    ValueDef::Const(_)
                ));
            })
            .unwrap();
        handle.join().unwrap();
    }

    #[test]
    fn deep_diamond_chain_uses_constant_stack() {
        let handle = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let (mut module, mut ssa) = fresh_builder();
                let diamonds = 2_000usize;
                let entry = push_block(&mut module);
                let v0 = ValueId::new(module.values.len() as u32);
                module.values.push(Value {
                    def: ValueDef::Param(0),
                    ty: Ty::Any,
                });
                let v1 = ValueId::new(module.values.len() as u32);
                module.values.push(Value {
                    def: ValueDef::Param(1),
                    ty: Ty::Any,
                });
                // Reg(0) stays constant across all diamonds (trivial-phi collapse);
                // Reg(1) gets redefined on one arm of the first diamond (non-trivial phi chain).
                ssa.write_variable(RegOrAcc::Reg(0), entry, v0);
                ssa.write_variable(RegOrAcc::Reg(1), entry, v0);
                ssa.seal_block(entry, &mut module);

                let mut prev = entry;
                for i in 0..diamonds {
                    let left = push_block(&mut module);
                    let right = push_block(&mut module);
                    let merge = push_block(&mut module);
                    add_normal_edge(&mut module, prev, left);
                    add_normal_edge(&mut module, prev, right);
                    add_normal_edge(&mut module, left, merge);
                    add_normal_edge(&mut module, right, merge);
                    if i == 0 {
                        ssa.write_variable(RegOrAcc::Reg(1), right, v1);
                    }
                    ssa.seal_block(left, &mut module);
                    ssa.seal_block(right, &mut module);
                    ssa.seal_block(merge, &mut module);
                    prev = merge;
                }

                // Trivial phis collapse all 2,000 diamonds back to `v0`.
                assert_eq!(ssa.read_variable(RegOrAcc::Reg(0), prev, &mut module), v0);
                // Non-trivial phi at diamond 0 survives and propagates cleanly.
                let joined = ssa.read_variable(RegOrAcc::Reg(1), prev, &mut module);
                assert_ne!(joined, v0);
                assert_ne!(joined, v1);
            })
            .unwrap();
        handle.join().unwrap();
    }

    #[test]
    fn unreachable_single_pred_cycle_terminates() {
        let (mut module, mut ssa) = fresh_builder();
        let entry = push_block(&mut module);
        let b1 = push_block(&mut module);
        let b2 = push_block(&mut module);
        let b3 = push_block(&mut module);
        // Sealed dead cycle b1 <-> b2 feeding b3.
        add_normal_edge(&mut module, b2, b1);
        add_normal_edge(&mut module, b1, b2);
        add_normal_edge(&mut module, b2, b3);
        for bb in [entry, b1, b2, b3] {
            ssa.seal_block(bb, &mut module);
        }

        let val = ssa.read_variable(RegOrAcc::Reg(0), b3, &mut module);
        assert!(matches!(module.values[val.index()].def, ValueDef::Inst(_)));
    }
}
