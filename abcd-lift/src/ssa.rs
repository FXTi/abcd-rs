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
//!   instructions (`design/ir.md` §1–§3, `design/decisions.md` ADR-04). One
//!   shared `Const::Undefined` for vregs, one shared `Const::Hole` for
//!   the accumulator (vendor: `CALL_PUSH_UNDEFINED(numVregs)` +
//!   `state->acc = JSTaggedValue::Hole()` at frame creation —
//!   interpreter-inl.cpp:285-291/:731-732/:1471-1472, :739/:1482;
//!   interpreter_assembly.cpp:3653-3657, :3695).

use std::collections::{HashMap, HashSet};

use abcd_ir::{
    BlockId, ConstId, Edge, FuncId, InstId, LocalScope, Module, Op, Ty, Value, ValueDef, ValueId,
};

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
    /// First `BlockId` index owned by the current function (`0` in standalone tests).
    block_base: usize,
    /// Per-block definition maps.
    defs: HashMap<BlockId, BlockDefs>,
    /// Dense per-block sealed flags indexed by `block.index() - block_base` (`R3-A4`).
    sealed: Vec<bool>,
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
    /// Iterative path-compressed union-find map (`trivial_phi -> replacement`)
    /// for Braun et al. (*CC* 2013) Algorithm 3 trivial-phi elimination.
    alias: HashMap<ValueId, ValueId>,
    /// Result `ValueId` -> defining `InstId` for every `Op::Phi` created in
    /// this function.
    phi_insts: HashMap<ValueId, InstId>,
    /// Reverse phi-use adjacency (`operand_phi -> consumer_phis` in deterministic
    /// registration order) driving iterative user-cascade collapse.
    phi_users: HashMap<ValueId, Vec<ValueId>>,
    /// Set of `InstId`s belonging to collapsed trivial `Op::Phi` instructions.
    removed_phis: HashSet<InstId>,
}

impl SsaBuilder {
    /// A fresh builder pre-sized for `num_blocks` starting at `block_base`.
    pub fn with_blocks(
        undefined_const: ConstId,
        hole_const: ConstId,
        block_base: usize,
        num_blocks: usize,
    ) -> Self {
        Self {
            block_base,
            defs: HashMap::with_capacity(num_blocks),
            sealed: vec![false; num_blocks],
            incomplete_phis: HashMap::new(),
            frame_initial_undefined: None,
            frame_initial_hole: None,
            frame_init_consts: Vec::new(),
            undefined_const,
            hole_const,
            alias: HashMap::new(),
            phi_insts: HashMap::new(),
            phi_users: HashMap::new(),
            removed_phis: HashSet::new(),
        }
    }

    /// A fresh builder (`block_base = 0`, dynamically grown in unit tests).
    #[cfg(test)]
    pub fn new(undefined_const: ConstId, hole_const: ConstId) -> Self {
        Self::with_blocks(undefined_const, hole_const, 0, 0)
    }

    /// Resolve `v` through the trivial-phi union-find forest with iterative
    /// two-pass path compression (zero recursion, `O(1)` stack).
    #[inline]
    pub fn resolve_alias(&mut self, mut v: ValueId) -> ValueId {
        if self.alias.is_empty() {
            return v;
        }
        let start = v;
        while let Some(&next) = self.alias.get(&v) {
            if next == v {
                break;
            }
            v = next;
        }
        let root = v;
        let mut cur = start;
        while let Some(&next) = self.alias.get(&cur) {
            if next == root || next == cur {
                break;
            }
            self.alias.insert(cur, root);
            cur = next;
        }
        root
    }

    /// Record a definition: `loc` is defined as `val` in `block`.
    pub fn write_variable(&mut self, loc: RegOrAcc, block: BlockId, val: ValueId) {
        let canonical = self.resolve_alias(val);
        self.defs.entry(block).or_default().insert(loc, canonical);
    }

    /// Read a variable in `block`. If not locally defined, iteratively
    /// searches predecessors on an explicit heap stack and inserts phi
    /// nodes as needed.
    pub fn read_variable(&mut self, loc: RegOrAcc, block: BlockId, module: &mut Module) -> ValueId {
        if let Some(val) = self.defs.get(&block).and_then(|m| m.get(&loc)).copied() {
            let resolved = self.resolve_alias(val);
            if resolved != val {
                self.defs.entry(block).or_default().insert(loc, resolved);
            }
            return resolved;
        }
        let val = self.run_ssa_stack(vec![SsaFrame::EnterRead { loc, block }], module);
        self.resolve_alias(val)
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
                            let canonical = self.resolve_alias(val);
                            if canonical != val {
                                self.defs.entry(cur).or_default().insert(loc, canonical);
                            }
                            break Some(canonical);
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
                            let canonical = self.resolve_alias(val);
                            entries.push((edge, canonical));
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
                    for (_, op_val) in &mut entries {
                        let resolved = self.resolve_alias(*op_val);
                        *op_val = resolved;
                        if resolved != phi_val && self.phi_insts.contains_key(&resolved) {
                            let users = self.phi_users.entry(resolved).or_default();
                            if !users.contains(&phi_val) {
                                users.push(phi_val);
                            }
                        }
                    }
                    module.insts[phi_inst.index()].op = Op::Phi { entries };
                    returned = Some(self.try_remove_trivial_phi(phi_val, module));
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
        let rel = block
            .index()
            .checked_sub(self.block_base)
            .expect("sealed block precedes function block_base");
        if rel >= self.sealed.len() {
            self.sealed.resize(rel + 1, false);
        }
        self.sealed[rel] = true;
        if let Some(incomplete) = self.incomplete_phis.remove(&block) {
            for (loc, phi_val) in incomplete {
                self.add_phi_operands(loc, block, phi_val, module);
            }
        }
    }

    /// Whether the block is sealed.
    #[inline]
    pub fn is_sealed(&self, block: BlockId) -> bool {
        block
            .index()
            .checked_sub(self.block_base)
            .and_then(|rel| self.sealed.get(rel))
            .copied()
            .unwrap_or(false)
    }

    /// Emit an empty phi node in `block`, register it in `phi_insts`, and
    /// return its result value.
    fn emit_empty_phi(&mut self, block: BlockId, module: &mut Module) -> ValueId {
        let (inst_id, result) = emit_inst(
            module,
            block,
            Op::Phi {
                entries: Vec::new(),
            },
            None,
        );
        let phi_val = result.expect("phi has a result");
        self.phi_insts.insert(phi_val, inst_id);
        phi_val
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

    /// Iteratively collapse `phi_val` and any cascading consumer `Op::Phi`s
    /// that become trivial (Braun et al. *CC* 2013 Algorithm 3, iterative
    /// union-find + phi-user worklist), removing dead `Op::Phi` instructions
    /// from `block.insts` immediately.
    fn try_remove_trivial_phi(&mut self, phi_val: ValueId, module: &mut Module) -> ValueId {
        self.collapse_trivial_phis_from(vec![phi_val], module);
        self.resolve_alias(phi_val)
    }

    /// Run iterative worklist trivial-phi elimination starting from `seeds`
    /// (`O(1)` call stack, zero `HashMap`/`HashSet` iteration for `N20`).
    fn collapse_trivial_phis_from(&mut self, seeds: Vec<ValueId>, module: &mut Module) {
        let mut worklist: Vec<ValueId> = Vec::with_capacity(seeds.len());
        let mut queued: HashSet<ValueId> = HashSet::with_capacity(seeds.len());
        for s in seeds {
            if !self.alias.contains_key(&s) && queued.insert(s) {
                worklist.push(s);
            }
        }

        while let Some(p_val) = worklist.pop() {
            queued.remove(&p_val);
            if self.alias.contains_key(&p_val) {
                continue;
            }
            let Some(&p_inst) = self.phi_insts.get(&p_val) else {
                continue;
            };
            if self.removed_phis.contains(&p_inst) {
                continue;
            }

            let mut entries = match &module.insts[p_inst.index()].op {
                Op::Phi { entries } if !entries.is_empty() => entries.clone(),
                // Incomplete phi in an unsealed block (or non-phi): never collapse yet.
                _ => continue,
            };

            let mut same: Option<ValueId> = None;
            let mut non_trivial = false;
            for (_, op_val) in &mut entries {
                let resolved = self.resolve_alias(*op_val);
                *op_val = resolved;
                if resolved == p_val {
                    continue; // self-reference
                }
                match same {
                    None => same = Some(resolved),
                    Some(s) if s == resolved => {}
                    Some(_) => {
                        non_trivial = true;
                    }
                }
            }

            if non_trivial {
                // Keep live non-trivial phi's operands canonicalized and ensure
                // `p_val` is subscribed to any phi operand it now references
                // after intermediate forwarding.
                for &(_, op_val) in &entries {
                    if op_val != p_val && self.phi_insts.contains_key(&op_val) {
                        let users = self.phi_users.entry(op_val).or_default();
                        if !users.contains(&p_val) {
                            users.push(p_val);
                        }
                    }
                }
                module.insts[p_inst.index()].op = Op::Phi { entries };
                continue;
            }

            // If `same` is `None`, all incoming operands self-reference `p_val`
            // (an unreachable sealed cycle prior to `sweep_dead_blocks`).
            let Some(replacement) = same else {
                module.insts[p_inst.index()].op = Op::Phi { entries };
                continue;
            };
            let replacement = self.resolve_alias(replacement);
            if replacement == p_val {
                continue;
            }

            self.alias.insert(p_val, replacement);
            self.removed_phis.insert(p_inst);
            let owner_bb = module.insts[p_inst.index()].block;
            module.blocks[owner_bb.index()]
                .insts
                .retain(|&iid| iid != p_inst);

            if let Some(users) = self.phi_users.remove(&p_val) {
                let rep_is_phi = self.phi_insts.contains_key(&replacement)
                    && !self.alias.contains_key(&replacement);
                for u_phi in users {
                    if u_phi == p_val || self.alias.contains_key(&u_phi) {
                        continue;
                    }
                    if rep_is_phi && u_phi != replacement {
                        let rep_users = self.phi_users.entry(replacement).or_default();
                        if !rep_users.contains(&u_phi) {
                            rep_users.push(u_phi);
                        }
                    }
                    if queued.insert(u_phi) {
                        worklist.push(u_phi);
                    }
                }
            }
        }
    }

    /// Re-run the iterative trivial-phi cascade over all surviving `Op::Phi`s
    /// in `func_id` (catching phis reduced to trivial by dead-block sweeping),
    /// prune collapsed `Op::Phi` instructions from `block.insts`, and rewrite
    /// every SSA use across instructions (`Op::for_each_operand_mut`), catch
    /// handlers, and `func.debug`.
    pub fn finalize_function(&mut self, module: &mut Module, func_id: FuncId) {
        let blocks = module.functions[func_id.index()].blocks.clone();
        let mut seeds: Vec<ValueId> = Vec::new();

        for &bb in &blocks {
            let inst_ids = module.blocks[bb.index()].insts.clone();
            for iid in inst_ids {
                if self.removed_phis.contains(&iid) {
                    continue;
                }
                let Some(phi_val) = module.insts[iid.index()].result else {
                    continue;
                };
                if !module.insts[iid.index()].op.is_phi() {
                    break; // Phis form a contiguous prefix of `block.insts`.
                }
                self.phi_insts.entry(phi_val).or_insert(iid);
                if let Op::Phi { entries } = &mut module.insts[iid.index()].op {
                    let mut operand_phis: Vec<ValueId> = Vec::new();
                    for (_, v) in entries.iter_mut() {
                        let resolved = self.resolve_alias(*v);
                        *v = resolved;
                        if resolved != phi_val && self.phi_insts.contains_key(&resolved) {
                            operand_phis.push(resolved);
                        }
                    }
                    for op_phi in operand_phis {
                        let users = self.phi_users.entry(op_phi).or_default();
                        if !users.contains(&phi_val) {
                            users.push(phi_val);
                        }
                    }
                }
                seeds.push(phi_val);
            }
        }

        if !seeds.is_empty() {
            self.collapse_trivial_phis_from(seeds, module);
        }

        if self.alias.is_empty() && self.removed_phis.is_empty() {
            return;
        }

        let mut surviving_insts: Vec<InstId> = Vec::new();
        let need_debug_fix = module.functions[func_id.index()].debug.is_some();

        for &bb in &blocks {
            if !self.removed_phis.is_empty() {
                module.blocks[bb.index()]
                    .insts
                    .retain(|iid| !self.removed_phis.contains(iid));
            }
            let inst_ids = module.blocks[bb.index()].insts.clone();
            for iid in inst_ids {
                if need_debug_fix {
                    surviving_insts.push(iid);
                }
                if !self.alias.is_empty() {
                    module.insts[iid.index()]
                        .op
                        .for_each_operand_mut(|v| *v = self.resolve_alias(*v));
                }
            }
        }

        if !self.alias.is_empty() {
            let num_regions = module.functions[func_id.index()].try_regions.len();
            for ri in 0..num_regions {
                let num_catches = module.functions[func_id.index()].try_regions[ri]
                    .catches
                    .len();
                for ci in 0..num_catches {
                    let old_exc =
                        module.functions[func_id.index()].try_regions[ri].catches[ci].exception;
                    let new_exc = self.resolve_alias(old_exc);
                    module.functions[func_id.index()].try_regions[ri].catches[ci].exception =
                        new_exc;
                }
            }
        }

        if let Some(dbg) = &mut module.functions[func_id.index()].debug
            && !self.removed_phis.is_empty()
        {
            dbg.line_table
                .retain(|e| !self.removed_phis.contains(&e.inst));
            dbg.column_table
                .retain(|e| !self.removed_phis.contains(&e.inst));
            for ln in &mut dbg.local_names {
                if let Some(scope) = ln.scope {
                    let start = surviving_insts
                        .iter()
                        .copied()
                        .find(|iid| iid.index() >= scope.start.index());
                    let end = surviving_insts
                        .iter()
                        .rev()
                        .copied()
                        .find(|iid| iid.index() <= scope.end.index());
                    ln.scope = match (start, end) {
                        (Some(s), Some(e)) if s.index() <= e.index() => {
                            Some(LocalScope { start: s, end: e })
                        }
                        _ => None,
                    };
                }
            }
        }
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

                // Trivial phis collapse all 2,000 diamonds back to `v0` and
                // leave zero dead `Op::Phi` instructions for `Reg(0)`.
                assert_eq!(ssa.read_variable(RegOrAcc::Reg(0), prev, &mut module), v0);
                let live_phis_after_r0: usize = module
                    .blocks
                    .iter()
                    .flat_map(|b| &b.insts)
                    .filter(|&&iid| module.insts[iid.index()].op.is_phi())
                    .count();
                assert_eq!(
                    live_phis_after_r0, 0,
                    "all 2,000 trivial diamond phis for Reg(0) must be removed from block.insts"
                );
                // Non-trivial phi at diamond 0 survives and propagates cleanly,
                // while all 1,999 downstream diamonds collapse to `joined`.
                let joined = ssa.read_variable(RegOrAcc::Reg(1), prev, &mut module);
                assert_ne!(joined, v0);
                assert_ne!(joined, v1);
                let live_phis_after_r1: usize = module
                    .blocks
                    .iter()
                    .flat_map(|b| &b.insts)
                    .filter(|&&iid| module.insts[iid.index()].op.is_phi())
                    .count();
                assert_eq!(
                    live_phis_after_r1, 1,
                    "only the single non-trivial join phi at diamond 0 survives across 2,000 diamonds"
                );
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

    #[test]
    fn cascading_cyclic_trivial_phi_web_rewrites_uses_and_debug() {
        use abcd_ir::{
            BinOp, ClassData, ClassId, ColumnEntry, DebugData, FunctionData, FunctionKind,
            LineEntry, LocalName,
        };

        let (mut module, mut ssa) = fresh_builder();
        let sym = module.sym.intern("test");
        let mut cls = ClassData::new(sym, sym);
        let func_id = FuncId::new(0);
        cls.methods.push(func_id);
        module.classes.push(cls);

        // CFG with mutual cycle `h1 <-> h2` entered from `entry`, joining at `exit`:
        // - `entry` defines `Reg(0) = param0`
        // - `h1` (unsealed first) creates incomplete `P1`, emits `add(P1, P1)`
        // - `h2` (unsealed first) creates incomplete `P2`
        // - `exit` merges `h1` and `h2` (`P3 = phi(P1, P2)`), emits `return P3`
        // When `h1`, `h2`, and `exit` seal, `{P1, P2, P3}` form a mutually
        // dependent trivial-phi web that must cascade completely to `param0`!
        let entry = push_block(&mut module);
        let h1 = push_block(&mut module);
        let h2 = push_block(&mut module);
        let exit = push_block(&mut module);

        add_normal_edge(&mut module, entry, h1);
        add_normal_edge(&mut module, h2, h1);
        add_normal_edge(&mut module, h1, h2);
        add_normal_edge(&mut module, h1, exit);
        add_normal_edge(&mut module, h2, exit);

        let param0 = ValueId::new(module.values.len() as u32);
        module.values.push(Value {
            def: ValueDef::Param(0),
            ty: Ty::Any,
        });
        let cond_cid = module.consts.intern(Const::Bool(true));

        let mut fd = FunctionData::new(ClassId::new(0), sym, FunctionKind::Function);
        fd.params.push(param0);
        fd.blocks = vec![entry, h1, h2, exit];
        module.functions.push(fd);

        // Translate `entry` and seal it.
        ssa.write_variable(RegOrAcc::Reg(0), entry, param0);
        emit_inst(&mut module, entry, Op::Branch { dest: h1 }, None);
        ssa.seal_block(entry, &mut module);

        // Read `Reg(0)` in unsealed `h1` -> incomplete `p1`, used by `BinaryOp` BEFORE sealing!
        let p1 = ssa.read_variable(RegOrAcc::Reg(0), h1, &mut module);
        let p1_iid = match module.values[p1.index()].def {
            ValueDef::Inst(iid) => iid,
            _ => panic!("expected incomplete phi inst"),
        };
        let (add_iid, add_res) = emit_inst(
            &mut module,
            h1,
            Op::BinaryOp {
                op: BinOp::Add,
                left: p1,
                right: p1,
            },
            None,
        );
        let (_, cond1) = emit_inst(&mut module, h1, Op::LoadConst(cond_cid), None);
        emit_inst(
            &mut module,
            h1,
            Op::CondBranch {
                cond: cond1.unwrap(),
                true_dest: h2,
                false_dest: exit,
            },
            None,
        );

        // Read `Reg(0)` in unsealed `h2` -> incomplete `p2`.
        let p2 = ssa.read_variable(RegOrAcc::Reg(0), h2, &mut module);
        let (_, cond2) = emit_inst(&mut module, h2, Op::LoadConst(cond_cid), None);
        emit_inst(
            &mut module,
            h2,
            Op::CondBranch {
                cond: cond2.unwrap(),
                true_dest: h1,
                false_dest: exit,
            },
            None,
        );

        // Seal `exit` while `h1`/`h2` are still unsealed so `p3 = phi(p1, p2)` is non-trivial initially!
        ssa.seal_block(exit, &mut module);
        let p3 = ssa.read_variable(RegOrAcc::Reg(0), exit, &mut module);
        assert_ne!(
            p3, param0,
            "p3 initially joins two distinct incomplete phis"
        );
        let (ret_iid, _) = emit_inst(
            &mut module,
            exit,
            Op::Return {
                value: Some(add_res.unwrap()),
            },
            None,
        );
        let (use_p3_iid, _) = emit_inst(&mut module, h2, Op::Mov { src: p2 }, None);
        // Move `Mov` before `CondBranch` in `h2` so terminator stays last.
        let h2_len = module.blocks[h2.index()].insts.len();
        module.blocks[h2.index()].insts.swap(h2_len - 2, h2_len - 1);
        let _ = use_p3_iid;

        // Also attach a `DebugData` referencing `p1_iid` to test debug cleanup.
        module.functions[func_id.index()].debug = Some(DebugData {
            source_file: Some(sym),
            source_code: None,
            line_table: vec![
                LineEntry {
                    inst: p1_iid,
                    line: 1,
                },
                LineEntry {
                    inst: add_iid,
                    line: 2,
                },
            ],
            column_table: vec![ColumnEntry {
                inst: p1_iid,
                column: 5,
            }],
            local_names: vec![LocalName {
                name: sym,
                ty: None,
                scope: Some(LocalScope {
                    start: p1_iid,
                    end: ret_iid,
                }),
            }],
            param_names: Vec::new(),
            scope_names: None,
        });

        // Now seal `h1` and `h2`: `p1`, `p2`, AND downstream consumer `p3` must
        // all cascade to `param0`!
        ssa.seal_block(h1, &mut module);
        ssa.seal_block(h2, &mut module);
        assert_eq!(ssa.resolve_alias(p1), param0);
        assert_eq!(ssa.resolve_alias(p2), param0);
        assert_eq!(
            ssa.resolve_alias(p3),
            param0,
            "consumer phi p3 collapsed via user-cascade"
        );

        ssa.finalize_function(&mut module, func_id);

        // Zero `Op::Phi` instructions remain in any block!
        for &bb in &[entry, h1, h2, exit] {
            assert!(
                module.blocks[bb.index()]
                    .insts
                    .iter()
                    .all(|&iid| !module.insts[iid.index()].op.is_phi()),
                "all trivial phis must be removed from block {bb:?}"
            );
        }
        // Pre-seal `BinaryOp` operands were rewritten from `p1` to `param0`.
        assert!(matches!(
            module.insts[add_iid.index()].op,
            Op::BinaryOp {
                left,
                right,
                ..
            } if left == param0 && right == param0
        ));
        // Debug entries referencing `p1_iid` were pruned/adjusted cleanly.
        let dbg = module.functions[func_id.index()].debug.as_ref().unwrap();
        assert_eq!(dbg.line_table.len(), 1);
        assert_eq!(dbg.line_table[0].inst, add_iid);
        assert!(dbg.column_table.is_empty());
        assert_eq!(
            dbg.local_names[0].scope,
            Some(LocalScope {
                start: add_iid,
                end: ret_iid,
            })
        );

        let report = abcd_ir::verify_module(&module);
        assert!(
            report.is_ok(),
            "verifier errors after cascading trivial-phi cleanup: {:?}",
            report.errors
        );
    }
}
