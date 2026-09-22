//! A generic monotone dataflow framework (block granularity, any
//! successor relation).
//!
//! The client implements [`MonotoneFramework`]: a domain with a meet, a
//! whole-block transfer, and boundary/initial values. The solver is the
//! standard worklist iteration to a fixed point, in RPO for forward
//! problems and reverse-RPO for backward ones, so convergence is fast and
//! — because every structure is iterated in a pinned order — the result
//! is deterministic (heros.md §5 item 4: iteration order is a feature).
//!
//! Termination requires the client's lattice to have finite descending
//! (toward the join) chain height and an honest `meet`; the framework has
//! no widening hook, mirroring heros' discipline (heros.md §7 item 11).

use std::collections::{HashMap, HashSet, VecDeque};

use abcd_ir::{BlockId, FuncId, Module};

/// Analysis direction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    /// Information flows entry → exits; meets happen over predecessors.
    Forward,
    /// Information flows exits → entry; meets happen over successors.
    Backward,
}

/// Solver configuration.
#[derive(Clone, Debug)]
pub struct SolveConfig {
    /// Direction of propagation.
    pub direction: Direction,
}

impl Default for SolveConfig {
    fn default() -> Self {
        Self {
            direction: Direction::Forward,
        }
    }
}

/// A monotone dataflow problem over one function.
///
/// `Domain` is the per-program-point dataflow value (a bitset, a map, a
/// lattice element — the framework is agnostic). `PartialEq` is the
/// change detection; it must be semantic equality (heros.md §1.3's
/// termination caveat applies here too).
pub trait MonotoneFramework {
    /// The per-block dataflow value.
    type Domain: Clone + PartialEq;

    /// The boundary value: at the entry block (forward) or at exit blocks
    /// (backward). Exit blocks are blocks with no successors in the
    /// chosen relation.
    fn boundary(&self) -> Self::Domain;

    /// The initial (identity-of-meet, "top") value for interior blocks.
    /// Sparse-by-default (heros.md §5 item 5): this value is what every
    /// block starts at; it should be the cheapest element to construct.
    fn initial(&self) -> Self::Domain;

    /// Join `other` into `acc` (`acc = acc ⊔ other`).
    fn meet(&self, acc: &mut Self::Domain, other: &Self::Domain);

    /// The transfer over one whole block: given the value at the block's
    /// input edge (forward) or output edge (backward), produce the value
    /// at the opposite edge. Clients iterate the block's instructions
    /// internally (`module.block(block)`), forward in order, backward in
    /// reverse; phis are ordinary leading instructions.
    fn transfer_block(
        &self,
        module: &Module,
        func: FuncId,
        block: BlockId,
        input: &Self::Domain,
    ) -> Self::Domain;
}

/// The result of a [`solve`] run: per-block values on both edges.
#[derive(Clone, Debug)]
pub struct DataflowResult<D> {
    /// Value at each block's input edge (entry block holds the boundary).
    pub block_in: HashMap<BlockId, D>,
    /// Value at each block's output edge.
    pub block_out: HashMap<BlockId, D>,
}

impl<D> DataflowResult<D> {
    /// The input-edge value of `block`, if the solver visited it.
    pub fn in_at(&self, block: BlockId) -> Option<&D> {
        self.block_in.get(&block)
    }

    /// The output-edge value of `block`, if the solver visited it.
    pub fn out_at(&self, block: BlockId) -> Option<&D> {
        self.block_out.get(&block)
    }
}

/// Solve `problem` over `func` to a fixed point.
///
/// `succ` is the successor relation the problem flows over (use
/// [`crate::control::block_succs`] for Normal-only flow or
/// [`crate::control::augmented_succs`] to make exceptional dispatch
/// first-class — the default for value flow, T5). Only blocks reachable
/// from the entry (forward) / from any exit walking backward (backward)
/// participate; unreachable blocks are absent from the result maps
/// (TOP-as-absent, heros.md §5 item 5).
pub fn solve<P: MonotoneFramework>(
    module: &Module,
    func: FuncId,
    succ: &dyn Fn(BlockId) -> Vec<BlockId>,
    config: &SolveConfig,
    problem: &P,
) -> DataflowResult<P::Domain> {
    let Some(f) = module.func(func) else {
        return DataflowResult {
            block_in: HashMap::new(),
            block_out: HashMap::new(),
        };
    };
    // Restrict the relation to in-function edges.
    let succ_of = |b: BlockId| -> Vec<BlockId> {
        succ(b)
            .into_iter()
            .filter(|s| f.blocks.contains(s))
            .collect()
    };

    // Deterministic block order: RPO from the entry. Backward problems
    // iterate it in reverse, which front-loads exit-adjacent blocks.
    let mut order: Vec<BlockId> = crate::control::reachable_blocks(module, func, &succ_of);
    if config.direction == Direction::Backward {
        order.reverse();
    }

    let is_boundary = |b: BlockId| -> bool {
        match config.direction {
            Direction::Forward => Some(b) == f.entry(),
            Direction::Backward => succ_of(b).is_empty(),
        }
    };

    let mut in_map: HashMap<BlockId, P::Domain> = HashMap::new();
    let mut out_map: HashMap<BlockId, P::Domain> = HashMap::new();
    for &b in &order {
        let v = if is_boundary(b) {
            problem.boundary()
        } else {
            problem.initial()
        };
        in_map.insert(b, v.clone());
        out_map.insert(b, v);
    }

    // Predecessors, computed once (forward problems meet over them;
    // backward problems need them for downstream scheduling).
    let mut preds: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for &b in &order {
        for s in succ_of(b) {
            preds.entry(s).or_default().push(b);
        }
    }

    let mut worklist: VecDeque<BlockId> = order.iter().copied().collect();
    let mut queued: HashSet<BlockId> = order.iter().copied().collect();

    while let Some(b) = worklist.pop_front() {
        queued.remove(&b);

        // Meet into the "from" edge value.
        let merged = if is_boundary(b) {
            problem.boundary()
        } else {
            let mut acc = problem.initial();
            match config.direction {
                Direction::Forward => {
                    for p in preds.get(&b).into_iter().flatten() {
                        if let Some(o) = out_map.get(p) {
                            problem.meet(&mut acc, o);
                        }
                    }
                }
                Direction::Backward => {
                    for s in succ_of(b) {
                        if let Some(i) = in_map.get(&s) {
                            problem.meet(&mut acc, i);
                        }
                    }
                }
            }
            acc
        };

        let (in_edge, out_edge) = match config.direction {
            Direction::Forward => {
                let out = problem.transfer_block(module, func, b, &merged);
                (merged, out)
            }
            Direction::Backward => {
                let input = problem.transfer_block(module, func, b, &merged);
                (input, merged)
            }
        };

        let changed_in = in_map.get(&b) != Some(&in_edge);
        let changed_out = out_map.get(&b) != Some(&out_edge);
        if !changed_in && !changed_out {
            continue;
        }
        in_map.insert(b, in_edge);
        out_map.insert(b, out_edge);

        // Propagate change downstream (successors for forward,
        // predecessors for backward).
        let downstream: Vec<BlockId> = match config.direction {
            Direction::Forward => succ_of(b),
            Direction::Backward => preds.get(&b).cloned().unwrap_or_default(),
        };
        for d in downstream {
            if queued.insert(d) {
                worklist.push_back(d);
            }
        }
    }

    DataflowResult {
        block_in: in_map,
        block_out: out_map,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::*;
    use abcd_ir::{Op, ValueId};

    /// Live variables (backward, may analysis) as the framework's
    /// executable specification: transfer kills defs, gens uses.
    struct LiveVars;

    impl MonotoneFramework for LiveVars {
        type Domain = std::collections::BTreeSet<ValueId>;

        fn boundary(&self) -> Self::Domain {
            Default::default()
        }

        fn initial(&self) -> Self::Domain {
            Default::default()
        }

        fn meet(&self, acc: &mut Self::Domain, other: &Self::Domain) {
            acc.extend(other.iter().copied());
        }

        fn transfer_block(
            &self,
            module: &Module,
            _func: FuncId,
            block: BlockId,
            output: &Self::Domain,
        ) -> Self::Domain {
            let mut live = output.clone();
            let bb = module.block(block).expect("block");
            for &iid in bb.insts.iter().rev() {
                let inst = module.inst(iid).expect("inst");
                if let Some(result) = inst.result {
                    live.remove(&result);
                }
                for v in inst.op.operands() {
                    live.insert(v);
                }
            }
            live
        }
    }

    /// Diamond: a's def is live on the true branch only; at the entry it
    /// is not live (overwritten... ) — checks meet/transfer/backward
    /// traversal end to end.
    #[test]
    fn live_variables_over_diamond() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let t = add_block(&mut m, f);
        let e = add_block(&mut m, f);
        let join = add_block(&mut m, f);

        let cond = load_number(&mut m, entry, 1.0);
        let a = load_number(&mut m, entry, 2.0);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond,
                true_dest: t,
                false_dest: e,
            },
        );
        let _use_a = add(&mut m, t, a, a);
        emit_void(&mut m, t, Op::Branch { dest: join });
        emit_void(&mut m, e, Op::Branch { dest: join });
        emit_void(&mut m, join, Op::Return { value: None });
        link(&mut m, entry, t);
        link(&mut m, entry, e);
        link(&mut m, t, join);
        link(&mut m, e, join);

        let result = solve(
            &m,
            f,
            &|b| crate::control::block_succs(&m, b),
            &SolveConfig {
                direction: Direction::Backward,
            },
            &LiveVars,
        );
        // `a` is used on the true branch, so it is live at entry's OUT
        // edge; `cond` is used by the terminator within entry, so it is
        // live only mid-block (never at an edge).
        let entry_out = result.out_at(entry).expect("entry visited");
        assert!(entry_out.contains(&a));
        assert!(!entry_out.contains(&cond));
        let entry_in = result.in_at(entry).expect("entry visited");
        assert!(!entry_in.contains(&a));
        assert!(!entry_in.contains(&cond));
        // The false branch never uses `a`: it is not live at e's input.
        let e_in = result.in_at(e).expect("e visited");
        assert!(!e_in.contains(&a));
        // Nothing is live at the join's output (return of nothing).
        assert!(result.out_at(join).expect("join visited").is_empty());
    }
}
