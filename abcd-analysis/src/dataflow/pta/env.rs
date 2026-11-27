//! Lexical-environment stack reconstruction and monotone closure-capture fixed point.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use abcd_ir::{FuncId, InstId, Module, Op};

use crate::dataflow::heap::AllocSiteSet;

use super::scan::{callable_body, closure_body, collect_const_method_refs};

/// The rung-2 answer to a lexical-environment query: the environment
/// objects a `GetLexVar`/`PutLexVar` at `level` may denote.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EnvAnswer {
    /// The `NewLexEnv`/`NewLexEnvWithName` sites (context-insensitive —
    /// recursion merges, documented).
    pub sites: AllocSiteSet,
    /// The access read past the known stack (or through an unknown
    /// entry): the answer is a lower bound.
    pub has_unknown: bool,
}

/// One lexical-environment stack entry.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct EnvEntry {
    pub(super) sites: BTreeSet<InstId>,
    pub(super) unknown: bool,
}

/// Bounded top-aligned lexical-environment chain for one [`abcd_ir::LexEnvKind`]
/// (`Plain` vs `Sendable`). `frames.last()` is `level = 0` (innermost top of
/// stack); `truncated_outer` records whether outer frames beyond `frames.len()`
/// may exist (depth cap overflow or `PopLexEnv` on an empty/uncertain stack).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct EnvChain {
    pub(super) frames: Vec<EnvEntry>,
    pub(super) truncated_outer: bool,
}

impl EnvChain {
    #[inline]
    pub(super) fn at_level(&self, level: u16) -> Option<&EnvEntry> {
        let lvl = level as usize;
        if lvl < self.frames.len() {
            Some(&self.frames[self.frames.len() - 1 - lvl])
        } else {
            None
        }
    }

    pub(super) fn push_site(&mut self, site: InstId, max_depth: usize) {
        if max_depth == 0 {
            self.frames.clear();
            self.truncated_outer = true;
            return;
        }
        self.frames.push(EnvEntry {
            sites: BTreeSet::from([site]),
            unknown: false,
        });
        if self.frames.len() > max_depth {
            let overflow = self.frames.len() - max_depth;
            self.frames.drain(0..overflow);
            self.truncated_outer = true;
        }
    }

    pub(super) fn pop_frame(&mut self) {
        match self.frames.pop() {
            None => self.truncated_outer = true,
            Some(popped) if popped.unknown => self.truncated_outer = true,
            Some(_) => {}
        }
    }

    /// Top-aligned monotone semilattice join (`self = self ⊔ other`), returning
    /// `true` iff `self` changed.
    pub(super) fn join_into(&mut self, other: &Self) -> bool {
        let joined = join_chains(self, other);
        if *self != joined {
            *self = joined;
            true
        } else {
            false
        }
    }
}

/// Dual lexical-environment stacks (`Plain` and `Sendable` never cross-pop).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct EnvState {
    pub(super) plain: EnvChain,
    pub(super) sendable: EnvChain,
}

impl EnvState {
    #[inline]
    pub(super) fn chain(&self, kind: abcd_ir::LexEnvKind) -> Option<&EnvChain> {
        match kind {
            abcd_ir::LexEnvKind::Plain => Some(&self.plain),
            abcd_ir::LexEnvKind::Sendable => Some(&self.sendable),
            abcd_ir::LexEnvKind::Patch => None,
        }
    }

    pub(super) fn join_into(&mut self, other: &Self) -> bool {
        let c1 = self.plain.join_into(&other.plain);
        let c2 = self.sendable.join_into(&other.sendable);
        c1 || c2
    }
}

/// Apply one instruction's lexical-environment transfer to `state`, returning
/// `true` iff `state` mutated. `Plain` (`newlexenv`/`newlexenvwithname`/
/// `poplexenv`) and `Sendable` (`callruntime.newsendableenv`) evolve on
/// separate stacks; `PopLexEnv` NEVER pops `Sendable`.
fn step_env_inst(op: &Op, iid: InstId, max_depth: usize, state: &mut EnvState) -> bool {
    match op {
        Op::NewLexEnv {
            kind: abcd_ir::LexEnvKind::Sendable,
            ..
        } => {
            state.sendable.push_site(iid, max_depth);
            true
        }
        Op::NewLexEnv { .. } | Op::NewLexEnvWithName { .. } => {
            state.plain.push_site(iid, max_depth);
            true
        }
        Op::PopLexEnv => {
            state.plain.pop_frame();
            true
        }
        _ => false,
    }
}

/// Precomputed CFG metadata for one function in `env_analysis`.
struct EnvFuncCfg {
    /// Reachable blocks in Reverse Post-Order starting at `f.blocks[0]`.
    rpo: Vec<abcd_ir::BlockId>,
    /// Block → position in `rpo` (for reachable blocks owned by `f`).
    rpo_pos: HashMap<abcd_ir::BlockId, usize>,
    /// Prebuilt dense exception-handler map when `has_lex_ops && !try_regions.is_empty()`.
    exc_map: Option<abcd_ir::ExceptionHandlerMap>,
}

/// Outcome of `env_analysis` (including optional `step_budget` cutoff).
pub(super) struct EnvAnalysisOut {
    pub(super) env_stack_at: Vec<Arc<EnvState>>,
    pub(super) env_sites: Vec<bool>,
    pub(super) rounds: usize,
    pub(super) capped: bool,
}

/// The lexical-environment analysis: per-instruction dual environment stacks
/// (`Plain` + `Sendable`) plus the monotone capture fixed point, charged
/// against `step_budget`.
pub(super) fn env_analysis(
    module: &Module,
    max_depth: usize,
    step_budget: usize,
    steps: &mut usize,
) -> EnvAnalysisOut {
    let mut env_sites = vec![false; module.insts.len()];
    let mut has_lex_ops = vec![false; module.functions.len()];
    let mut inst_reached = vec![false; module.insts.len()];
    let mut inst_owner: Vec<Option<usize>> = vec![None; module.insts.len()];
    let mut capture_points: BTreeMap<FuncId, BTreeSet<InstId>> = BTreeMap::new();
    let mut func_cfgs: Vec<EnvFuncCfg> = Vec::with_capacity(module.functions.len());

    for (fi, f) in module.functions.iter().enumerate() {
        let func = FuncId::new(fi as u32);
        if f.is_external || f.blocks.is_empty() {
            func_cfgs.push(EnvFuncCfg {
                rpo: Vec::new(),
                rpo_pos: HashMap::new(),
                exc_map: None,
            });
            continue;
        }
        let exc_map = (!f.try_regions.is_empty())
            .then(|| abcd_ir::ExceptionHandlerMap::build(module, func))
            .flatten();
        let func_block_set: std::collections::HashSet<abcd_ir::BlockId> =
            f.blocks.iter().copied().collect();

        // Iterative post-order DFS from `f.blocks[0]` over Normal edges +
        // `ExceptionHandlerMap` edges from protected blocks that contain at
        // least one non-phi `may_throw` instruction.
        let entry = f.blocks[0];
        let block_succs_aug = |b: abcd_ir::BlockId| -> Vec<abcd_ir::BlockId> {
            let mut out = Vec::new();
            let Some(bb) = module.block(b) else {
                return out;
            };
            if let Some(&last_iid) = bb.insts.last()
                && let Some(last_inst) = module.inst(last_iid)
            {
                let (targets, count) = abcd_ir::normal_succs_inline(&last_inst.op);
                for &t in &targets[..count] {
                    if func_block_set.contains(&t) && !out.contains(&t) {
                        out.push(t);
                    }
                }
            }
            if let Some(map) = &exc_map {
                let handlers = map.handlers_of(b);
                if !handlers.is_empty() {
                    let has_throw = bb.insts.iter().any(|&iid| {
                        module
                            .inst(iid)
                            .is_some_and(|i| !i.op.is_phi() && i.op.effects_in(module).may_throw)
                    });
                    if has_throw {
                        for &h in handlers {
                            if func_block_set.contains(&h) && !out.contains(&h) {
                                out.push(h);
                            }
                        }
                    }
                }
            }
            out
        };

        let mut visited = std::collections::HashSet::with_capacity(f.blocks.len());
        let mut post_order = Vec::with_capacity(f.blocks.len());
        visited.insert(entry);
        let mut dfs_stack: Vec<(abcd_ir::BlockId, Vec<abcd_ir::BlockId>, usize)> =
            vec![(entry, block_succs_aug(entry), 0)];
        while let Some((node, succs, idx)) = dfs_stack.last_mut() {
            if *idx < succs.len() {
                let s = succs[*idx];
                *idx += 1;
                if visited.insert(s) {
                    let next_succs = block_succs_aug(s);
                    dfs_stack.push((s, next_succs, 0));
                }
            } else {
                post_order.push(*node);
                dfs_stack.pop();
            }
        }
        post_order.reverse();
        let mut rpo_pos = HashMap::with_capacity(post_order.len());
        for (pos, &b) in post_order.iter().enumerate() {
            rpo_pos.insert(b, pos);
        }

        for &b in &f.blocks {
            let Some(bb) = module.block(b) else { continue };
            let b_reached = rpo_pos.contains_key(&b);
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if b_reached {
                    if let Some(slot) = inst_reached.get_mut(iid.index()) {
                        *slot = true;
                    }
                    if let Some(slot) = inst_owner.get_mut(iid.index()) {
                        *slot = Some(fi);
                    }
                }
                match &inst.op {
                    Op::NewLexEnv { .. } | Op::NewLexEnvWithName { .. } => {
                        if let Some(slot) = env_sites.get_mut(iid.index()) {
                            *slot = true;
                        }
                        has_lex_ops[fi] = true;
                    }
                    Op::PopLexEnv => {
                        has_lex_ops[fi] = true;
                    }
                    Op::AllocClosure { func }
                    | Op::CreateGenerator { func }
                    | Op::CreateAsyncGenerator { func } => {
                        if let Some(body) = closure_body(module, *func) {
                            capture_points.entry(body).or_default().insert(iid);
                        }
                    }
                    Op::DefineFunc { body, .. } => {
                        capture_points.entry(*body).or_default().insert(iid);
                    }
                    Op::DefineMethod { func, .. } => {
                        if let Some(body) = callable_body(module, *func) {
                            capture_points.entry(body).or_default().insert(iid);
                        }
                    }
                    Op::DefineGetterSetterByValue { getter, setter, .. } => {
                        for &inner in [getter, setter] {
                            if let Some(body) = callable_body(module, inner) {
                                capture_points.entry(body).or_default().insert(iid);
                            }
                        }
                    }
                    Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                        capture_points.entry(cls.ctor).or_default().insert(iid);
                        for mfid in collect_const_method_refs(module, cls.members) {
                            capture_points.entry(mfid).or_default().insert(iid);
                        }
                    }
                    Op::AllocObject { shape } => {
                        for mfid in collect_const_method_refs(module, *shape) {
                            capture_points.entry(mfid).or_default().insert(iid);
                        }
                    }
                    Op::AllocArray { shape: Some(shape) } => {
                        for mfid in collect_const_method_refs(module, *shape) {
                            capture_points.entry(mfid).or_default().insert(iid);
                        }
                    }
                    _ => {}
                }
            }
        }
        func_cfgs.push(EnvFuncCfg {
            rpo: post_order,
            rpo_pos: if has_lex_ops[fi] {
                rpo_pos
            } else {
                HashMap::new()
            },
            exc_map: if has_lex_ops[fi] { exc_map } else { None },
        });
    }

    let empty_state = Arc::new(EnvState::default());
    let mut func_stacks: Vec<Arc<EnvState>> = vec![Arc::clone(&empty_state); module.insts.len()];

    // Recompute one function's instruction stacks in `func_stacks` given its
    // entry capture state, returning `Err(())` if `step_budget` is exceeded.
    let compute_func_stacks = |fi: usize,
                               entry_state: &EnvState,
                               func_stacks: &mut [Arc<EnvState>],
                               steps: &mut usize|
     -> Result<(), ()> {
        let cfg = &func_cfgs[fi];
        if cfg.rpo.is_empty() {
            return Ok(());
        }
        if !has_lex_ops[fi] {
            let entry_arc = if *entry_state == EnvState::default() {
                Arc::clone(&empty_state)
            } else {
                Arc::new(entry_state.clone())
            };
            for &b in &cfg.rpo {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    if module.inst(iid).is_some()
                        && let Some(slot) = func_stacks.get_mut(iid.index())
                    {
                        *slot = Arc::clone(&entry_arc);
                    }
                }
            }
            return Ok(());
        }

        // Phase 1: RPO worklist seeding `entry_state` into `in_state[entry]`
        // (`cfg.rpo[0]`) BEFORE joining predecessor / pre-throw handler edges.
        let n_rpo = cfg.rpo.len();
        let mut in_state: Vec<Option<EnvState>> = vec![None; n_rpo];
        in_state[0] = Some(entry_state.clone());
        let mut worklist: BTreeSet<usize> = BTreeSet::from([0]);

        let join_edge = |target: abcd_ir::BlockId,
                         incoming: &EnvState,
                         in_state: &mut [Option<EnvState>],
                         worklist: &mut BTreeSet<usize>| {
            let Some(&pos) = cfg.rpo_pos.get(&target) else {
                return;
            };
            match &mut in_state[pos] {
                None => {
                    in_state[pos] = Some(incoming.clone());
                    worklist.insert(pos);
                }
                Some(cur) => {
                    if cur.join_into(incoming) {
                        worklist.insert(pos);
                    }
                }
            }
        };

        while let Some(rpo_idx) = worklist.pop_first() {
            *steps += 1;
            if *steps > step_budget {
                return Err(());
            }
            let b = cfg.rpo[rpo_idx];
            let Some(bb) = module.block(b) else { continue };
            let Some(mut state) = in_state[rpo_idx].clone() else {
                continue;
            };
            let handlers = cfg
                .exc_map
                .as_ref()
                .map_or(&[][..], |map| map.handlers_of(b));
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if !handlers.is_empty() && !inst.op.is_phi() && inst.op.effects_in(module).may_throw
                {
                    for &h in handlers {
                        join_edge(h, &state, &mut in_state, &mut worklist);
                    }
                }
                step_env_inst(&inst.op, iid, max_depth, &mut state);
            }
            if let Some(&last_iid) = bb.insts.last()
                && let Some(last_inst) = module.inst(last_iid)
            {
                let (targets, count) = abcd_ir::normal_succs_inline(&last_inst.op);
                for &succ in &targets[..count] {
                    join_edge(succ, &state, &mut in_state, &mut worklist);
                }
            }
        }

        // Phase 2: materialize per-instruction `Arc<EnvState>` in ONE final pass.
        for (rpo_idx, &b) in cfg.rpo.iter().enumerate() {
            let Some(bb) = module.block(b) else { continue };
            let Some(mut state) = in_state[rpo_idx].clone() else {
                continue;
            };
            let mut cur_arc = if state == EnvState::default() {
                Arc::clone(&empty_state)
            } else {
                Arc::new(state.clone())
            };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if let Some(slot) = func_stacks.get_mut(iid.index()) {
                    *slot = Arc::clone(&cur_arc);
                }
                if step_env_inst(&inst.op, iid, max_depth, &mut state) {
                    cur_arc = if state == EnvState::default() {
                        Arc::clone(&empty_state)
                    } else {
                        Arc::new(state.clone())
                    };
                }
            }
        }
        Ok(())
    };

    // Monotone capture fixed point: functions with capture sites start at `⊥`
    // (`func_computed[fi] == false`) so unseeded outer closures never pollute
    // nested closures with a spurious empty stack before their own capture
    // arrives; `entry_stacks[body]` joins monotonically across rounds.
    let default_env = EnvState::default();
    let mut entry_stacks: BTreeMap<FuncId, EnvState> = BTreeMap::new();
    let mut func_computed = vec![false; module.functions.len()];
    let mut dirty_funcs = vec![false; module.functions.len()];
    let mut rounds = 0usize;
    loop {
        rounds += 1;
        if rounds == 1 {
            for (fi, &has_lex) in has_lex_ops.iter().enumerate() {
                let fid = FuncId::new(fi as u32);
                if !capture_points.contains_key(&fid) {
                    func_computed[fi] = true;
                    if has_lex
                        && compute_func_stacks(fi, &default_env, &mut func_stacks, steps).is_err()
                    {
                        return EnvAnalysisOut {
                            env_stack_at: func_stacks,
                            env_sites,
                            rounds,
                            capped: true,
                        };
                    }
                }
            }
        } else {
            for (fi, dirty) in dirty_funcs.iter_mut().enumerate() {
                if *dirty {
                    *dirty = false;
                    func_computed[fi] = true;
                    let func = FuncId::new(fi as u32);
                    let entry = entry_stacks.get(&func).unwrap_or(&default_env);
                    if compute_func_stacks(fi, entry, &mut func_stacks, steps).is_err() {
                        return EnvAnalysisOut {
                            env_stack_at: func_stacks,
                            env_sites,
                            rounds,
                            capped: true,
                        };
                    }
                }
            }
        }

        let mut changed = false;
        for (&body, points) in &capture_points {
            let mut round_chain: Option<EnvState> = None;
            for &p in points {
                if inst_reached.get(p.index()).copied().unwrap_or(false)
                    && inst_owner
                        .get(p.index())
                        .copied()
                        .flatten()
                        .is_some_and(|owner_fi| func_computed[owner_fi])
                    && let Some(stack) = func_stacks.get(p.index())
                {
                    *steps += 1;
                    if *steps > step_budget {
                        return EnvAnalysisOut {
                            env_stack_at: func_stacks,
                            env_sites,
                            rounds,
                            capped: true,
                        };
                    }
                    match &mut round_chain {
                        None => round_chain = Some((**stack).clone()),
                        Some(cur) => {
                            let _ = cur.join_into(stack);
                        }
                    }
                }
            }
            let Some(candidate) = round_chain else {
                continue;
            };
            let advanced = match entry_stacks.get_mut(&body) {
                None => {
                    entry_stacks.insert(body, candidate);
                    true
                }
                Some(prev) => prev.join_into(&candidate),
            };
            if advanced {
                changed = true;
                if let Some(slot) = dirty_funcs.get_mut(body.index()) {
                    *slot = true;
                }
            }
        }
        if !changed {
            // Seed any remaining unreached/isolated self-capturing closure components
            // at `default_env` so their own internal `NewLexEnv`/`PopLexEnv` ops run.
            let mut seeded_uncomputed = false;
            for (fi, computed) in func_computed.iter().enumerate() {
                if !*computed {
                    let fid = FuncId::new(fi as u32);
                    entry_stacks.entry(fid).or_default();
                    dirty_funcs[fi] = true;
                    seeded_uncomputed = true;
                }
            }
            if !seeded_uncomputed {
                return EnvAnalysisOut {
                    env_stack_at: func_stacks,
                    env_sites,
                    rounds,
                    capped: false,
                };
            }
        }
    }
}

/// Top-aligned join of two environment chains (`level = 0` is the innermost top
/// `frames[len - 1]`). Positions present on only one side become `unknown = true`
/// while retaining known sites; `truncated_outer` joins disjunctively.
pub(super) fn join_chains(a: &EnvChain, b: &EnvChain) -> EnvChain {
    let len = a.frames.len().max(b.frames.len());
    let mut frames = Vec::with_capacity(len);
    for rev_pos in (0..len).rev() {
        let level = rev_pos as u16;
        match (a.at_level(level), b.at_level(level)) {
            (Some(x), Some(y)) => frames.push(EnvEntry {
                sites: x.sites.union(&y.sites).copied().collect(),
                unknown: x.unknown || y.unknown,
            }),
            (Some(x), None) | (None, Some(x)) => frames.push(EnvEntry {
                sites: x.sites.clone(),
                unknown: true,
            }),
            (None, None) => unreachable!(),
        }
    }
    EnvChain {
        frames,
        truncated_outer: a.truncated_outer || b.truncated_outer,
    }
}
