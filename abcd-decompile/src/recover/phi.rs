//! Out-of-SSA parallel-copy scheduling and cycle breaking (`R5-6a`).

use super::*;

impl<'m> Recover<'m> {
    /// Compute the exact evaluation order in which `flush_phi_tail` will
    /// evaluate incoming `val` expressions for a single `(pred, to, exceptional)`
    /// phi group `(phi_res, incoming_val)`, using [`schedule_parallel_phi_copies`].
    pub(super) fn schedule_phi_eval_order(&self, entries: &[(ValueId, ValueId)]) -> Vec<ValueId> {
        let peel = |mut v: ValueId| -> ValueId {
            let mut g = 0usize;
            while let Some(&t) = self.alias.get(&v) {
                v = t;
                g += 1;
                if g > 32 {
                    break;
                }
            }
            v
        };
        if entries.len() <= 1 || entries.iter().all(|&(p, v)| peel(v) == p) {
            return entries.iter().map(|&(_, v)| v).collect();
        }

        let k = entries.len();
        let mut target_id: HashMap<ValueId, usize> = HashMap::with_capacity(k);
        let mut item_tid: Vec<usize> = Vec::with_capacity(k);
        let mut writers_of_tid: Vec<Vec<usize>> = Vec::new();
        for (j, &(phi_res, _)) in entries.iter().enumerate() {
            let tid = *target_id.entry(phi_res).or_insert_with(|| {
                let id = writers_of_tid.len();
                writers_of_tid.push(Vec::new());
                id
            });
            item_tid.push(tid);
            writers_of_tid[tid].push(j);
        }

        let mut read_tids: Vec<Vec<usize>> = Vec::with_capacity(k);
        let mut is_self_noop_cand: Vec<bool> = Vec::with_capacity(k);
        for &(phi_res, val) in entries {
            is_self_noop_cand.push(peel(val) == phi_res);
            let mut r_tids: Vec<usize> = Vec::new();
            let mut visited: HashSet<ValueId> = HashSet::new();
            let mut stack: Vec<ValueId> = vec![val];
            while let Some(raw) = stack.pop() {
                let v = peel(raw);
                if !visited.insert(v) {
                    continue;
                }
                if self.inline.contains(&v) {
                    if let Some(Value {
                        def: ValueDef::Inst(ciid),
                        ..
                    }) = self.module.value(v)
                        && let Some(cinst) = self.module.inst(*ciid)
                    {
                        stack.extend(ordered_eval_operands(&cinst.op));
                    }
                } else if let Some(&rtid) = target_id.get(&v) {
                    r_tids.push(rtid);
                }
            }
            r_tids.sort_unstable();
            r_tids.dedup();
            read_tids.push(r_tids);
        }

        let steps =
            schedule_parallel_phi_copies(&writers_of_tid, &item_tid, is_self_noop_cand, read_tids);
        let mut victim_cleared = vec![false; k];
        let mut eval_order = Vec::with_capacity(k);
        for step in steps {
            match step {
                ParallelPhiStep::BreakCycle { victim } => {
                    victim_cleared[victim] = true;
                    eval_order.push(entries[victim].1);
                }
                ParallelPhiStep::Emit(j) => {
                    if !victim_cleared[j] {
                        eval_order.push(entries[j].1);
                    }
                }
            }
        }
        eval_order
    }

    /// Schedule parallel out-of-SSA `PhiAssign` copies per
    /// `(pred, to, exceptional)` edge via [`schedule_parallel_phi_copies`] so
    /// inlined expressions and cyclic phi updates never clobber a variable
    /// before a sibling copy reads it.
    pub(super) fn flush_phi_tail(
        &mut self,
        blocks: &mut [BlockStmts],
        block_index: &HashMap<BlockId, usize>,
        phi_tail: Vec<PendingPhiAssign>,
    ) {
        let mut groups: Vec<PhiEdgeGroup> = Vec::new();
        let mut group_idx: HashMap<(BlockId, BlockId, bool), usize> = HashMap::new();
        for item in phi_tail {
            if !block_index.contains_key(&item.pred) {
                continue;
            }
            let key = (item.pred, item.to, item.exceptional);
            if let Some(&gi) = group_idx.get(&key) {
                groups[gi].assigns.push((item.target, item.value));
            } else {
                let gi = groups.len();
                group_idx.insert(key, gi);
                groups.push(PhiEdgeGroup {
                    pred: item.pred,
                    to: item.to,
                    exceptional: item.exceptional,
                    assigns: vec![(item.target, item.value)],
                });
            }
        }

        let mut synth_phi_seq: u32 = 0;
        for PhiEdgeGroup {
            pred,
            to,
            exceptional,
            assigns,
        } in groups
        {
            let Some(&bi) = block_index.get(&pred) else {
                continue;
            };
            let (decls, emitted) = schedule_parallel_phi_stmts(
                assigns,
                to,
                exceptional,
                &mut self.legal,
                &mut synth_phi_seq,
            );
            if !decls.is_empty()
                && let Some(entry_blk) = blocks.first_mut()
            {
                let insert_at = entry_blk
                    .stmts
                    .iter()
                    .take_while(|s| matches!(s, Stmt::CatchBind { .. } | Stmt::PhiDecl { .. }))
                    .count();
                entry_blk.stmts.splice(insert_at..insert_at, decls);
            }
            blocks[bi].stmts.extend(emitted);
        }
    }
}

/// One step of the canonical parallel-copy out-of-SSA scheduler (`R5-6a`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ParallelPhiStep {
    /// Emit assignment `j` directly (`target_j = value_j`).
    Emit(usize),
    /// Save `value_victim` into a fresh temporary and replace `value_victim`
    /// with that temporary to break a permutation cycle.
    BreakCycle { victim: usize },
}

/// Schedule `k` parallel assignments `(item_tid[j], read_tids[j])` in `O(k + E)`
/// via a deterministic min-index ready heap and cycle-breaking walk (`R5-6a`).
pub(crate) fn schedule_parallel_phi_copies(
    writers_of_tid: &[Vec<usize>],
    item_tid: &[usize],
    mut is_self_noop_cand: Vec<bool>,
    mut read_tids: Vec<Vec<usize>>,
) -> Vec<ParallelPhiStep> {
    let k = item_tid.len();
    let nt = writers_of_tid.len();
    let mut writers_rem: Vec<usize> = writers_of_tid.iter().map(Vec::len).collect();
    let mut readers_of_tid: Vec<Vec<usize>> = vec![Vec::new(); nt];
    let mut total_readers_rem: Vec<usize> = vec![0; nt];
    let mut self_reads: Vec<bool> = vec![false; k];

    for (i, r_tids) in read_tids.iter().enumerate() {
        for &rtid in r_tids {
            if rtid == item_tid[i] {
                self_reads[i] = true;
            }
            readers_of_tid[rtid].push(i);
            total_readers_rem[rtid] += 1;
        }
    }

    let mut done = vec![false; k];
    let mut victim_cleared = vec![false; k];
    let mut in_heap = vec![false; k];
    let mut ready_heap: std::collections::BinaryHeap<std::cmp::Reverse<usize>> =
        std::collections::BinaryHeap::new();
    let is_ready = |j: usize,
                    done: &[bool],
                    is_self_noop_cand: &[bool],
                    writers_rem: &[usize],
                    total_readers_rem: &[usize],
                    self_reads: &[bool],
                    item_tid: &[usize]|
     -> bool {
        if done[j] {
            return false;
        }
        let tid = item_tid[j];
        (is_self_noop_cand[j] && writers_rem[tid] == 1)
            || total_readers_rem[tid] == usize::from(self_reads[j])
    };

    for (j, in_h) in in_heap.iter_mut().enumerate().take(k) {
        if is_ready(
            j,
            &done,
            &is_self_noop_cand,
            &writers_rem,
            &total_readers_rem,
            &self_reads,
            item_tid,
        ) {
            *in_h = true;
            ready_heap.push(std::cmp::Reverse(j));
        }
    }

    let mut remaining = k;
    let mut scan_cursor = 0usize;
    let mut reader_cursor = vec![0usize; nt];
    let mut path_pos: Vec<Option<usize>> = vec![None; k];
    let mut steps: Vec<ParallelPhiStep> = Vec::with_capacity(k + 2);

    while remaining > 0 {
        let mut next_ready = None;
        while let Some(std::cmp::Reverse(j)) = ready_heap.pop() {
            if !done[j] {
                next_ready = Some(j);
                break;
            }
        }

        if let Some(j) = next_ready {
            done[j] = true;
            remaining -= 1;
            steps.push(ParallelPhiStep::Emit(j));
            let wtid = item_tid[j];
            writers_rem[wtid] -= 1;
            if writers_rem[wtid] == 1 {
                for &w in &writers_of_tid[wtid] {
                    if !in_heap[w]
                        && is_ready(
                            w,
                            &done,
                            &is_self_noop_cand,
                            &writers_rem,
                            &total_readers_rem,
                            &self_reads,
                            item_tid,
                        )
                    {
                        in_heap[w] = true;
                        ready_heap.push(std::cmp::Reverse(w));
                    }
                }
            }
            for rtid in std::mem::take(&mut read_tids[j]) {
                total_readers_rem[rtid] -= 1;
                if total_readers_rem[rtid] <= 1 {
                    for &w in &writers_of_tid[rtid] {
                        if !in_heap[w]
                            && is_ready(
                                w,
                                &done,
                                &is_self_noop_cand,
                                &writers_rem,
                                &total_readers_rem,
                                &self_reads,
                                item_tid,
                            )
                        {
                            in_heap[w] = true;
                            ready_heap.push(std::cmp::Reverse(w));
                        }
                    }
                }
            }
            continue;
        }

        while scan_cursor < k && (done[scan_cursor] || victim_cleared[scan_cursor]) {
            scan_cursor += 1;
        }
        let start = if scan_cursor < k {
            scan_cursor
        } else {
            match (0..k).find(|&i| !done[i]) {
                Some(i) => i,
                None => break,
            }
        };
        let mut path: Vec<usize> = Vec::new();
        let mut cur = start;
        let victim = loop {
            if let Some(pos) = path_pos[cur] {
                let v = path[pos..]
                    .iter()
                    .copied()
                    .filter(|&x| !victim_cleared[x])
                    .min()
                    .unwrap_or_else(|| path[pos..].iter().copied().min().unwrap_or(cur));
                break v;
            }
            path_pos[cur] = Some(path.len());
            path.push(cur);
            let ctid = item_tid[cur];
            let rlist = &readers_of_tid[ctid];
            let cursor = &mut reader_cursor[ctid];
            while *cursor < rlist.len() {
                let r = rlist[*cursor];
                if !done[r] && !victim_cleared[r] && r != cur {
                    break;
                }
                *cursor += 1;
            }
            if *cursor < rlist.len() {
                cur = rlist[*cursor];
            } else {
                break cur;
            }
        };
        for &node in &path {
            path_pos[node] = None;
        }

        steps.push(ParallelPhiStep::BreakCycle { victim });
        is_self_noop_cand[victim] = false;
        self_reads[victim] = false;
        victim_cleared[victim] = true;
        for rtid in std::mem::take(&mut read_tids[victim]) {
            total_readers_rem[rtid] -= 1;
            if total_readers_rem[rtid] <= 1 {
                for &w in &writers_of_tid[rtid] {
                    if !in_heap[w]
                        && is_ready(
                            w,
                            &done,
                            &is_self_noop_cand,
                            &writers_rem,
                            &total_readers_rem,
                            &self_reads,
                            item_tid,
                        )
                    {
                        in_heap[w] = true;
                        ready_heap.push(std::cmp::Reverse(w));
                    }
                }
            }
        }
        if !in_heap[victim]
            && is_ready(
                victim,
                &done,
                &is_self_noop_cand,
                &writers_rem,
                &total_readers_rem,
                &self_reads,
                item_tid,
            )
        {
            in_heap[victim] = true;
            ready_heap.push(std::cmp::Reverse(victim));
        }
    }

    steps
}

/// Schedule a parallel `(target, value)` `PhiAssign` batch onto `(decls, assigns)`,
/// shared across Stage-A `flush_phi_tail` and Stage-B structuring (`R5-6a`).
pub(crate) fn schedule_parallel_phi_stmts(
    assigns: Vec<(String, Expr)>,
    to: BlockId,
    exceptional: bool,
    legal: &mut Legalizer,
    synth_phi_seq: &mut u32,
) -> (Vec<Stmt>, Vec<Stmt>) {
    if assigns.len() <= 1
        || assigns
            .iter()
            .all(|(target, value)| is_self_phi_assign(target, value))
    {
        let emitted = assigns
            .into_iter()
            .map(|(target, value)| Stmt::PhiAssign {
                target,
                value,
                to,
                exceptional,
            })
            .collect();
        return (Vec::new(), emitted);
    }

    let k = assigns.len();
    let mut items = assigns;
    let mut target_id: HashMap<String, usize> = HashMap::with_capacity(k);
    let mut item_tid: Vec<usize> = Vec::with_capacity(k);
    let mut writers_of_tid: Vec<Vec<usize>> = Vec::new();
    for (j, (target, _)) in items.iter().enumerate() {
        let tid = *target_id.entry(target.clone()).or_insert_with(|| {
            let id = writers_of_tid.len();
            writers_of_tid.push(Vec::new());
            id
        });
        item_tid.push(tid);
        writers_of_tid[tid].push(j);
    }

    let mut read_tids: Vec<Vec<usize>> = Vec::with_capacity(k);
    let mut is_self_noop_cand: Vec<bool> = Vec::with_capacity(k);
    for (target, value) in &items {
        is_self_noop_cand.push(is_self_phi_assign(target, value));
        let raw_reads = collect_expr_reads(value);
        let mut r_tids: Vec<usize> = raw_reads
            .iter()
            .filter_map(|name| target_id.get(name).copied())
            .collect();
        r_tids.sort_unstable();
        r_tids.dedup();
        read_tids.push(r_tids);
    }

    let steps =
        schedule_parallel_phi_copies(&writers_of_tid, &item_tid, is_self_noop_cand, read_tids);
    let mut decls = Vec::new();
    let mut emitted = Vec::with_capacity(k + 2);
    for step in steps {
        match step {
            ParallelPhiStep::BreakCycle { victim } => {
                let tmp = legal.mint("phi");
                let synth_vid = ValueId::new(u32::MAX.saturating_sub(*synth_phi_seq));
                *synth_phi_seq = synth_phi_seq.saturating_add(1);
                decls.push(Stmt::PhiDecl {
                    name: tmp.clone(),
                    value_id: synth_vid,
                });
                let old_val = std::mem::replace(&mut items[victim].1, Expr::Ident(tmp.clone()));
                emitted.push(Stmt::PhiAssign {
                    target: tmp,
                    value: old_val,
                    to,
                    exceptional,
                });
            }
            ParallelPhiStep::Emit(j) => {
                emitted.push(Stmt::PhiAssign {
                    target: items[j].0.clone(),
                    value: items[j].1.clone(),
                    to,
                    exceptional,
                });
            }
        }
    }
    (decls, emitted)
}
