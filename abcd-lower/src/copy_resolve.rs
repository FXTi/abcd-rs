//! Slot-level parallel-copy resolution.
//!
//! Phi elimination produces, per CFG edge, a set of parallel copies: every
//! destination must receive the value its source held *before* any copy of
//! the set ran. After register allocation (and coalescing) distinct SSA
//! values may share one slot, so the copy set must be sequentialized in
//! *slot* space — a value-space order that looks safe can clobber a shared
//! source slot, and a slot-space cycle can exist where value space has none.
//!
//! [`resolve_slot_copies`] takes the edge's copies mapped to slot pairs and
//! returns a sequential emission order that preserves parallel semantics: a
//! topological sort (emit copies whose destination slot is not the source of
//! any pending copy), breaking remaining slot cycles through a reserved
//! temporary slot. [`emit_copy`] maps one resolved slot pair to its bytecode.

use std::collections::{HashMap, HashSet, VecDeque};

use abcd_isa::{Bytecode, Reg};

use crate::regalloc::RegSlot;

/// Error returned when a copy set cannot be sequentialized.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum CopyResolveError {
    /// A slot cycle needs a temporary slot, but none was reserved (or the
    /// reserved temporary itself participates in the copy set).
    #[error("slot-level copy cycle requires a reserved temporary slot")]
    CycleNeedsTemp,
}

/// Sequentialize a parallel copy set in slot space (`O(N)`, `#61` `R3-X7`).
///
/// `copies` are `(src_slot, dst_slot)` pairs. `temp` is the per-function
/// reserved temporary slot ([`crate::regalloc::RegAlloc::copy_temp`]); it
/// must be a slot that does not participate in any remaining cycle.
///
/// Same-slot copies are dropped (they are no-ops). The remaining copies are
/// returned in an order that preserves parallel-copy semantics when emitted
/// sequentially.
///
/// Every slot is a register (`ADR-03` / `B4`: the accumulator is an
/// emission-time resource, not a coloring class), so the resolved pairs all
/// lower to the auto-widening `Mov` — acc never appears in copy slots.
pub fn resolve_slot_copies(
    copies: &[(RegSlot, RegSlot)],
    temp: Option<RegSlot>,
) -> Result<Vec<(RegSlot, RegSlot)>, CopyResolveError> {
    if copies.is_empty() {
        return Ok(Vec::new());
    }

    // 1. Deduplicate non-trivial `(src, dst)` pairs in insertion order (`O(N)`).
    let mut seen: HashSet<(RegSlot, RegSlot)> = HashSet::with_capacity(copies.len());
    let mut edges: Vec<(RegSlot, RegSlot)> = Vec::with_capacity(copies.len());
    let mut slot_to_id: HashMap<RegSlot, usize> = HashMap::with_capacity(copies.len() * 2);
    let next_slot_id = |slot: RegSlot, map: &mut HashMap<RegSlot, usize>| -> usize {
        let len = map.len();
        *map.entry(slot).or_insert(len)
    };

    for &(src, dst) in copies {
        if src != dst && seen.insert((src, dst)) {
            let _ = next_slot_id(src, &mut slot_to_id);
            let _ = next_slot_id(dst, &mut slot_to_id);
            edges.push((src, dst));
        }
    }
    if edges.is_empty() {
        return Ok(Vec::new());
    }

    let num_slots = slot_to_id.len();
    let mut src_use_count = vec![0usize; num_slots];
    let mut writers_of_dst: Vec<Vec<usize>> = vec![Vec::new(); num_slots];
    let mut edge_slots: Vec<(usize, usize)> = Vec::with_capacity(edges.len());

    for (idx, &(src, dst)) in edges.iter().enumerate() {
        let s_id = slot_to_id[&src];
        let d_id = slot_to_id[&dst];
        src_use_count[s_id] += 1;
        writers_of_dst[d_id].push(idx);
        edge_slots.push((s_id, d_id));
    }

    // 2. Kahn-style ready queue: any edge `(src, dst)` whose `dst` is read by
    // zero pending edges (`src_use_count[d_id] == 0`) can emit safely (`O(N)`).
    let mut done = vec![false; edges.len()];
    let mut queued = vec![false; edges.len()];
    let mut ready: VecDeque<usize> = VecDeque::with_capacity(edges.len());
    for (idx, &(_, d_id)) in edge_slots.iter().enumerate() {
        if src_use_count[d_id] == 0 {
            queued[idx] = true;
            ready.push_back(idx);
        }
    }

    let mut result: Vec<(RegSlot, RegSlot)> = Vec::with_capacity(edges.len() + 2);
    let drain_ready = |ready: &mut VecDeque<usize>,
                       done: &mut [bool],
                       queued: &mut [bool],
                       src_use_count: &mut [usize],
                       result: &mut Vec<(RegSlot, RegSlot)>| {
        while let Some(idx) = ready.pop_front() {
            if done[idx] {
                continue;
            }
            done[idx] = true;
            result.push(edges[idx]);
            let (s_id, _) = edge_slots[idx];
            src_use_count[s_id] -= 1;
            if src_use_count[s_id] == 0 {
                for &w_idx in &writers_of_dst[s_id] {
                    if !done[w_idx] && !queued[w_idx] {
                        queued[w_idx] = true;
                        ready.push_back(w_idx);
                    }
                }
            }
        }
    };

    drain_ready(
        &mut ready,
        &mut done,
        &mut queued,
        &mut src_use_count,
        &mut result,
    );

    // 3. Break remaining slot cycles in deterministic input order (`O(N)`).
    let mut writer_cursor = vec![0usize; num_slots];
    let mut temp_checked: Option<RegSlot> = None;

    for start_idx in 0..edges.len() {
        if done[start_idx] {
            continue;
        }
        let usable_temp = match temp_checked {
            Some(t) => t,
            None => {
                let Some(t) = temp else {
                    return Err(CopyResolveError::CycleNeedsTemp);
                };
                if let Some(&t_id) = slot_to_id.get(&t) {
                    let participates = edges.iter().enumerate().any(|(i, _)| {
                        !done[i] && (edge_slots[i].0 == t_id || edge_slots[i].1 == t_id)
                    });
                    if participates {
                        return Err(CopyResolveError::CycleNeedsTemp);
                    }
                }
                temp_checked = Some(t);
                t
            }
        };

        let (first_src, first_dst) = edges[start_idx];
        let (first_s_id, _) = edge_slots[start_idx];
        done[start_idx] = true;
        src_use_count[first_s_id] -= 1;
        result.push((first_src, usable_temp));

        let mut cur_slot = first_s_id;
        loop {
            let writers = &writers_of_dst[cur_slot];
            let cursor = &mut writer_cursor[cur_slot];
            while *cursor < writers.len() && done[writers[*cursor]] {
                *cursor += 1;
            }
            if *cursor >= writers.len() {
                break;
            }
            let w_idx = writers[*cursor];
            *cursor += 1;
            done[w_idx] = true;
            result.push(edges[w_idx]);
            let (s_id, _) = edge_slots[w_idx];
            src_use_count[s_id] -= 1;
            if src_use_count[s_id] == 0 {
                for &u_idx in &writers_of_dst[s_id] {
                    if !done[u_idx] && !queued[u_idx] {
                        queued[u_idx] = true;
                        ready.push_back(u_idx);
                    }
                }
            }
            cur_slot = s_id;
        }
        result.push((usable_temp, first_dst));
        if src_use_count[first_s_id] == 0 {
            for &u_idx in &writers_of_dst[first_s_id] {
                if !done[u_idx] && !queued[u_idx] {
                    queued[u_idx] = true;
                    ready.push_back(u_idx);
                }
            }
        }
        drain_ready(
            &mut ready,
            &mut done,
            &mut queued,
            &mut src_use_count,
            &mut result,
        );
    }

    Ok(result)
}

/// Emit one resolved slot-level copy as its bytecode. Every slot is a
/// register, so this is always the auto-widening `Mov` (encodable at any
/// register height — no scratch routing, no acc involvement).
pub fn emit_copy(src: RegSlot, dst: RegSlot) -> Bytecode {
    match (src, dst) {
        (RegSlot::Reg(s), RegSlot::Reg(d)) => Bytecode::Mov(Reg(d), Reg(s)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: u16) -> RegSlot {
        RegSlot::Reg(n)
    }

    #[test]
    fn empty_copy_set_resolves_to_empty() {
        assert_eq!(resolve_slot_copies(&[], Some(r(9))), Ok(vec![]));
        assert_eq!(resolve_slot_copies(&[], None), Ok(vec![]));
    }

    #[test]
    fn singleton_copy_set_is_unchanged() {
        assert_eq!(
            resolve_slot_copies(&[(r(1), r(2))], Some(r(9))),
            Ok(vec![(r(1), r(2))])
        );
    }

    #[test]
    fn same_slot_copies_are_dropped() {
        assert_eq!(resolve_slot_copies(&[(r(1), r(1))], Some(r(9))), Ok(vec![]));
    }

    #[test]
    fn war_hazard_emits_reader_first() {
        // (R1→R2) must not run before (R2→R3) has read R2.
        assert_eq!(
            resolve_slot_copies(&[(r(1), r(2)), (r(2), r(3))], Some(r(9))),
            Ok(vec![(r(2), r(3)), (r(1), r(2))])
        );
    }

    #[test]
    fn two_cycle_is_broken_with_temp() {
        assert_eq!(
            resolve_slot_copies(&[(r(1), r(2)), (r(2), r(1))], Some(r(9))),
            Ok(vec![(r(1), r(9)), (r(2), r(1)), (r(9), r(2))])
        );
    }

    #[test]
    fn three_cycle_is_broken_with_temp() {
        assert_eq!(
            resolve_slot_copies(&[(r(1), r(2)), (r(2), r(3)), (r(3), r(1))], Some(r(9))),
            Ok(vec![(r(1), r(9)), (r(3), r(1)), (r(2), r(3)), (r(9), r(2))])
        );
    }

    #[test]
    fn cycle_without_temp_is_an_error_not_a_panic() {
        assert_eq!(
            resolve_slot_copies(&[(r(1), r(2)), (r(2), r(1))], None),
            Err(CopyResolveError::CycleNeedsTemp)
        );
    }

    #[test]
    fn temp_participating_in_cycle_is_an_error() {
        // Reserved temp collides with a copy participant: refuse rather than
        // silently emitting a corrupt sequence.
        assert_eq!(
            resolve_slot_copies(&[(r(1), r(2)), (r(2), r(1))], Some(r(1))),
            Err(CopyResolveError::CycleNeedsTemp)
        );
    }

    #[test]
    fn emit_copy_maps_slot_pairs_to_a_mov() {
        // `Bytecode` does not implement PartialEq; match structurally.
        assert!(matches!(
            emit_copy(r(1), r(2)),
            Bytecode::Mov(Reg(2), Reg(1))
        ));
        // Reg→Reg at any height is the auto-widening mov — no scratch.
        assert!(matches!(
            emit_copy(r(300), r(600)),
            Bytecode::Mov(Reg(600), Reg(300))
        ));
    }
}
