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

use std::collections::HashSet;

use abcd_isa::{Bytecode, Reg};

use super::regalloc::RegSlot;

/// Error returned when a copy set cannot be sequentialized.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum CopyResolveError {
    /// A slot cycle needs a temporary slot, but none was reserved (or the
    /// reserved temporary itself participates in the copy set).
    #[error("slot-level copy cycle requires a reserved temporary slot")]
    CycleNeedsTemp,
}

/// Sequentialize a parallel copy set in slot space.
///
/// `copies` are `(src_slot, dst_slot)` pairs. `temp` is the per-function
/// reserved temporary slot ([`super::regalloc::RegAlloc::copy_temp`]); it
/// must be a slot that does not participate in the copy set.
///
/// Same-slot copies are dropped (they are no-ops). The remaining copies are
/// returned in an order that preserves parallel-copy semantics when emitted
/// sequentially.
pub fn resolve_slot_copies(
    copies: &[(RegSlot, RegSlot)],
    temp: Option<RegSlot>,
) -> Result<Vec<(RegSlot, RegSlot)>, CopyResolveError> {
    // Drop same-slot no-ops and duplicate pairs.
    let mut pending: Vec<(RegSlot, RegSlot)> = Vec::new();
    for &(src, dst) in copies {
        if src != dst && !pending.contains(&(src, dst)) {
            pending.push((src, dst));
        }
    }

    let mut result: Vec<(RegSlot, RegSlot)> = Vec::new();

    // Topological passes: emit every copy whose destination slot is not the
    // source of any pending copy. Overwriting that destination cannot
    // clobber a value a later copy still needs to read.
    while !pending.is_empty() {
        let srcs: HashSet<RegSlot> = pending.iter().map(|(s, _)| *s).collect();
        let mut next_pending = Vec::new();
        let mut progress = false;
        for &(src, dst) in &pending {
            if !srcs.contains(&dst) {
                result.push((src, dst));
                progress = true;
            } else {
                next_pending.push((src, dst));
            }
        }
        pending = next_pending;
        if !progress {
            break;
        }
    }

    // What remains is one or more slot cycles. Break each through the
    // reserved temporary: save the first source, walk the cycle, restore.
    while !pending.is_empty() {
        let usable_temp = match temp {
            Some(t) if !pending.iter().any(|&(s, d)| s == t || d == t) => t,
            _ => return Err(CopyResolveError::CycleNeedsTemp),
        };
        let (first_src, first_dst) = pending.remove(0);
        result.push((first_src, usable_temp));
        let mut cur = first_src;
        while let Some(pos) = pending.iter().position(|&(_, d)| d == cur) {
            let (s, d) = pending.remove(pos);
            result.push((s, d));
            cur = s;
        }
        result.push((usable_temp, first_dst));
    }

    Ok(result)
}

/// Emit one resolved slot-level copy as a bytecode.
/// Returns `None` for `Acc → Acc` (no machine operation needed).
pub fn emit_copy(src: RegSlot, dst: RegSlot) -> Option<Bytecode> {
    match (src, dst) {
        (RegSlot::Reg(s), RegSlot::Reg(d)) => Some(Bytecode::Mov(Reg(d), Reg(s))),
        (RegSlot::Acc, RegSlot::Reg(d)) => Some(Bytecode::Sta(Reg(d))),
        (RegSlot::Reg(s), RegSlot::Acc) => Some(Bytecode::Lda(Reg(s))),
        (RegSlot::Acc, RegSlot::Acc) => None,
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
        // Acc → Acc is a same-slot copy: skipped, no temp consulted.
        assert_eq!(
            resolve_slot_copies(&[(RegSlot::Acc, RegSlot::Acc)], None),
            Ok(vec![])
        );
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
    fn acc_cycle_is_broken_with_temp() {
        // Swap Acc ↔ R1: Sta tmp; Lda R1; Mov R1, tmp at the bytecode level.
        assert_eq!(
            resolve_slot_copies(&[(RegSlot::Acc, r(1)), (r(1), RegSlot::Acc)], Some(r(9))),
            Ok(vec![
                (RegSlot::Acc, r(9)),
                (r(1), RegSlot::Acc),
                (r(9), r(1))
            ])
        );
    }

    #[test]
    fn acc_can_serve_as_temp_for_reg_cycle() {
        assert_eq!(
            resolve_slot_copies(&[(r(1), r(2)), (r(2), r(1))], Some(RegSlot::Acc)),
            Ok(vec![
                (r(1), RegSlot::Acc),
                (r(2), r(1)),
                (RegSlot::Acc, r(2))
            ])
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
    fn emit_copy_maps_slot_pairs_to_bytecodes() {
        // `Bytecode` does not implement PartialEq; match structurally.
        assert!(matches!(
            emit_copy(r(1), r(2)),
            Some(Bytecode::Mov(Reg(2), Reg(1)))
        ));
        assert!(matches!(
            emit_copy(RegSlot::Acc, r(2)),
            Some(Bytecode::Sta(Reg(2)))
        ));
        assert!(matches!(
            emit_copy(r(1), RegSlot::Acc),
            Some(Bytecode::Lda(Reg(1)))
        ));
        assert!(emit_copy(RegSlot::Acc, RegSlot::Acc).is_none());
    }
}
