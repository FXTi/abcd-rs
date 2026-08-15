//! CFG construction from flat bytecode.
//!
//! Scans a method's bytecode to identify basic block leaders, then partitions
//! the instruction stream into [`RawBlock`]s with successor/predecessor edges.

use std::collections::{BTreeSet, HashMap};

use abcd_file::MethodBody;
use abcd_isa::Bytecode;

/// A raw basic block before SSA construction.
///
/// Represents a contiguous range of bytecodes `[start..end)` with known
/// control-flow successors and exception handler edges.
#[derive(Debug)]
pub struct RawBlock {
    /// Instruction index of the first bytecode in this block.
    pub start: usize,
    /// Instruction index one past the last bytecode (exclusive).
    pub end: usize,
    /// Normal control-flow successors (jump targets / fall-through).
    pub succs: Vec<usize>,
    /// Exception handler targets (from TryBlock coverage).
    pub catch_succs: Vec<usize>,
}

/// Result of CFG construction: ordered blocks + leader→block-index mapping.
#[derive(Debug)]
pub struct RawCfg {
    /// Basic blocks in leader order.
    pub blocks: Vec<RawBlock>,
    /// Maps instruction index (leader) → index into `blocks`.
    pub leader_to_block: HashMap<usize, usize>,
}

/// Build a CFG from a method body's bytecodes and try-blocks.
///
/// Returns `None` if the method body has no bytecodes.
pub fn build_cfg(body: &MethodBody) -> Option<RawCfg> {
    let bytecodes = &body.bytecodes;
    if bytecodes.is_empty() {
        return None;
    }

    // Phase 1: Identify leaders (block start points).
    let mut leaders = BTreeSet::new();
    leaders.insert(0); // entry point is always a leader

    for (idx, bc) in bytecodes.iter().enumerate() {
        if bc.is_jump() {
            // Jump target is a leader.
            if let Some(target) = jump_target(bc) {
                leaders.insert(target);
            }
            // Instruction after a jump is a leader (fall-through for conditional,
            // or start of next block for unconditional).
            if idx + 1 < bytecodes.len() {
                leaders.insert(idx + 1);
            }
        } else if bc.is_terminator() {
            // return/throw: next instruction is a leader.
            if idx + 1 < bytecodes.len() {
                leaders.insert(idx + 1);
            }
        }
    }

    // Catch handler entries are also leaders.
    for try_block in &body.try_blocks {
        for catch in &try_block.catches {
            leaders.insert(catch.handler as usize);
        }
    }

    // Phase 2: Partition into blocks.
    let sorted_leaders: Vec<usize> = leaders.iter().copied().collect();
    let mut leader_to_block: HashMap<usize, usize> = HashMap::new();
    let mut blocks: Vec<RawBlock> = Vec::new();

    for (bi, &leader) in sorted_leaders.iter().enumerate() {
        let end = if bi + 1 < sorted_leaders.len() {
            sorted_leaders[bi + 1]
        } else {
            bytecodes.len()
        };
        leader_to_block.insert(leader, bi);
        blocks.push(RawBlock {
            start: leader,
            end,
            succs: Vec::new(),
            catch_succs: Vec::new(),
        });
    }

    // Phase 3: Compute successor edges.
    for bi in 0..blocks.len() {
        let block_end = blocks[bi].end;
        if block_end == 0 {
            continue;
        }
        let last_idx = block_end - 1;
        let last_bc = &bytecodes[last_idx];

        if last_bc.is_jump() {
            if let Some(target) = jump_target(last_bc) {
                if let Some(&target_bi) = leader_to_block.get(&target) {
                    blocks[bi].succs.push(target_bi);
                }
            }
            // Conditional jumps also fall through.
            if is_conditional_jump(last_bc) {
                if block_end < bytecodes.len() {
                    if let Some(&fall_bi) = leader_to_block.get(&block_end) {
                        blocks[bi].succs.push(fall_bi);
                    }
                }
            }
        } else if !last_bc.is_terminator() {
            // Non-terminator: implicit fall-through.
            if block_end < bytecodes.len() {
                if let Some(&fall_bi) = leader_to_block.get(&block_end) {
                    blocks[bi].succs.push(fall_bi);
                }
            }
        }
        // return/throw have no successors.
    }

    // Phase 4: Exception handler edges.
    for try_block in &body.try_blocks {
        let try_start = try_block.start as usize;
        let try_end = (try_block.start + try_block.len) as usize;

        // Collect catch handler block indices.
        let catch_targets: Vec<usize> = try_block
            .catches
            .iter()
            .filter_map(|c| leader_to_block.get(&(c.handler as usize)).copied())
            .collect();

        // For each block that overlaps the try region, add catch edges.
        for bi in 0..blocks.len() {
            let bs = blocks[bi].start;
            let be = blocks[bi].end;
            // Block overlaps try region if [bs..be) ∩ [try_start..try_end) ≠ ∅
            if bs < try_end && be > try_start {
                for &ct in &catch_targets {
                    if !blocks[bi].catch_succs.contains(&ct) {
                        blocks[bi].catch_succs.push(ct);
                    }
                }
            }
        }
    }

    Some(RawCfg {
        blocks,
        leader_to_block,
    })
}

/// Extract the jump target instruction index from a jump bytecode.
fn jump_target(bc: &Bytecode) -> Option<usize> {
    use Bytecode::*;
    match bc {
        Jmp(l)
        | Jeqz(l)
        | Jnez(l)
        | Jstricteqz(l)
        | Jnstricteqz(l)
        | Jeqnull(l)
        | Jnenull(l)
        | Jstricteqnull(l)
        | Jnstricteqnull(l)
        | Jequndefined(l)
        | Jneundefined(l)
        | Jstrictequndefined(l)
        | Jnstrictequndefined(l) => Some(l.0 as usize),
        Jeq(_, l) | Jne(_, l) | Jstricteq(_, l) | Jnstricteq(_, l) => Some(l.0 as usize),
        _ => None,
    }
}

/// Returns true if the bytecode is a conditional jump (has fall-through).
fn is_conditional_jump(bc: &Bytecode) -> bool {
    use Bytecode::*;
    matches!(
        bc,
        Jeqz(_)
            | Jnez(_)
            | Jstricteqz(_)
            | Jnstricteqz(_)
            | Jeqnull(_)
            | Jnenull(_)
            | Jstricteqnull(_)
            | Jnstricteqnull(_)
            | Jequndefined(_)
            | Jneundefined(_)
            | Jstrictequndefined(_)
            | Jnstrictequndefined(_)
            | Jeq(_, _)
            | Jne(_, _)
            | Jstricteq(_, _)
            | Jnstricteq(_, _)
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use abcd_isa::Label;

    fn make_body(bytecodes: Vec<Bytecode>) -> MethodBody {
        MethodBody {
            num_vregs: 0,
            num_args: 0,
            bytecodes,
            try_blocks: Vec::new(),
        }
    }

    #[test]
    fn linear_block() {
        let body = make_body(vec![Bytecode::Ldundefined, Bytecode::Return]);
        let cfg = build_cfg(&body).unwrap();
        assert_eq!(cfg.blocks.len(), 1);
        assert_eq!(cfg.blocks[0].start, 0);
        assert_eq!(cfg.blocks[0].end, 2);
        assert!(cfg.blocks[0].succs.is_empty());
    }

    #[test]
    fn conditional_branch() {
        let body = make_body(vec![
            Bytecode::Ldtrue,          // 0
            Bytecode::Jeqz(Label(3)),  // 1 → jump to 3
            Bytecode::Return,          // 2 (fall-through)
            Bytecode::Returnundefined, // 3 (jump target)
        ]);
        let cfg = build_cfg(&body).unwrap();
        assert_eq!(cfg.blocks.len(), 3);
        // Block 0: [0..2), succs = [block for 3, block for 2]
        let b0 = &cfg.blocks[0];
        assert_eq!(b0.start, 0);
        assert_eq!(b0.end, 2);
        assert_eq!(b0.succs.len(), 2);
    }

    #[test]
    fn unconditional_jump() {
        let body = make_body(vec![
            Bytecode::Jmp(Label(2)),   // 0 → jump to 2
            Bytecode::Return,          // 1
            Bytecode::Returnundefined, // 2
        ]);
        let cfg = build_cfg(&body).unwrap();
        assert_eq!(cfg.blocks.len(), 3);
        let b0 = &cfg.blocks[0];
        assert_eq!(b0.succs.len(), 1); // only jump target, no fall-through
    }

    #[test]
    fn try_catch_edges() {
        use abcd_file::{CatchBlock, TryBlock};
        let body = MethodBody {
            num_vregs: 0,
            num_args: 0,
            bytecodes: vec![
                Bytecode::Ldundefined, // 0 (try start)
                Bytecode::Return,      // 1
                Bytecode::Ldnull,      // 2 (catch handler)
                Bytecode::Return,      // 3
            ],
            try_blocks: vec![TryBlock {
                start: 0,
                len: 2,
                catches: vec![CatchBlock {
                    type_idx: 0,
                    handler: 2,
                    len: 2,
                }],
            }],
        };
        let cfg = build_cfg(&body).unwrap();
        // Block covering [0..2) should have catch edge to block starting at 2.
        let b0 = &cfg.blocks[0];
        assert!(!b0.catch_succs.is_empty());
    }
}
