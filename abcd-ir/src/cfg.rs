use std::collections::{BTreeMap, BTreeSet};

/// Index of a basic block within the CFG.
pub type BlockId = usize;

/// A basic block: a maximal sequence of instructions with no internal branches.
#[derive(Debug, Clone)]
pub struct BasicBlock {
    /// Unique block index.
    pub id: BlockId,
    /// Byte offset of the first instruction.
    pub start: u32,
    /// Byte offset past the last instruction (exclusive).
    pub end: u32,
    /// Index range into the instruction array [first_insn..last_insn).
    pub first_insn: usize,
    pub last_insn: usize,
    /// Successor block IDs.
    pub succs: Vec<BlockId>,
    /// Predecessor block IDs.
    pub preds: Vec<BlockId>,
    /// If this block is a catch handler entry.
    pub is_catch_handler: bool,
}

/// Control flow graph for a single method.
#[derive(Debug)]
pub struct CFG {
    /// Basic blocks, indexed by BlockId.
    pub blocks: Vec<BasicBlock>,
    /// Entry block ID (always 0).
    pub entry: BlockId,
    /// Map from instruction byte offset to block ID.
    offset_to_block: BTreeMap<u32, BlockId>,
}

/// Check if a throw instruction is a conditional/runtime check that falls through
/// in normal execution (TDZ checks, type checks, etc.)
fn is_conditional_throw(mnemonic: &str) -> bool {
    matches!(
        mnemonic,
        "throw.undefinedifholewithname"
            | "throw.undefinedifhole"
            | "throw.ifsupernotcorrectcall"
            | "throw.ifnotobject"
            | "throw.constassignment"
            | "throw.notexists"
            | "throw.patternnoncoercible"
            | "throw.deletesuperproperty"
    )
}

impl CFG {
    /// Look up which block contains the given byte offset.
    pub fn block_at_offset(&self, offset: u32) -> Option<BlockId> {
        // Find the block whose start <= offset < end
        self.offset_to_block
            .range(..=offset)
            .next_back()
            .map(|(_, &id)| id)
    }

    /// Build a CFG from decoded instructions and try-block metadata.
    pub fn build(
        instructions: &[crate::instruction::Instruction],
        try_blocks: &[crate::instruction::TryBlockInfo],
    ) -> Self {
        if instructions.is_empty() {
            return CFG {
                blocks: vec![],
                entry: 0,
                offset_to_block: BTreeMap::new(),
            };
        }

        // Step 1: Identify leaders (block start offsets)
        let mut leaders = BTreeSet::new();
        leaders.insert(0u32); // First instruction is always a leader

        for (i, insn) in instructions.iter().enumerate() {
            let flags = abcd_isa::lookup(insn.opcode.0)
                .map(|info| info.flags())
                .unwrap_or(abcd_isa::OpcodeFlags::empty());

            // Jump targets are leaders
            if flags.contains(abcd_isa::OpcodeFlags::JUMP) {
                for op in &insn.operands {
                    if let crate::instruction::Operand::JumpOffset(off) = op {
                        let target = (insn.offset as i64 + *off as i64) as u32;
                        leaders.insert(target);
                    }
                }
                // Instruction after a jump is also a leader
                if i + 1 < instructions.len() {
                    leaders.insert(instructions[i + 1].offset);
                }
            }

            // Returns and throws end a block
            // But NOT conditional throws like throw.undefinedifhole* and throw.if*
            // which are TDZ/runtime checks that fall through in normal execution
            if flags.contains(abcd_isa::OpcodeFlags::RETURN)
                || (flags.contains(abcd_isa::OpcodeFlags::THROW)
                    && !is_conditional_throw(insn.opcode.mnemonic()))
            {
                if i + 1 < instructions.len() {
                    leaders.insert(instructions[i + 1].offset);
                }
            }
        }

        // Catch handler entries are leaders
        for tb in try_blocks {
            for cb in &tb.catch_blocks {
                leaders.insert(cb.handler_pc);
            }
        }

        // Step 2: Create blocks by splitting at leaders
        let leader_vec: Vec<u32> = leaders.iter().copied().collect();
        let mut offset_to_block = BTreeMap::new();
        let mut blocks = Vec::new();

        // Map instruction offset to instruction index
        let mut off_to_idx: BTreeMap<u32, usize> = BTreeMap::new();
        for (i, insn) in instructions.iter().enumerate() {
            off_to_idx.insert(insn.offset, i);
        }

        for (bi, &leader_off) in leader_vec.iter().enumerate() {
            let Some(&first_insn) = off_to_idx.get(&leader_off) else {
                continue;
            };

            // Block ends at the next leader or end of instructions
            let end_off = if bi + 1 < leader_vec.len() {
                leader_vec[bi + 1]
            } else {
                let last = instructions.last().unwrap();
                last.offset + last.size as u32
            };

            // Find last instruction index in this block
            let mut last_insn = first_insn;
            for j in first_insn..instructions.len() {
                if instructions[j].offset >= end_off {
                    break;
                }
                last_insn = j + 1;
            }

            let block_id = blocks.len();
            offset_to_block.insert(leader_off, block_id);

            let is_catch = try_blocks
                .iter()
                .any(|tb| tb.catch_blocks.iter().any(|cb| cb.handler_pc == leader_off));

            blocks.push(BasicBlock {
                id: block_id,
                start: leader_off,
                end: end_off,
                first_insn,
                last_insn,
                succs: vec![],
                preds: vec![],
                is_catch_handler: is_catch,
            });
        }

        // Step 3: Add edges
        for bi in 0..blocks.len() {
            let block = &blocks[bi];
            if block.first_insn >= block.last_insn {
                continue;
            }
            let last_idx = block.last_insn - 1;
            let last_insn = &instructions[last_idx];
            let flags = abcd_isa::lookup(last_insn.opcode.0)
                .map(|info| info.flags())
                .unwrap_or(abcd_isa::OpcodeFlags::empty());

            let is_jump = flags.contains(abcd_isa::OpcodeFlags::JUMP);
            let is_cond = flags.contains(abcd_isa::OpcodeFlags::CONDITIONAL);
            let is_return = flags.contains(abcd_isa::OpcodeFlags::RETURN);
            let is_throw = flags.contains(abcd_isa::OpcodeFlags::THROW)
                && !is_conditional_throw(last_insn.opcode.mnemonic());
            let is_unconditional_jump = is_jump && !is_cond;

            if is_return || is_throw {
                // No successors
            } else if is_unconditional_jump {
                // Only the jump target
                for op in &last_insn.operands {
                    if let crate::instruction::Operand::JumpOffset(off) = op {
                        let target = (last_insn.offset as i64 + *off as i64) as u32;
                        if let Some(&target_id) = offset_to_block.get(&target) {
                            blocks[bi].succs.push(target_id);
                        }
                    }
                }
            } else if is_cond {
                // Fall-through + jump target
                let fallthrough_id = if bi + 1 < blocks.len() {
                    Some(blocks[bi + 1].id)
                } else {
                    None
                };
                if let Some(ft) = fallthrough_id {
                    blocks[bi].succs.push(ft);
                }
                for op in &last_insn.operands {
                    if let crate::instruction::Operand::JumpOffset(off) = op {
                        let target = (last_insn.offset as i64 + *off as i64) as u32;
                        if let Some(&target_id) = offset_to_block.get(&target) {
                            if !blocks[bi].succs.contains(&target_id) {
                                blocks[bi].succs.push(target_id);
                            }
                        }
                    }
                }
            } else {
                // Fall-through
                let fallthrough_id = if bi + 1 < blocks.len() {
                    Some(blocks[bi + 1].id)
                } else {
                    None
                };
                if let Some(ft) = fallthrough_id {
                    blocks[bi].succs.push(ft);
                }
            }
        }

        // Build predecessor lists
        for bi in 0..blocks.len() {
            let succs = blocks[bi].succs.clone();
            for &s in &succs {
                if !blocks[s].preds.contains(&bi) {
                    blocks[s].preds.push(bi);
                }
            }
        }

        CFG {
            blocks,
            entry: 0,
            offset_to_block,
        }
    }
}
