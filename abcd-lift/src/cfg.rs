//! CFG construction from flat bytecode (ported from v0.1
//! `abcd-ir/src/lift/cfg.rs` — the proven leader-partition + exception
//! edge algorithm, unchanged).
//!
//! Scans a method's bytecode to identify basic block leaders, then
//! partitions the instruction stream into [`RawBlock`]s with
//! successor/predecessor edges.

use std::collections::{BTreeSet, HashMap};

use abcd_file::TryBlock;
use abcd_isa::Bytecode;

use crate::LiftError;

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

/// Result of CFG construction: ordered blocks + leader→block-index
/// mapping.
#[derive(Debug)]
pub struct RawCfg {
    /// Basic blocks in leader order.
    pub blocks: Vec<RawBlock>,
    /// Maps instruction index (leader) → index into `blocks`.
    pub leader_to_block: HashMap<usize, usize>,
}

/// Build a CFG from a decoded bytecode slice and `try_blocks`, validating
/// jump targets, terminal fall-throughs, and try/catch bounds (`R3-M3`).
pub fn build_cfg(bytecodes: &[Bytecode], try_blocks: &[TryBlock]) -> Result<RawCfg, LiftError> {
    if bytecodes.is_empty() {
        return Err(LiftError::EmptyBytecode);
    }

    let n = bytecodes.len();

    // Phase 1a: Validate control-flow bounds (R3-M3) and collect natural
    // leaders (entry, jump targets, post-jump/terminator fall-throughs, and
    // catch handler entries).
    let mut natural_leaders = BTreeSet::new();
    natural_leaders.insert(0);

    for (idx, bc) in bytecodes.iter().enumerate() {
        if bc.is_jump() {
            if let Some(target) = jump_target(bc) {
                if target >= n {
                    return Err(LiftError::JumpTargetOutOfBounds {
                        pc: idx,
                        target,
                        len: n,
                    });
                }
                natural_leaders.insert(target);
            }
            if is_conditional_jump(bc) && idx + 1 >= n {
                return Err(LiftError::FallthroughOutOfBounds { pc: idx, len: n });
            }
            if idx + 1 < n {
                natural_leaders.insert(idx + 1);
            }
        } else if bc.is_terminator() || bc.is_return_or_throw() {
            if idx + 1 < n {
                natural_leaders.insert(idx + 1);
            }
        } else if idx + 1 >= n {
            return Err(LiftError::FallthroughOutOfBounds { pc: idx, len: n });
        }
    }

    for try_block in try_blocks {
        let Some(try_end) = (try_block.start as usize)
            .checked_add(try_block.len as usize)
            .filter(|&end| end <= n)
        else {
            return Err(LiftError::TryRangeOutOfBounds {
                start: try_block.start,
                len: try_block.len,
                bytecode_len: n,
            });
        };
        let _ = try_end;
        for catch in &try_block.catches {
            let handler = catch.handler as usize;
            if handler >= n
                || handler
                    .checked_add(catch.len as usize)
                    .is_none_or(|end| end > n)
            {
                return Err(LiftError::CatchRangeOutOfBounds {
                    handler: catch.handler,
                    len: catch.len,
                    bytecode_len: n,
                });
            }
            natural_leaders.insert(handler);
        }
    }

    if try_blocks.is_empty() {
        return Ok(partition_and_wire(bytecodes, try_blocks, &natural_leaders));
    }

    // Phase 1b: Throwing-aware `try_start` / `try_end` leaders (R2-C2).
    let mut leaders = natural_leaders.clone();
    let mut nat_vec: Vec<usize> = natural_leaders.iter().copied().collect();
    nat_vec.push(n);

    for try_block in try_blocks {
        let try_start = (try_block.start as usize).min(n);
        let try_end = ((try_block.start + try_block.len) as usize).min(n);
        if 0 < try_start && try_start < n && !natural_leaders.contains(&try_start) {
            let upper = nat_vec.partition_point(|&x| x <= try_start);
            let seg_start = nat_vec[upper - 1];
            if bytecodes[seg_start..try_start]
                .iter()
                .any(|bc| !cannot_throw_ir(bc))
            {
                leaders.insert(try_start);
            }
        }
        if 0 < try_end && try_end < n && !natural_leaders.contains(&try_end) {
            let upper = nat_vec.partition_point(|&x| x <= try_end);
            let seg_end = nat_vec[upper];
            if bytecodes[try_end..seg_end]
                .iter()
                .any(|bc| !cannot_throw_ir(bc))
            {
                leaders.insert(try_end);
            }
        }
    }

    // Phase 1c: Handler-liveness-guided pre-write block splitting (R2-C1).
    let pre_cfg = partition_and_wire(bytecodes, try_blocks, &leaders);
    if split_protected_live_writes(bytecodes, &pre_cfg, &mut leaders) {
        Ok(partition_and_wire(bytecodes, try_blocks, &leaders))
    } else {
        Ok(pre_cfg)
    }
}

/// Phases 2–4: Partition `bytecodes` at `leaders` and wire normal + catch edges.
fn partition_and_wire(
    bytecodes: &[Bytecode],
    try_blocks: &[abcd_file::TryBlock],
    leaders: &BTreeSet<usize>,
) -> RawCfg {
    let sorted_leaders: Vec<usize> = leaders.iter().copied().collect();
    let mut leader_to_block: HashMap<usize, usize> = HashMap::with_capacity(sorted_leaders.len());
    let mut blocks: Vec<RawBlock> = Vec::with_capacity(sorted_leaders.len());

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

    for block in &mut blocks {
        let block_end = block.end;
        if block_end == 0 {
            continue;
        }
        let last_bc = &bytecodes[block_end - 1];

        if last_bc.is_jump() {
            if let Some(target) = jump_target(last_bc)
                && let Some(&target_bi) = leader_to_block.get(&target)
            {
                block.succs.push(target_bi);
            }
            if is_conditional_jump(last_bc)
                && block_end < bytecodes.len()
                && let Some(&fall_bi) = leader_to_block.get(&block_end)
            {
                block.succs.push(fall_bi);
            }
        } else if !(last_bc.is_terminator() || last_bc.is_return_or_throw())
            && block_end < bytecodes.len()
            && let Some(&fall_bi) = leader_to_block.get(&block_end)
        {
            block.succs.push(fall_bi);
        }
    }

    for try_block in try_blocks {
        let try_start = try_block.start as usize;
        let try_end = try_start.saturating_add(try_block.len as usize);
        let catch_targets: Vec<usize> = try_block
            .catches
            .iter()
            .filter_map(|c| leader_to_block.get(&(c.handler as usize)).copied())
            .collect();
        if catch_targets.is_empty() {
            continue;
        }

        // `blocks` partitions `[0, bytecodes.len())` in strictly ascending
        // `(start, end)` order, so `[first_bi..end_bi)` is the exact contiguous
        // slice satisfying `block.start < try_end && block.end > try_start` (`#103`).
        let first_bi = blocks.partition_point(|b| b.end <= try_start);
        let end_bi = blocks.partition_point(|b| b.start < try_end);
        if first_bi < end_bi {
            for block in &mut blocks[first_bi..end_bi] {
                for &ct in &catch_targets {
                    if !block.catch_succs.contains(&ct) {
                        block.catch_succs.push(ct);
                    }
                }
            }
        }
    }

    RawCfg {
        blocks,
        leader_to_block,
    }
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

/// Conservative check returning `true` ONLY for bytecodes guaranteed to emit
/// zero `may_throw == true` IR ops (`R2-C1`, synchronized 1-for-1 with
/// `abcd_ir::Op::effects`).
fn is_guaranteed_non_throwing(bc: &Bytecode) -> bool {
    use Bytecode::*;
    matches!(
        bc,
        Nop | Debugger
            | Mov(..)
            | Lda(..)
            | Sta(..)
            | Setgeneratorstate(..)
            | CallruntimeNotifyconcurrentresult
            | Ldundefined
            | Ldnull
            | Ldtrue
            | Ldfalse
            | Ldhole
            | Ldnan
            | Ldinfinity
            | Ldsymbol
            | Ldai(..)
            | Fldai(..)
            | LdaStr(..)
            | Ldbigint(..)
            | Ldthis
            | Ldfunction
            | Ldnewtarget
            | Ldglobal
            | DeprecatedLdlexenv
            | Istrue
            | Isfalse
            | CallruntimeIstrue(..)
            | CallruntimeIsfalse(..)
            | Typeof(..)
            | Stricteq(..)
            | Strictnoteq(..)
            | Createemptyobject
            | Createobjectwithbuffer(..)
            | Createemptyarray(..)
            | Createarraywithbuffer(..)
            | DeprecatedCreatearraywithbuffer(..)
            | DeprecatedCreateobjectwithbuffer(..)
            | DeprecatedCreateobjecthavingmethod(..)
            | Copyrestargs(..)
            | WideCopyrestargs(..)
            | Getunmappedargs
            | Definefunc(..)
            | Createiterresultobj(..)
            | Creategeneratorobj(..)
            | Createasyncgeneratorobj(..)
            | Getresumemode
            | DeprecatedGetresumemode(..)
            | Asyncfunctionenter
            | Asyncfunctionresolve(..)
            | Asyncfunctionreject(..)
            | Asyncgeneratorreject(..)
            | DeprecatedAsyncfunctionresolve(..)
            | DeprecatedAsyncfunctionreject(..)
            | DeprecatedAsyncgeneratorreject(..)
            | Newlexenv(..)
            | WideNewlexenv(..)
            | Newlexenvwithname(..)
            | WideNewlexenvwithname(..)
            | CallruntimeNewsendableenv(..)
            | CallruntimeWidenewsendableenv(..)
            | Poplexenv
            | DeprecatedPoplexenv
            | Ldlexvar(..)
            | WideLdlexvar(..)
            | Stlexvar(..)
            | WideStlexvar(..)
            | CallruntimeLdsendablevar(..)
            | CallruntimeWideldsendablevar(..)
            | CallruntimeStsendablevar(..)
            | CallruntimeWidestsendablevar(..)
            | WideLdpatchvar(..)
            | WideStpatchvar(..)
            | DeprecatedStlexvar(..)
            | CallruntimeCreateprivateproperty(..)
            | Ldlocalmodulevar(..)
            | WideLdlocalmodulevar(..)
            | CallruntimeLdsendablelocalmodulevar(..)
            | CallruntimeWideldsendablelocalmodulevar(..)
            | CallruntimeLdsendableclass(..)
            | Stmodulevar(..)
            | WideStmodulevar(..)
            | DeprecatedStmodulevar(..)
    )
}

/// Bytecodes guaranteed to emit zero `may_throw == true` IR ops, including
/// non-throwing control-flow transfers (`R2-C1` / `R2-C2`).
pub(crate) fn cannot_throw_ir(bc: &Bytecode) -> bool {
    use Bytecode::*;
    is_guaranteed_non_throwing(bc)
        || matches!(bc, Jmp(_) | Jeqz(_) | Jnez(_) | Return | Returnundefined)
}

#[derive(Clone, Default)]
struct RegBitSet {
    words: Vec<u64>,
}

impl RegBitSet {
    fn with_words(num_words: usize) -> Self {
        Self {
            words: vec![0; num_words],
        }
    }

    #[inline]
    fn insert(&mut self, reg: u16) {
        let w = (reg as usize) >> 6;
        if w >= self.words.len() {
            self.words.resize(w + 1, 0);
        }
        self.words[w] |= 1u64 << (reg & 63);
    }

    #[inline]
    fn contains(&self, reg: u16) -> bool {
        let w = (reg as usize) >> 6;
        self.words
            .get(w)
            .is_some_and(|&bits| (bits & (1u64 << (reg & 63))) != 0)
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.words.iter().all(|&w| w == 0)
    }

    fn union_with(&mut self, other: &Self) {
        for (dst, &src) in self.words.iter_mut().zip(&other.words) {
            *dst |= src;
        }
    }
}

/// Compute backward virtual-register liveness over `pre_cfg` (`succs ∪ catch_succs`)
/// and insert pre-write split leaders into `leaders` ONLY when the written
/// register is live-in at at least one covering catch handler (`R2-C1`).
fn split_protected_live_writes(
    bytecodes: &[Bytecode],
    pre_cfg: &RawCfg,
    leaders: &mut BTreeSet<usize>,
) -> bool {
    let num_blocks = pre_cfg.blocks.len();
    if !pre_cfg.blocks.iter().any(|b| !b.catch_succs.is_empty()) {
        return false;
    }

    let mut use_gen = vec![RegBitSet::default(); num_blocks];
    let mut kill = vec![RegBitSet::default(); num_blocks];
    let mut pre_throw_kill = vec![RegBitSet::default(); num_blocks];

    for (bi, pb) in pre_cfg.blocks.iter().enumerate() {
        let mut seen_throw = false;
        for bc in &bytecodes[pb.start..pb.end] {
            for_each_reg_read(bc, |r| {
                if !kill[bi].contains(r) {
                    use_gen[bi].insert(r);
                }
            });
            if !cannot_throw_ir(bc) {
                seen_throw = true;
            }
            if let Some(w) = reg_written(bc) {
                kill[bi].insert(w);
                if !seen_throw {
                    pre_throw_kill[bi].insert(w);
                }
            }
        }
    }

    let num_words = use_gen
        .iter()
        .chain(&kill)
        .map(|s| s.words.len())
        .max()
        .unwrap_or(0);
    if num_words == 0 {
        return false;
    }
    for s in use_gen
        .iter_mut()
        .chain(&mut kill)
        .chain(&mut pre_throw_kill)
    {
        s.words.resize(num_words, 0);
    }

    let mut live_in = vec![RegBitSet::with_words(num_words); num_blocks];
    let mut norm_out = vec![0u64; num_words];
    let mut exc_out = vec![0u64; num_words];
    let mut changed = true;
    while changed {
        changed = false;
        for b in (0..num_blocks).rev() {
            norm_out.fill(0);
            for &s in &pre_cfg.blocks[b].succs {
                for (dst, &src) in norm_out.iter_mut().zip(&live_in[s].words) {
                    *dst |= src;
                }
            }
            exc_out.fill(0);
            for &c in &pre_cfg.blocks[b].catch_succs {
                for (dst, &src) in exc_out.iter_mut().zip(&live_in[c].words) {
                    *dst |= src;
                }
            }
            let gen_w = &use_gen[b].words;
            let kill_w = &kill[b].words;
            let pre_kill_w = &pre_throw_kill[b].words;
            let li_w = &mut live_in[b].words;
            for w in 0..num_words {
                let next = gen_w[w] | (norm_out[w] & !kill_w[w]) | (exc_out[w] & !pre_kill_w[w]);
                if next != li_w[w] {
                    li_w[w] = next;
                    changed = true;
                }
            }
        }
    }

    let mut added_any = false;
    let mut handler_live = RegBitSet::with_words(num_words);
    for pb in &pre_cfg.blocks {
        if pb.catch_succs.is_empty() {
            continue;
        }
        handler_live.words.fill(0);
        for &h in &pb.catch_succs {
            handler_live.union_with(&live_in[h]);
        }
        if handler_live.is_empty() {
            continue;
        }
        let mut seen_may_throw = false;
        for (idx, bc) in bytecodes[pb.start..pb.end]
            .iter()
            .enumerate()
            .map(|(off, bc)| (pb.start + off, bc))
        {
            if let Some(w) = reg_written(bc)
                && seen_may_throw
                && handler_live.contains(w)
            {
                if leaders.insert(idx) {
                    added_any = true;
                }
                seen_may_throw = false;
            }
            if !cannot_throw_ir(bc) {
                seen_may_throw = true;
            }
        }
    }
    added_any
}

#[inline]
fn reg_written(bc: &Bytecode) -> Option<u16> {
    match bc {
        Bytecode::Sta(r) => Some(r.0),
        Bytecode::Mov(dst, _) => Some(dst.0),
        _ => None,
    }
}

fn for_each_reg_read(bc: &Bytecode, mut f: impl FnMut(u16)) {
    use Bytecode::*;
    match bc {
        Sta(_) => {}
        Mov(_, src) => f(src.0),
        Createobjectwithexcludedkeys(num, obj_reg, start_reg)
        | WideCreateobjectwithexcludedkeys(num, obj_reg, start_reg) => {
            f(obj_reg.0);
            let count = (num.0 as u16).saturating_add(1);
            for i in 0..count {
                if let Some(r) = start_reg.0.checked_add(i) {
                    f(r);
                }
            }
        }
        Callrange(_, argc, start)
        | WideCallrange(argc, start)
        | Supercallthisrange(_, argc, start)
        | WideSupercallthisrange(argc, start)
        | Supercallarrowrange(_, argc, start)
        | WideSupercallarrowrange(argc, start)
        | Newobjrange(_, argc, start)
        | WideNewobjrange(argc, start) => {
            let count = argc.0 as u16;
            for i in 0..count {
                if let Some(r) = start.0.checked_add(i) {
                    f(r);
                }
            }
        }
        DeprecatedCallrange(argc, start) => {
            if let Ok(n) = u16::try_from(argc.0) {
                let count = n.saturating_add(1);
                for i in 0..count {
                    if let Some(r) = start.0.checked_add(i) {
                        f(r);
                    }
                }
            }
        }
        Callthisrange(_, argc, start)
        | WideCallthisrange(argc, start)
        | Callthisrangewithname(_, argc, _, start)
        | WideCallthisrangewithname(argc, _, start)
        | DeprecatedCallthisrange(argc, start) => {
            let count = (argc.0 as u16).saturating_add(2);
            for i in 0..count {
                if let Some(r) = start.0.checked_add(i) {
                    f(r);
                }
            }
        }
        _ => {
            for op in bc.operands() {
                if let abcd_isa::Operand::Reg(r) = op {
                    f(r);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
