//! CFG construction from flat bytecode (ported from v0.1
//! `abcd-ir/src/lift/cfg.rs` — the proven leader-partition + exception
//! edge algorithm, unchanged).
//!
//! Scans a method's bytecode to identify basic block leaders, then
//! partitions the instruction stream into [`RawBlock`]s with
//! successor/predecessor edges.

use std::collections::{BTreeSet, HashMap};

use abcd_file::MethodBody;
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

/// Build a CFG from a method body's bytecodes and try-blocks, validating
/// jump targets, terminal fall-throughs, and try/catch bounds (`R3-M3`).
pub fn build_cfg(body: &MethodBody) -> Result<RawCfg, LiftError> {
    let bytecodes = &body.bytecodes;
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

    for try_block in &body.try_blocks {
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

    if body.try_blocks.is_empty() {
        return Ok(partition_and_wire(
            bytecodes,
            &body.try_blocks,
            &natural_leaders,
        ));
    }

    // Phase 1b: Throwing-aware `try_start` / `try_end` leaders (R2-C2).
    let mut leaders = natural_leaders.clone();
    let mut nat_vec: Vec<usize> = natural_leaders.iter().copied().collect();
    nat_vec.push(n);

    for try_block in &body.try_blocks {
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
    let pre_cfg = partition_and_wire(bytecodes, &body.try_blocks, &leaders);
    if split_protected_live_writes(bytecodes, &pre_cfg, &mut leaders) {
        Ok(partition_and_wire(bytecodes, &body.try_blocks, &leaders))
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
        let try_end = (try_block.start + try_block.len) as usize;
        let catch_targets: Vec<usize> = try_block
            .catches
            .iter()
            .filter_map(|c| leader_to_block.get(&(c.handler as usize)).copied())
            .collect();

        for block in &mut blocks {
            if block.start < try_end && block.end > try_start {
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
mod tests {
    use super::*;
    use abcd_file::{CatchBlock, TryBlock};
    use abcd_isa::{Imm, Label, Reg};

    fn make_body(bytecodes: Vec<Bytecode>) -> MethodBody {
        MethodBody {
            entities: Default::default(),
            num_vregs: 0,
            num_args: 0,
            bytecodes,
            try_blocks: Vec::new(),
            ic_size: None,
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
        let body = MethodBody {
            entities: Default::default(),
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
                    type_class: None,
                    handler: 2,
                    len: 2,
                }],
            }],
            ic_size: None,
        };
        let cfg = build_cfg(&body).unwrap();
        let b0 = &cfg.blocks[0];
        assert!(!b0.catch_succs.is_empty());
    }

    #[test]
    fn catchall_rethrow_handler_does_not_split_protected_writes() {
        // Synthetic `.catchall` (`sta v0; poplexenv; lda v0; throw`) has zero
        // live-in virtual registers, so `Sta` writes inside the try range must
        // NOT shatter the protected block.
        let body = MethodBody {
            entities: Default::default(),
            num_vregs: 3,
            num_args: 0,
            bytecodes: vec![
                Bytecode::Callarg0(Imm(0)), // 0 (try)
                Bytecode::Sta(Reg(1)),      // 1 (try)
                Bytecode::Callarg0(Imm(1)), // 2 (try)
                Bytecode::Sta(Reg(2)),      // 3 (try)
                Bytecode::Returnundefined,  // 4
                Bytecode::Sta(Reg(0)),      // 5 (catchall handler: kills v0)
                Bytecode::Poplexenv,        // 6
                Bytecode::Lda(Reg(0)),      // 7
                Bytecode::Throw,            // 8
            ],
            try_blocks: vec![TryBlock {
                start: 0,
                len: 4,
                catches: vec![CatchBlock {
                    type_class: None,
                    handler: 5,
                    len: 4,
                }],
            }],
            ic_size: None,
        };
        let cfg = build_cfg(&body).unwrap();
        assert_eq!(cfg.blocks.len(), 2, "protected body stays a single block");
        assert_eq!((cfg.blocks[0].start, cfg.blocks[0].end), (0, 5));
    }

    #[test]
    fn try_end_pure_jmp_backedge_stays_in_protected_block() {
        // `[try_start..try_end)` followed immediately by `jmp loop_header`
        // keeps the pure `jmp` tail attached to the protected block instead of
        // splitting an unprotected back-edge block.
        let body = MethodBody {
            entities: Default::default(),
            num_vregs: 1,
            num_args: 0,
            bytecodes: vec![
                Bytecode::Callarg0(Imm(0)), // 0 (loop_header, try_start)
                Bytecode::Jmp(Label(0)),    // 1 (try_end = 1, pure back-edge)
                Bytecode::Returnundefined,  // 2 (catch handler)
            ],
            try_blocks: vec![TryBlock {
                start: 0,
                len: 1,
                catches: vec![CatchBlock {
                    type_class: None,
                    handler: 2,
                    len: 1,
                }],
            }],
            ic_size: None,
        };
        let cfg = build_cfg(&body).unwrap();
        assert_eq!(cfg.blocks.len(), 2);
        assert_eq!((cfg.blocks[0].start, cfg.blocks[0].end), (0, 2));
        assert_eq!(cfg.blocks[0].succs, vec![0]);
        assert_eq!(cfg.blocks[0].catch_succs, vec![1]);
    }

    #[test]
    fn non_throwing_async_and_generator_init_does_not_split_before_sta() {
        // `asyncfunctionenter; sta v0` and `createasyncgeneratorobj; sta v1`
        // emit `may_throw: false` IR ops, so they must NOT split before `sta`
        // even when `v0`/`v1` are read in the reject catch handler.
        let body = MethodBody {
            entities: Default::default(),
            num_vregs: 3,
            num_args: 0,
            bytecodes: vec![
                Bytecode::Asyncfunctionenter,              // 0 (try, non-throwing)
                Bytecode::Sta(Reg(0)),                     // 1 (try, must NOT split)
                Bytecode::Createasyncgeneratorobj(Reg(2)), // 2 (try, non-throwing)
                Bytecode::Sta(Reg(1)),                     // 3 (try, must NOT split)
                Bytecode::Callarg0(Imm(0)),                // 4 (try, may_throw)
                Bytecode::Return,                          // 5
                Bytecode::Asyncfunctionreject(Reg(0)),     // 6 (handler: reads v0, v1)
                Bytecode::Asyncgeneratorreject(Reg(1)),    // 7
                Bytecode::Return,                          // 8
            ],
            try_blocks: vec![TryBlock {
                start: 0,
                len: 5,
                catches: vec![CatchBlock {
                    type_class: None,
                    handler: 6,
                    len: 3,
                }],
            }],
            ic_size: None,
        };
        let cfg = build_cfg(&body).unwrap();
        assert_eq!(
            cfg.blocks.len(),
            2,
            "no spurious split before non-throwing init `sta`"
        );
        assert_eq!((cfg.blocks[0].start, cfg.blocks[0].end), (0, 6));
    }

    #[test]
    fn try_end_mov_tail_splits_iff_written_reg_is_handler_live() {
        // Handler reads `v2` (`live_in = {v2}`), while `v3` is dead at handler.
        let make = |written: u16| MethodBody {
            entities: Default::default(),
            num_vregs: 4,
            num_args: 0,
            bytecodes: vec![
                Bytecode::Callarg0(Imm(0)),          // 0 (try_start = 0, may_throw)
                Bytecode::Mov(Reg(written), Reg(1)), // 1 (try_end = 1: post-try tail)
                Bytecode::Jmp(Label(5)),             // 2
                Bytecode::Lda(Reg(2)),               // 3 (catch handler: reads v2)
                Bytecode::Return,                    // 4
                Bytecode::Returnundefined,           // 5 (join)
            ],
            try_blocks: vec![TryBlock {
                start: 0,
                len: 1,
                catches: vec![CatchBlock {
                    type_class: None,
                    handler: 3,
                    len: 2,
                }],
            }],
            ic_size: None,
        };

        // Dead `v3` at `try_end`: stays attached to `blocks[0]` (`[0..3)`).
        let dead_cfg = build_cfg(&make(3)).unwrap();
        assert_eq!(dead_cfg.blocks.len(), 3);
        assert_eq!((dead_cfg.blocks[0].start, dead_cfg.blocks[0].end), (0, 3));

        // Handler-live `v2` at `try_end`: Phase 1c splits `[1..3)` out of `blocks[0]`,
        // and `[1..3)` (`>= try_end`) has empty `catch_succs`.
        let live_cfg = build_cfg(&make(2)).unwrap();
        assert_eq!(live_cfg.blocks.len(), 4);
        assert_eq!((live_cfg.blocks[0].start, live_cfg.blocks[0].end), (0, 1));
        assert_eq!((live_cfg.blocks[1].start, live_cfg.blocks[1].end), (1, 3));
        assert!(live_cfg.blocks[1].catch_succs.is_empty());
    }

    /// Compiler-enforced exhaustive index over all 247 [`Bytecode`] variants
    /// (zero `_` wildcard arm — adding any new `Bytecode` variant forces updating
    /// `exhaustive_bytecode_cannot_throw_ir_matches_op_effects_may_throw`).
    fn bytecode_variant_index(bc: &Bytecode) -> usize {
        use Bytecode::*;
        match bc {
            Ldundefined => 0,
            Ldnull => 1,
            Ldtrue => 2,
            Ldfalse => 3,
            Createemptyobject => 4,
            Createemptyarray(..) => 5,
            Createarraywithbuffer(..) => 6,
            Createobjectwithbuffer(..) => 7,
            Newobjrange(..) => 8,
            Newlexenv(..) => 9,
            Add2(..) => 10,
            Sub2(..) => 11,
            Mul2(..) => 12,
            Div2(..) => 13,
            Mod2(..) => 14,
            Eq(..) => 15,
            Noteq(..) => 16,
            Less(..) => 17,
            Lesseq(..) => 18,
            Greater(..) => 19,
            Greatereq(..) => 20,
            Shl2(..) => 21,
            Shr2(..) => 22,
            Ashr2(..) => 23,
            And2(..) => 24,
            Or2(..) => 25,
            Xor2(..) => 26,
            Exp(..) => 27,
            Typeof(..) => 28,
            Tonumber(..) => 29,
            Tonumeric(..) => 30,
            Neg(..) => 31,
            Not(..) => 32,
            Inc(..) => 33,
            Dec(..) => 34,
            Istrue => 35,
            Isfalse => 36,
            Isin(..) => 37,
            Instanceof(..) => 38,
            Strictnoteq(..) => 39,
            Stricteq(..) => 40,
            Callarg0(..) => 41,
            Callarg1(..) => 42,
            Callargs2(..) => 43,
            Callargs3(..) => 44,
            Callthis0(..) => 45,
            Callthis1(..) => 46,
            Callthis2(..) => 47,
            Callthis3(..) => 48,
            Callthisrange(..) => 49,
            Supercallthisrange(..) => 50,
            Definefunc(..) => 51,
            Definemethod(..) => 52,
            Defineclasswithbuffer(..) => 53,
            Getnextpropname(..) => 54,
            Ldobjbyvalue(..) => 55,
            Stobjbyvalue(..) => 56,
            Ldsuperbyvalue(..) => 57,
            Ldobjbyindex(..) => 58,
            Stobjbyindex(..) => 59,
            Ldlexvar(..) => 60,
            Stlexvar(..) => 61,
            LdaStr(..) => 62,
            Tryldglobalbyname(..) => 63,
            Trystglobalbyname(..) => 64,
            Ldglobalvar(..) => 65,
            Ldobjbyname(..) => 66,
            Stobjbyname(..) => 67,
            Mov(..) => 68,
            Ldsuperbyname(..) => 69,
            Stconsttoglobalrecord(..) => 70,
            Sttoglobalrecord(..) => 71,
            Ldthisbyname(..) => 72,
            Stthisbyname(..) => 73,
            Ldthisbyvalue(..) => 74,
            Stthisbyvalue(..) => 75,
            Jmp(..) => 76,
            Jeqz(..) => 77,
            Jnez(..) => 78,
            Jstricteqz(..) => 79,
            Jnstricteqz(..) => 80,
            Jeqnull(..) => 81,
            Jnenull(..) => 82,
            Jstricteqnull(..) => 83,
            Jnstricteqnull(..) => 84,
            Jequndefined(..) => 85,
            Jneundefined(..) => 86,
            Jstrictequndefined(..) => 87,
            Jnstrictequndefined(..) => 88,
            Jeq(..) => 89,
            Jne(..) => 90,
            Jstricteq(..) => 91,
            Jnstricteq(..) => 92,
            Lda(..) => 93,
            Sta(..) => 94,
            Ldai(..) => 95,
            Fldai(..) => 96,
            Return => 97,
            Returnundefined => 98,
            Getpropiterator => 99,
            Getiterator(..) => 100,
            Closeiterator(..) => 101,
            Poplexenv => 102,
            Ldnan => 103,
            Ldinfinity => 104,
            Getunmappedargs => 105,
            Ldglobal => 106,
            Ldnewtarget => 107,
            Ldthis => 108,
            Ldhole => 109,
            Createregexpwithliteral(..) => 110,
            Callrange(..) => 111,
            Gettemplateobject(..) => 112,
            Setobjectwithproto(..) => 113,
            Stownbyvalue(..) => 114,
            Stownbyindex(..) => 115,
            Stownbyname(..) => 116,
            Getmodulenamespace(..) => 117,
            Stmodulevar(..) => 118,
            Ldlocalmodulevar(..) => 119,
            Ldexternalmodulevar(..) => 120,
            Stglobalvar(..) => 121,
            Stownbynamewithnameset(..) => 122,
            Asyncgeneratorreject(..) => 123,
            Stownbyvaluewithnameset(..) => 124,
            Ldsymbol => 125,
            Asyncfunctionenter => 126,
            Ldfunction => 127,
            Debugger => 128,
            Creategeneratorobj(..) => 129,
            Createiterresultobj(..) => 130,
            Createobjectwithexcludedkeys(..) => 131,
            Newobjapply(..) => 132,
            Newlexenvwithname(..) => 133,
            Createasyncgeneratorobj(..) => 134,
            Asyncgeneratorresolve(..) => 135,
            Supercallspread(..) => 136,
            Apply(..) => 137,
            Supercallarrowrange(..) => 138,
            Definegettersetterbyvalue(..) => 139,
            Dynamicimport => 140,
            Resumegenerator => 141,
            Getresumemode => 142,
            Delobjprop(..) => 143,
            Suspendgenerator(..) => 144,
            Asyncfunctionawaituncaught(..) => 145,
            Copydataproperties(..) => 146,
            Starrayspread(..) => 147,
            Stsuperbyvalue(..) => 148,
            Asyncfunctionresolve(..) => 149,
            Asyncfunctionreject(..) => 150,
            Copyrestargs(..) => 151,
            Stsuperbyname(..) => 152,
            Ldbigint(..) => 153,
            Nop => 154,
            Setgeneratorstate(..) => 155,
            Getasynciterator(..) => 156,
            Ldprivateproperty(..) => 157,
            Stprivateproperty(..) => 158,
            Testin(..) => 159,
            Definefieldbyname(..) => 160,
            Definepropertybyname(..) => 161,
            Callthis0withname(..) => 162,
            Callthis1withname(..) => 163,
            Callthis2withname(..) => 164,
            Callthis3withname(..) => 165,
            Callthisrangewithname(..) => 166,
            CallruntimeNotifyconcurrentresult => 167,
            DeprecatedLdlexenv => 168,
            WideCreateobjectwithexcludedkeys(..) => 169,
            Throw => 170,
            CallruntimeDefinefieldbyvalue(..) => 171,
            DeprecatedPoplexenv => 172,
            WideNewobjrange(..) => 173,
            ThrowNotexists => 174,
            CallruntimeDefinefieldbyindex(..) => 175,
            DeprecatedGetiteratornext(..) => 176,
            WideNewlexenv(..) => 177,
            ThrowPatternnoncoercible => 178,
            CallruntimeTopropertykey => 179,
            DeprecatedCreatearraywithbuffer(..) => 180,
            WideNewlexenvwithname(..) => 181,
            ThrowDeletesuperproperty => 182,
            CallruntimeCreateprivateproperty(..) => 183,
            DeprecatedCreateobjectwithbuffer(..) => 184,
            WideCallrange(..) => 185,
            ThrowConstassignment(..) => 186,
            CallruntimeDefineprivateproperty(..) => 187,
            DeprecatedTonumber(..) => 188,
            WideCallthisrange(..) => 189,
            ThrowIfnotobject(..) => 190,
            CallruntimeCallinit(..) => 191,
            DeprecatedTonumeric(..) => 192,
            WideSupercallthisrange(..) => 193,
            ThrowUndefinedifhole(..) => 194,
            CallruntimeDefinesendableclass(..) => 195,
            DeprecatedNeg(..) => 196,
            WideSupercallarrowrange(..) => 197,
            ThrowIfsupernotcorrectcall(..) => 198,
            CallruntimeLdsendableclass(..) => 199,
            DeprecatedNot(..) => 200,
            WideLdobjbyindex(..) => 201,
            CallruntimeLdsendableexternalmodulevar(..) => 202,
            DeprecatedInc(..) => 203,
            WideStobjbyindex(..) => 204,
            ThrowUndefinedifholewithname(..) => 205,
            CallruntimeWideldsendableexternalmodulevar(..) => 206,
            DeprecatedDec(..) => 207,
            WideStownbyindex(..) => 208,
            CallruntimeNewsendableenv(..) => 209,
            DeprecatedCallarg0(..) => 210,
            WideCopyrestargs(..) => 211,
            CallruntimeWidenewsendableenv(..) => 212,
            DeprecatedCallarg1(..) => 213,
            WideLdlexvar(..) => 214,
            CallruntimeStsendablevar(..) => 215,
            DeprecatedCallargs2(..) => 216,
            WideStlexvar(..) => 217,
            DeprecatedCallargs3(..) => 218,
            WideGetmodulenamespace(..) => 219,
            CallruntimeWidestsendablevar(..) => 220,
            DeprecatedCallrange(..) => 221,
            WideStmodulevar(..) => 222,
            CallruntimeLdsendablevar(..) => 223,
            DeprecatedCallspread(..) => 224,
            WideLdlocalmodulevar(..) => 225,
            DeprecatedCallthisrange(..) => 226,
            WideLdexternalmodulevar(..) => 227,
            CallruntimeWideldsendablevar(..) => 228,
            DeprecatedDefineclasswithbuffer(..) => 229,
            WideLdpatchvar(..) => 230,
            CallruntimeIstrue(..) => 231,
            DeprecatedResumegenerator(..) => 232,
            WideStpatchvar(..) => 233,
            CallruntimeIsfalse(..) => 234,
            DeprecatedGetresumemode(..) => 235,
            WideCallthisrangewithname(..) => 236,
            CallruntimeLdlazymodulevar(..) => 237,
            DeprecatedGettemplateobject(..) => 238,
            CallruntimeWideldlazymodulevar(..) => 239,
            DeprecatedDelobjprop(..) => 240,
            CallruntimeLdlazysendablemodulevar(..) => 241,
            DeprecatedSuspendgenerator(..) => 242,
            CallruntimeWideldlazysendablemodulevar(..) => 243,
            DeprecatedAsyncfunctionawaituncaught(..) => 244,
            CallruntimeSupercallforwardallargs(..) => 245,
            DeprecatedCopydataproperties(..) => 246,
            CallruntimeLdsendablelocalmodulevar(..) => 247,
            DeprecatedSetobjectwithproto(..) => 248,
            CallruntimeWideldsendablelocalmodulevar(..) => 249,
            DeprecatedLdobjbyvalue(..) => 250,
            DeprecatedLdsuperbyvalue(..) => 251,
            DeprecatedLdobjbyindex(..) => 252,
            DeprecatedAsyncfunctionresolve(..) => 253,
            DeprecatedAsyncfunctionreject(..) => 254,
            DeprecatedStlexvar(..) => 255,
            DeprecatedGetmodulenamespace(..) => 256,
            DeprecatedStmodulevar(..) => 257,
            DeprecatedLdobjbyname(..) => 258,
            DeprecatedLdsuperbyname(..) => 259,
            DeprecatedLdmodulevar(..) => 260,
            DeprecatedStconsttoglobalrecord(..) => 261,
            DeprecatedStlettoglobalrecord(..) => 262,
            DeprecatedStclasstoglobalrecord(..) => 263,
            DeprecatedLdhomeobject => 264,
            DeprecatedCreateobjecthavingmethod(..) => 265,
            DeprecatedDynamicimport(..) => 266,
            DeprecatedAsyncgeneratorreject(..) => 267,
        }
    }

    #[test]
    fn exhaustive_bytecode_cannot_throw_ir_matches_op_effects_may_throw() {
        use Bytecode::*;
        use abcd_file::{
            AccessFlags, Class, EntityRef, File, FileType, FunctionKind as FileFunctionKind,
            LiteralArray, LiteralArrayIdx, LiteralValue, Method, MethodIdx,
            SourceLang as FileSourceLang, StringPool,
        };
        use abcd_isa::{EntityId, EntityKind, Version};

        const TOTAL_VARIANTS: usize = 268;
        let eid = EntityId(0);
        let r0 = Reg(0);
        let r1 = Reg(1);
        let r2 = Reg(2);
        let r3 = Reg(3);
        let i0 = Imm(0);
        let i1 = Imm(1);
        let lbl = Label(1);

        let samples: Vec<Bytecode> = vec![
            Ldundefined,
            Ldnull,
            Ldtrue,
            Ldfalse,
            Createemptyobject,
            Createemptyarray(i0),
            Createarraywithbuffer(i0, eid),
            Createobjectwithbuffer(i0, eid),
            Newobjrange(i0, i1, r0),
            Newlexenv(i1),
            Add2(i0, r0),
            Sub2(i0, r0),
            Mul2(i0, r0),
            Div2(i0, r0),
            Mod2(i0, r0),
            Eq(i0, r0),
            Noteq(i0, r0),
            Less(i0, r0),
            Lesseq(i0, r0),
            Greater(i0, r0),
            Greatereq(i0, r0),
            Shl2(i0, r0),
            Shr2(i0, r0),
            Ashr2(i0, r0),
            And2(i0, r0),
            Or2(i0, r0),
            Xor2(i0, r0),
            Exp(i0, r0),
            Typeof(i0),
            Tonumber(i0),
            Tonumeric(i0),
            Neg(i0),
            Not(i0),
            Inc(i0),
            Dec(i0),
            Istrue,
            Isfalse,
            Isin(i0, r0),
            Instanceof(i0, r0),
            Strictnoteq(i0, r0),
            Stricteq(i0, r0),
            Callarg0(i0),
            Callarg1(i0, r0),
            Callargs2(i0, r0, r1),
            Callargs3(i0, r0, r1, r2),
            Callthis0(i0, r0),
            Callthis1(i0, r0, r1),
            Callthis2(i0, r0, r1, r2),
            Callthis3(i0, r0, r1, r2, r3),
            Callthisrange(i0, i1, r0),
            Supercallthisrange(i0, i1, r0),
            Definefunc(i0, eid, i0),
            Definemethod(i0, eid, i0),
            Defineclasswithbuffer(i0, eid, eid, i0, r0),
            Getnextpropname(r0),
            Ldobjbyvalue(i0, r0),
            Stobjbyvalue(i0, r0, r1),
            Ldsuperbyvalue(i0, r0),
            Ldobjbyindex(i0, i1),
            Stobjbyindex(i0, r0, i1),
            Ldlexvar(i0, i0),
            Stlexvar(i0, i0),
            LdaStr(eid),
            Tryldglobalbyname(i0, eid),
            Trystglobalbyname(i0, eid),
            Ldglobalvar(i0, eid),
            Ldobjbyname(i0, eid),
            Stobjbyname(i0, eid, r0),
            Mov(r0, r1),
            Ldsuperbyname(i0, eid),
            Stconsttoglobalrecord(i0, eid),
            Sttoglobalrecord(i0, eid),
            Ldthisbyname(i0, eid),
            Stthisbyname(i0, eid),
            Ldthisbyvalue(i0),
            Stthisbyvalue(i0, r0),
            Jmp(lbl),
            Jeqz(lbl),
            Jnez(lbl),
            Jstricteqz(lbl),
            Jnstricteqz(lbl),
            Jeqnull(lbl),
            Jnenull(lbl),
            Jstricteqnull(lbl),
            Jnstricteqnull(lbl),
            Jequndefined(lbl),
            Jneundefined(lbl),
            Jstrictequndefined(lbl),
            Jnstrictequndefined(lbl),
            Jeq(r0, lbl),
            Jne(r0, lbl),
            Jstricteq(r0, lbl),
            Jnstricteq(r0, lbl),
            Lda(r0),
            Sta(r0),
            Ldai(i1),
            Fldai(i0),
            Return,
            Returnundefined,
            Getpropiterator,
            Getiterator(i0),
            Closeiterator(i0, r0),
            Poplexenv,
            Ldnan,
            Ldinfinity,
            Getunmappedargs,
            Ldglobal,
            Ldnewtarget,
            Ldthis,
            Ldhole,
            Createregexpwithliteral(i0, eid, i0),
            Callrange(i0, i1, r0),
            Gettemplateobject(i0),
            Setobjectwithproto(i0, r0),
            Stownbyvalue(i0, r0, r1),
            Stownbyindex(i0, r0, i1),
            Stownbyname(i0, eid, r0),
            Getmodulenamespace(i0),
            Stmodulevar(i0),
            Ldlocalmodulevar(i0),
            Ldexternalmodulevar(i0),
            Stglobalvar(i0, eid),
            Stownbynamewithnameset(i0, eid, r0),
            Asyncgeneratorreject(r0),
            Stownbyvaluewithnameset(i0, r0, r1),
            Ldsymbol,
            Asyncfunctionenter,
            Ldfunction,
            Debugger,
            Creategeneratorobj(r0),
            Createiterresultobj(r0, r1),
            Createobjectwithexcludedkeys(i1, r0, r1),
            Newobjapply(i0, r0),
            Newlexenvwithname(i1, eid),
            Createasyncgeneratorobj(r0),
            Asyncgeneratorresolve(r0, r1, r2),
            Supercallspread(i0, r0),
            Apply(i0, r0, r1),
            Supercallarrowrange(i0, i1, r0),
            Definegettersetterbyvalue(r0, r1, r2, r3),
            Dynamicimport,
            Resumegenerator,
            Getresumemode,
            Delobjprop(r0),
            Suspendgenerator(r0),
            Asyncfunctionawaituncaught(r0),
            Copydataproperties(r0),
            Starrayspread(r0, r1),
            Stsuperbyvalue(i0, r0, r1),
            Asyncfunctionresolve(r0),
            Asyncfunctionreject(r0),
            Copyrestargs(i0),
            Stsuperbyname(i0, eid, r0),
            Ldbigint(eid),
            Nop,
            Setgeneratorstate(i0),
            Getasynciterator(i0),
            Ldprivateproperty(i0, i0, i0),
            Stprivateproperty(i0, i0, i0, r0),
            Testin(i0, i0, i0),
            Definefieldbyname(i0, eid, r0),
            Definepropertybyname(i0, eid, r0),
            Callthis0withname(i0, eid, r0),
            Callthis1withname(i0, eid, r0, r1),
            Callthis2withname(i0, eid, r0, r1, r2),
            Callthis3withname(i0, eid, r0, r1, r2, r3),
            Callthisrangewithname(i0, i1, eid, r0),
            CallruntimeNotifyconcurrentresult,
            DeprecatedLdlexenv,
            WideCreateobjectwithexcludedkeys(i1, r0, r1),
            Throw,
            CallruntimeDefinefieldbyvalue(i0, r0, r1),
            DeprecatedPoplexenv,
            WideNewobjrange(i1, r0),
            ThrowNotexists,
            CallruntimeDefinefieldbyindex(i0, i1, r0),
            DeprecatedGetiteratornext(r0, r1),
            WideNewlexenv(i1),
            ThrowPatternnoncoercible,
            CallruntimeTopropertykey,
            DeprecatedCreatearraywithbuffer(i0),
            WideNewlexenvwithname(i1, eid),
            ThrowDeletesuperproperty,
            CallruntimeCreateprivateproperty(i1, eid),
            DeprecatedCreateobjectwithbuffer(i0),
            WideCallrange(i1, r0),
            ThrowConstassignment(r0),
            CallruntimeDefineprivateproperty(i0, i0, i0, r0),
            DeprecatedTonumber(r0),
            WideCallthisrange(i1, r0),
            ThrowIfnotobject(r0),
            CallruntimeCallinit(i0, r0),
            DeprecatedTonumeric(r0),
            WideSupercallthisrange(i1, r0),
            ThrowUndefinedifhole(r0, r1),
            CallruntimeDefinesendableclass(i0, eid, eid, i0, r0),
            DeprecatedNeg(r0),
            WideSupercallarrowrange(i1, r0),
            ThrowIfsupernotcorrectcall(i0),
            CallruntimeLdsendableclass(i0),
            DeprecatedNot(r0),
            WideLdobjbyindex(i1),
            CallruntimeLdsendableexternalmodulevar(i0),
            DeprecatedInc(r0),
            WideStobjbyindex(r0, i1),
            ThrowUndefinedifholewithname(eid),
            CallruntimeWideldsendableexternalmodulevar(i0),
            DeprecatedDec(r0),
            WideStownbyindex(r0, i1),
            CallruntimeNewsendableenv(i1),
            DeprecatedCallarg0(r0),
            WideCopyrestargs(i0),
            CallruntimeWidenewsendableenv(i1),
            DeprecatedCallarg1(r0, r1),
            WideLdlexvar(i0, i0),
            CallruntimeStsendablevar(i0, i0),
            DeprecatedCallargs2(r0, r1, r2),
            WideStlexvar(i0, i0),
            DeprecatedCallargs3(r0, r1, r2, r3),
            WideGetmodulenamespace(i0),
            CallruntimeWidestsendablevar(i0, i0),
            DeprecatedCallrange(i1, r0),
            WideStmodulevar(i0),
            CallruntimeLdsendablevar(i0, i0),
            DeprecatedCallspread(r0, r1, r2),
            WideLdlocalmodulevar(i0),
            DeprecatedCallthisrange(i1, r0),
            WideLdexternalmodulevar(i0),
            CallruntimeWideldsendablevar(i0, i0),
            DeprecatedDefineclasswithbuffer(eid, i0, i0, r0, r1),
            WideLdpatchvar(i0),
            CallruntimeIstrue(i0),
            DeprecatedResumegenerator(r0),
            WideStpatchvar(i0),
            CallruntimeIsfalse(i0),
            DeprecatedGetresumemode(r0),
            WideCallthisrangewithname(i1, eid, r0),
            CallruntimeLdlazymodulevar(i0),
            DeprecatedGettemplateobject(r0),
            CallruntimeWideldlazymodulevar(i0),
            DeprecatedDelobjprop(r0, r1),
            CallruntimeLdlazysendablemodulevar(i0),
            DeprecatedSuspendgenerator(r0, r1),
            CallruntimeWideldlazysendablemodulevar(i0),
            DeprecatedAsyncfunctionawaituncaught(r0, r1),
            CallruntimeSupercallforwardallargs(r0),
            DeprecatedCopydataproperties(r0, r1),
            CallruntimeLdsendablelocalmodulevar(i0),
            DeprecatedSetobjectwithproto(r0, r1),
            CallruntimeWideldsendablelocalmodulevar(i0),
            DeprecatedLdobjbyvalue(r0, r1),
            DeprecatedLdsuperbyvalue(r0, r1),
            DeprecatedLdobjbyindex(r0, i1),
            DeprecatedAsyncfunctionresolve(r0, r1, r2),
            DeprecatedAsyncfunctionreject(r0, r1, r2),
            DeprecatedStlexvar(i0, i0, r0),
            DeprecatedGetmodulenamespace(eid),
            DeprecatedStmodulevar(eid),
            DeprecatedLdobjbyname(eid, r0),
            DeprecatedLdsuperbyname(eid, r0),
            DeprecatedLdmodulevar(eid, i0),
            DeprecatedStconsttoglobalrecord(eid),
            DeprecatedStlettoglobalrecord(eid),
            DeprecatedStclasstoglobalrecord(eid),
            DeprecatedLdhomeobject,
            DeprecatedCreateobjecthavingmethod(i0),
            DeprecatedDynamicimport(r0),
            DeprecatedAsyncgeneratorreject(r0, r1),
        ];

        let mut seen = vec![false; TOTAL_VARIANTS];
        for bc in &samples {
            seen[bytecode_variant_index(bc)] = true;
        }
        assert!(
            seen.iter().all(|&b| b),
            "every Bytecode variant must be present in `samples`"
        );

        let lift_single = |bc: Bytecode| -> abcd_ir::Module {
            let mut strings = StringPool::default();
            let desc = strings.get_or_intern("LG;");
            let helper_name = strings.get_or_intern("helper");
            let test_name = strings.get_or_intern("test_fn");
            let str_ent = strings.get_or_intern("123");

            let helper = Method {
                name: helper_name,
                offset: 0x100,
                access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
                function_kind: FileFunctionKind::Function,
                source_lang: FileSourceLang::EcmaScript,
                is_external: false,
                return_type: None,
                arg_types: Vec::new(),
                body: Some(MethodBody {
                    entities: HashMap::new(),
                    num_vregs: 0,
                    num_args: 3,
                    bytecodes: vec![Returnundefined],
                    try_blocks: Vec::new(),
                    ic_size: None,
                }),
                annotations: Default::default(),
                param_annotations: Default::default(),
                debug: None,
            };

            let bytecodes = if bc.is_terminator() || bc.is_return_or_throw() {
                vec![bc]
            } else {
                vec![bc, Returnundefined]
            };
            let entities = HashMap::from([
                ((EntityKind::StringId, 0), EntityRef::string(str_ent)),
                ((EntityKind::MethodId, 0), EntityRef::Method(MethodIdx(0))),
                (
                    (EntityKind::LiteralarrayId, 0),
                    EntityRef::LiteralArray(LiteralArrayIdx(0)),
                ),
            ]);
            let test_m = Method {
                name: test_name,
                offset: 0x200,
                access_flags: AccessFlags::PUBLIC | AccessFlags::STATIC,
                function_kind: FileFunctionKind::Function,
                source_lang: FileSourceLang::EcmaScript,
                is_external: false,
                return_type: None,
                arg_types: Vec::new(),
                body: Some(MethodBody {
                    entities,
                    num_vregs: 8,
                    num_args: 3,
                    bytecodes,
                    try_blocks: Vec::new(),
                    ic_size: None,
                }),
                annotations: Default::default(),
                param_annotations: Default::default(),
                debug: None,
            };
            let cls = Class {
                descriptor: desc,
                name: desc,
                access_flags: AccessFlags::PUBLIC,
                source_lang: FileSourceLang::EcmaScript,
                source_file: None,
                is_external: false,
                super_class: None,
                interfaces: Vec::new(),
                methods: vec![helper, test_m],
                fields: Vec::new(),
                annotations: Default::default(),
            };
            let file = File {
                version: Version::new(12, 0, 6, 0),
                checksum: 0,
                size: 0,
                file_type: FileType::Dynamic,
                strings,
                classes: [(desc, cls)].into_iter().collect(),
                literal_arrays: vec![LiteralArray::new(vec![LiteralValue::String(str_ent)])],
                literal_array_header_offsets: Vec::new(),
            };
            crate::lift_file(&file).expect("synthetic single-bytecode method lifts cleanly")
        };

        for bc in samples {
            if matches!(bc, Nop) {
                assert!(cannot_throw_ir(&bc), "Nop cannot throw");
                continue;
            }
            if bc.is_jump() {
                if matches!(bc, Jmp(..) | Jeqz(..) | Jnez(..)) {
                    assert!(cannot_throw_ir(&bc), "{bc:?} jump cannot throw");
                } else {
                    assert!(
                        !cannot_throw_ir(&bc),
                        "unsupported fused jump {bc:?} must not be marked cannot_throw_ir"
                    );
                }
                continue;
            }

            let is_term = bc.is_terminator() || bc.is_return_or_throw();
            let ir = lift_single(bc);
            let f = &ir.functions[1];
            let mut emitted_ops: Vec<&abcd_ir::Op> = f
                .blocks
                .iter()
                .flat_map(|&bb| &ir.blocks[bb.index()].insts)
                .map(|&iid| &ir.insts[iid.index()].op)
                .collect();
            if !is_term {
                let tail = emitted_ops.pop();
                assert!(
                    matches!(tail, Some(abcd_ir::Op::Return { value: None })),
                    "expected trailing synthetic Returnundefined for {bc:?}, got {tail:?}"
                );
            }

            let ir_may_throw = emitted_ops.iter().any(|op| op.effects().may_throw);
            assert_eq!(
                cannot_throw_ir(&bc),
                !ir_may_throw,
                "may_throw drift on {bc:?}: cannot_throw_ir={}, ir_may_throw={} (ops={emitted_ops:?})",
                cannot_throw_ir(&bc),
                ir_may_throw,
            );
        }

        // Also check `DeprecatedLdmodulevar` with `flag = 1` (`Local` mode -> non-throwing op,
        // while `cannot_throw_ir` conservatively returns `false` because `flag = 0` is `External`).
        let ir_local = lift_single(DeprecatedLdmodulevar(eid, i1));
        let local_op = &ir_local.insts
            [ir_local.blocks[ir_local.functions[1].blocks[0].index()].insts[0].index()]
        .op;
        assert!(matches!(
            local_op,
            abcd_ir::Op::LoadModuleVar {
                kind: abcd_ir::ModuleVarKind::Local,
                ..
            }
        ));
        assert!(!local_op.effects().may_throw);
        assert!(!cannot_throw_ir(&DeprecatedLdmodulevar(eid, i1)));
    }
}
