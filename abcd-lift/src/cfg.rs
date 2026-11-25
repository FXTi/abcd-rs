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

/// Build a CFG from a method body's bytecodes and try-blocks.
///
/// Returns `None` if the method body has no bytecodes.
pub fn build_cfg(body: &MethodBody) -> Option<RawCfg> {
    let bytecodes = &body.bytecodes;
    // unreachable in production: the only non-test caller (lib.rs:441) is
    // dominated by the `body.bytecodes.is_empty()` hard error at
    // lib.rs:421-423 — c-COV diagnosis
    if bytecodes.is_empty() {
        return None;
    }

    let n = bytecodes.len();

    // Phase 1a: Natural leaders (entry, jump targets, post-jump/terminator
    // fall-throughs, and catch handler entries).
    let mut natural_leaders = BTreeSet::new();
    natural_leaders.insert(0);

    for (idx, bc) in bytecodes.iter().enumerate() {
        if bc.is_jump() {
            if let Some(target) = jump_target(bc)
                && target < n
            {
                natural_leaders.insert(target);
            }
            if idx + 1 < n {
                natural_leaders.insert(idx + 1);
            }
        } else if bc.is_terminator() && idx + 1 < n {
            natural_leaders.insert(idx + 1);
        }
    }

    for try_block in &body.try_blocks {
        for catch in &try_block.catches {
            let handler = catch.handler as usize;
            if handler < n {
                natural_leaders.insert(handler);
            }
        }
    }

    if body.try_blocks.is_empty() {
        return Some(partition_and_wire(
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
        Some(partition_and_wire(bytecodes, &body.try_blocks, &leaders))
    } else {
        Some(pre_cfg)
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
        } else if !last_bc.is_terminator()
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
            | CallruntimeTopropertykey
            | Ldundefined
            | Ldnull
            | Ldtrue
            | Ldfalse
            | Ldhole
            | Ldnan
            | Ldinfinity
            | Ldai(..)
            | Fldai(..)
            | LdaStr(..)
            | Ldbigint(..)
            | Ldthis
            | Ldfunction
            | Ldnewtarget
            | Ldglobal
            | DeprecatedLdlexenv
            | DeprecatedLdhomeobject
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
            | Asyncgeneratorresolve(..)
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
            | Ldexternalmodulevar(..)
            | WideLdexternalmodulevar(..)
            | CallruntimeLdsendablelocalmodulevar(..)
            | CallruntimeWideldsendablelocalmodulevar(..)
            | CallruntimeLdsendableexternalmodulevar(..)
            | CallruntimeWideldsendableexternalmodulevar(..)
            | CallruntimeLdsendableclass(..)
            | Stmodulevar(..)
            | WideStmodulevar(..)
            | Getmodulenamespace(..)
            | WideGetmodulenamespace(..)
            | DeprecatedGetmodulenamespace(..)
            | DeprecatedStmodulevar(..)
            | DeprecatedLdmodulevar(..)
    )
}

/// Bytecodes guaranteed to emit zero `may_throw == true` IR ops, including
/// non-throwing control-flow transfers (`R2-C1` / `R2-C2`).
fn cannot_throw_ir(bc: &Bytecode) -> bool {
    use Bytecode::*;
    is_guaranteed_non_throwing(bc)
        || matches!(
            bc,
            Jmp(_)
                | Jeqz(_)
                | Jnez(_)
                | Jstricteqz(_)
                | Jnstricteqz(_)
                | Jstricteqnull(_)
                | Jnstricteqnull(_)
                | Jstrictequndefined(_)
                | Jnstrictequndefined(_)
                | Return
                | Returnundefined
        )
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
        | WideNewobjrange(argc, start)
        | DeprecatedCallrange(argc, start) => {
            let count = argc.0 as u16;
            for i in 0..count {
                if let Some(r) = start.0.checked_add(i) {
                    f(r);
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
            entity_offsets: Default::default(),
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
            entity_offsets: Default::default(),
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
            entity_offsets: Default::default(),
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
                    type_idx: u32::MAX,
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
            entity_offsets: Default::default(),
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
                    type_idx: u32::MAX,
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
            entity_offsets: Default::default(),
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
                    type_idx: u32::MAX,
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
            entity_offsets: Default::default(),
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
                    type_idx: u32::MAX,
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
}
