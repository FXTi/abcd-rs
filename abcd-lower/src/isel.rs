//! Instruction selection: IR instructions → ArkCompiler bytecodes
//! (port of v0.1 `abcd_ir::lower::isel` onto the v0.2 IR).
//!
//! Takes an IR function with register allocation results and produces
//! a sequence of ArkCompiler bytecodes per basic block.
//!
//! v0.2 adaptations:
//!
//! - Entity operands are IR identities, never file offsets (the reverse
//!   mapping lives in `method_body`): strings ride as the raw [`Sym`]
//!   index, method references as the module function-table index
//!   ([`FuncId`]), literal shapes as the [`ConstId`].
//! - The lift's expansion mappings (compare.rs rule 3) fold back via
//!   [`Suppression`]: `DefineFunc`+`AllocClosure` → definefunc,
//!   +`DefineMethod` → definemethod, `LoadConst`+`LoadPropIdx` →
//!   ldobjbyindex, `LoadConst(undefined)`+`TryGetGlobal` →
//!   tryldglobalbyname.
//! - Frame-initial values are [`ValueDef::Const`] constants; like v0.1's
//!   entry-top seed literals they are materialized at the entry block
//!   top (later-created first — v0.1 inserted each seed at index 0).
//! - v0.1's `BinOp` splits into [`Op::BinaryOp`]/[`Op::Compare`]; the
//!   compare-branch fusion pattern-matches `Op::Compare` accordingly.

use std::collections::{HashMap, HashSet};

use abcd_ir2::{
    BinOp, BlockId, CallKind, CmpOp, Const, ConstId, FuncId, InstId, Module, Op, SuperCheck,
    SuperKey, Sym, UnOp, ValueDef, ValueId,
};
use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Label, Reg};

use crate::LowerError;
use crate::fusion::Suppression;
use crate::regalloc::{self, RegAlloc, RegSlot};

/// Result of instruction selection for one function.
#[derive(Debug)]
pub struct IselResult {
    /// Bytecodes per block (in RPO order).
    pub block_codes: Vec<(BlockId, Vec<Bytecode>)>,
    /// Audit trail of every emitted entity operand, keyed by (entity
    /// kind, raw operand value). v0.2 operands are IR entities by
    /// construction (always [`EntityTrace::Traced`]); the v0.1
    /// `Untraced` case (identity fallback for a source-less hand-built
    /// module) has no v0.2 equivalent — traceability is decided wholly
    /// by the reverse resolution in `method_body::to_method_body`.
    pub entity_traces: HashMap<(EntityKind, u32), EntityTrace>,
    /// Total number of IC slots allocated for this function.
    pub ic_size: u32,
    /// First unsupported-instruction message (v0.1 parity field; v0.2
    /// reports unsupported shapes through `Result` hard errors instead).
    pub unsupported: Option<String>,
}

/// Whether an emitted entity operand value is traceable to a source-file
/// entity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EntityTrace {
    /// The operand value traces to a source-file entity.
    Traced,
    /// At least one use of this operand value could not be traced
    /// (v0.1 legacy; unused in v0.2).
    Untraced,
}

/// Records every emitted entity operand for the audit trail.
struct EntityTracer {
    traces: HashMap<(EntityKind, u32), EntityTrace>,
}

impl EntityTracer {
    /// Emit a string operand: the raw [`Sym`] arena index. Reverse
    /// resolution (content → source offset) happens in
    /// `method_body::to_method_body`.
    fn eid(&mut self, sym: Sym) -> EntityId {
        self.traces
            .insert((EntityKind::StringId, sym.0), EntityTrace::Traced);
        EntityId(sym.0)
    }

    /// Emit a method-reference operand: the raw module function-table
    /// index. Reverse resolution (index → method offset) happens in
    /// `method_body::to_method_body`.
    fn method_eid(&mut self, func: FuncId) -> EntityId {
        self.traces
            .insert((EntityKind::MethodId, func.0), EntityTrace::Traced);
        EntityId(func.0)
    }

    /// Emit a literal-shape operand: the raw [`ConstId`]. Reverse
    /// resolution (content → literal-array offset) happens in
    /// `method_body::to_method_body`.
    fn literal_eid(&mut self, shape: ConstId) -> EntityId {
        self.traces
            .insert((EntityKind::LiteralarrayId, shape.0), EntityTrace::Traced);
        EntityId(shape.0)
    }
}

/// Per-function IC slot allocator.
struct IcAllocator {
    counter: u32,
}

impl IcAllocator {
    fn new() -> Self {
        Self { counter: 0 }
    }

    /// Allocate `slot_count` consecutive IC slots, returning the first slot's Imm.
    fn alloc(&mut self, slot_count: u16) -> Imm {
        let id = self.counter;
        self.counter = self.counter.saturating_add(slot_count as u32);
        Imm(id as i64)
    }

    /// Allocate 1 IC slot (arithmetic, globals, object/array creation, function def).
    fn one(&mut self) -> Imm {
        self.alloc(1)
    }

    /// Allocate 2 IC slots (property access, calls, iterators).
    fn two(&mut self) -> Imm {
        self.alloc(2)
    }
}

/// Emission-time model of the PHYSICAL accumulator content (B4:
/// "acc-as-cache"). The accumulator is one physical location; register
/// allocation gives every value a register home, and this tracker records
/// — as an emission-time fact — which value's content the acc provably
/// holds at each point. `ensure_acc` consults it: a hit elides the `Lda`.
///
/// Soundness invariant: [`AccContent::Holds`]`(v)` is recorded ONLY at
/// points where the physical acc was just written with v's content (an
/// acc-writing instruction's result, the homing `Sta`, an `Lda(home v)`,
/// or exception dispatch), and every later acc write updates the tracker
/// (the helpers in this file are the only acc writers). A stale entry is
/// therefore impossible in the dangerous direction: a hit and a miss
/// always produce the same physical acc content. The worst a modeling gap
/// can do is forget a content (`Unknown`), costing a redundant `Lda`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AccContent {
    /// Frame-entry state: the vendor frame init leaves the hole in acc
    /// (arkcompiler_ets_runtime-master/ecmascript/interpreter/
    /// interpreter-inl.cpp:739, :1482). Never equal to a value's content.
    Hole,
    /// The physical acc provably holds this SSA value's content.
    Holds(ValueId),
    /// Unknown content: an acc-writing instruction whose result is not a
    /// tracked value, exception dispatch of an uncolored exception value,
    /// the meet of disagreeing predecessors, or a not-yet-emitted
    /// (back-edge) predecessor.
    Unknown,
}

/// Meet the acc content at a block entry over its already-emitted
/// predecessors: the content is known only when EVERY predecessor exits
/// with the SAME content. A predecessor without a recorded exit state (a
/// back edge — RPO emits it later — or an unreachable block) degrades the
/// meet to `Unknown`. Layout-inserted phi copies and trampolines are pure
/// `Mov`s (vendor `acc: none`) and never perturb the content across an
/// edge, so per-predecessor exit states are valid at successor entries.
fn meet_acc_content<'a>(
    preds: impl IntoIterator<Item = &'a abcd_ir2::Edge>,
    exit_states: &HashMap<BlockId, AccContent>,
) -> AccContent {
    let mut meet: Option<AccContent> = None;
    for edge in preds {
        let state = exit_states
            .get(&edge.from)
            .copied()
            .unwrap_or(AccContent::Unknown);
        meet = Some(match (meet, state) {
            (None, s) => s,
            (Some(a), b) if a == b => a,
            _ => AccContent::Unknown,
        });
    }
    meet.unwrap_or(AccContent::Unknown)
}

/// Select instructions for a function.
pub fn select(
    module: &Module,
    func_id: FuncId,
    alloc: &RegAlloc,
    rpo: &[BlockId],
    suppression: &Suppression,
) -> Result<IselResult, LowerError> {
    let mut block_codes: Vec<(BlockId, Vec<Bytecode>)> = Vec::new();
    let mut ic = IcAllocator::new();
    let mut tracer = EntityTracer {
        traces: HashMap::new(),
    };

    let Some(func) = module.func(func_id) else {
        return Err(LowerError::EmptyFunction(func_id));
    };
    let entry_block = func.entry().ok_or(LowerError::EmptyFunction(func_id))?;

    // Values with at least one use: an acc-writing instruction's result is
    // homed (`Sta`) only when it has a use — a dead result never leaves the
    // accumulator, so its acc content is `Unknown` to the tracker.
    // Suppressed values are never home-read (fusion).
    let mut used: HashSet<ValueId> = HashSet::new();
    for &bb in rpo {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &inst_id in &block.insts {
            if let Some(inst) = module.inst(inst_id) {
                used.extend(
                    inst.op
                        .operands()
                        .into_iter()
                        .filter(|v| !suppression.values.contains(v)),
                );
            }
        }
    }

    // Per-block EXIT acc content, filled as blocks are emitted (RPO: every
    // non-back-edge predecessor is emitted before its successors).
    let mut exit_states: HashMap<BlockId, AccContent> = HashMap::new();

    // N13: handler block → its exception value. The exception is delivered
    // in acc by the dispatch itself; the prologue below materializes it
    // into its register home.
    let mut handler_exc: HashMap<BlockId, ValueId> = HashMap::new();
    for region in &func.try_regions {
        for catch in &region.catches {
            handler_exc.entry(catch.handler).or_insert(catch.exception);
        }
    }
    // EVERY catch-handler block (try-region derived, not just the ones with
    // a seeded exception value): exception dispatch physically clobbers the
    // accumulator at handler entry, so a handler's entry acc content is
    // never the meet of its CFG predecessors — values defined in the try
    // body are NOT in acc, even when every predecessor agrees.
    let handler_blocks: HashSet<BlockId> = func
        .try_regions
        .iter()
        .flat_map(|region| region.catches.iter().map(|c| c.handler))
        .collect();

    // Frame-initial constants owned by this function (v0.1's entry-top
    // seed literals), materialized at the entry block top, LATER-CREATED
    // FIRST — v0.1 inserted each new seed at entry index 0, so the entry
    // block began with the seeds in reverse creation order. UNUSED seeds
    // are materialized too: v0.1 emits the seed's load unconditionally
    // (only the `Sta` is use-gated) and an unused seed's load leaves the
    // acc tracker `Unknown`.
    let mut entry_consts = regalloc::frame_init_consts(module, func_id);
    entry_consts.sort_unstable_by(|a, b| b.cmp(a)); // descending id = reverse creation

    // N21 pinned stores for handler-block phis, grouped by emission point.
    // Deterministic order: sorted by (pred, src, dst) / (src, dst).
    //
    // - AfterDef: the source is defined by an instruction inside the pred —
    //   the store is emitted immediately after that instruction (the
    //   closest implementable point to the vendored `sta`; the source's
    //   result homing has just run, so its register home holds it).
    // - BlockStart(pred): every other source — defined in a dominating
    //   block, a phi result (materialized by the incoming edge copies), a
    //   parameter (the entry copy-in prologue has run), or an exception
    //   value (the handler prologue has run). The store is emitted before
    //   the pred's first instruction, so an exception at any pred
    //   instruction observes it.
    let mut after_def_stores: HashMap<ValueId, Vec<(ValueId, ValueId)>> = HashMap::new();
    let mut block_start_stores: HashMap<BlockId, Vec<(ValueId, ValueId)>> = HashMap::new();
    for &(pred, src, dst) in &alloc.handler_phi_stores {
        let defined_in_pred = match module.value(src).map(|v| v.def) {
            Some(ValueDef::Inst(i)) => module
                .inst(i)
                .is_some_and(|inst| !inst.op.is_phi() && inst.block == pred),
            // A frame-initial const's definition site is the entry-block
            // materialization: for an entry-pred handler phi, its pinned
            // store belongs right after the materialization (after-def),
            // never at block start (the home is written only there).
            Some(ValueDef::Const(_)) => pred == entry_block,
            _ => false,
        };
        if defined_in_pred {
            after_def_stores.entry(src).or_default().push((src, dst));
        } else {
            block_start_stores.entry(pred).or_default().push((src, dst));
        }
    }
    for stores in block_start_stores.values_mut() {
        stores.sort_unstable();
    }
    for stores in after_def_stores.values_mut() {
        stores.sort_unstable();
    }

    for &bb in rpo {
        let mut codes = Vec::new();
        let Some(block) = module.block(bb) else {
            continue;
        };

        // Block-entry acc content (B4): the entry block starts with the
        // vendor frame-init hole; a catch handler starts with the
        // dispatched exception object (unknown to the tracker until the
        // prologue homes it); every other block meets its predecessors'
        // exit contents.
        let mut tracker = if bb == entry_block {
            AccContent::Hole
        } else if handler_blocks.contains(&bb) {
            AccContent::Unknown
        } else {
            meet_acc_content(&block.preds, &exit_states)
        };

        // Copy-in prologue: arguments arrive in the ABI top slots and are
        // moved into the parameters' vreg homes at the very start of the
        // entry block. `mov` never touches acc — the tracker stays Hole.
        if bb == entry_block {
            emit_param_copy_in(func_id, module, alloc, &mut codes)?;
        }

        // N13 handler prologue: exception dispatch physically delivers the
        // thrown object in acc (vendor `SET_ACC(exception)`,
        // interpreter_assembly.cpp:7860-7863) — materialize it into its
        // register home as the handler's FIRST bytecode, before anything
        // can clobber acc. This is exactly the vendored handler-entry
        // `sta vX`. Skipped when the handler never reads the exception (the
        // value is then uncolored). After the store the tracker knows the
        // acc holds the exception value (a `sta` reads but never writes
        // acc — vendor `acc: in`).
        if let Some(&exc) = handler_exc.get(&bb) {
            if let Some(&RegSlot::Reg(home)) = alloc.allocation.get(&exc) {
                emit_sta_home(func_id, home, alloc, &mut codes)?;
                tracker = AccContent::Holds(exc);
            }
        }

        // N21 pinned stores at block start (phi-result / exception /
        // parameter sources). Runs after the exception prologue so a store
        // sourcing the exception reads its just-written home. Pure `Mov`s:
        // the tracker is unaffected.
        if let Some(stores) = block_start_stores.get(&bb) {
            for &(src, dst) in stores {
                let s = home_of(func_id, src, alloc)?;
                let d = home_of(func_id, dst, alloc)?;
                if s != d {
                    codes.push(Bytecode::Mov(Reg(d), Reg(s)));
                }
            }
        }

        // Frame-initial constants (v0.1's entry-top seed literals), at the
        // head of the entry block's instruction stream — after the pinned
        // stores, exactly where v0.1's seed instructions sat. The load is
        // unconditional (v0.1 emits it for unused seeds too); the homing
        // `Sta` is use-gated, and an unused seed's acc write leaves the
        // tracker `Unknown` (v0.1's `home_result` semantics).
        if bb == entry_block {
            for &cval in &entry_consts {
                let Some(ValueDef::Const(cid)) = module.value(cval).map(|v| v.def) else {
                    continue;
                };
                let bc = const_load_bytecode(module, cid, func_id, &mut tracer)?;
                codes.push(bc);
                if used.contains(&cval) {
                    let r = home_of(func_id, cval, alloc)?;
                    emit_sta_home(func_id, r, alloc, &mut codes)?;
                    tracker = AccContent::Holds(cval);
                } else {
                    tracker = AccContent::Unknown;
                }
                // N21 after-def pinned stores keyed by this const value:
                // the materialization is its definition site (v0.1's seed
                // instruction — the store runs right after its `Sta`).
                if let Some(stores) = after_def_stores.get(&cval) {
                    for &(_, dst) in stores {
                        let d = home_of(func_id, dst, alloc)?;
                        let s = home_of(func_id, cval, alloc)?;
                        if s != d {
                            codes.push(Bytecode::Mov(Reg(d), Reg(s)));
                        }
                    }
                }
            }
        }

        // Phi copies from predecessors are handled in layout (inserted before terminators).
        // Skip phi instructions — they don't produce bytecodes directly.

        for &inst in &block.insts {
            if suppression.insts.contains(&inst) {
                continue; // folded into its consumer (fusion)
            }
            let Some(node) = module.inst(inst) else {
                continue;
            };

            select_inst(
                node,
                inst,
                &block.insts,
                func_id,
                module,
                alloc,
                &used,
                suppression,
                &mut tracer,
                &mut codes,
                &mut ic,
                &mut tracker,
            )?;

            // N21 pinned stores right after the defining instruction (see
            // the ordering argument at `after_def_stores`). Pure `Mov`s.
            if let Some(v) = node.result {
                if let Some(stores) = after_def_stores.get(&v) {
                    for &(_, dst) in stores {
                        let d = home_of(func_id, dst, alloc)?;
                        let s = home_of(func_id, v, alloc)?;
                        if s != d {
                            codes.push(Bytecode::Mov(Reg(d), Reg(s)));
                        }
                    }
                }
            }
        }

        exit_states.insert(bb, tracker);
        block_codes.push((bb, codes));
    }

    Ok(IselResult {
        block_codes,
        entity_traces: tracer.traces,
        ic_size: ic.counter,
        unsupported: None,
    })
}

/// Emit the copy-in prologue at the very start of the entry block: for each
/// parameter `i`, `Mov(home_i, Reg(num_regs + i))` moves the ABI top slot
/// into the parameter's vreg home. The vendor frame is
/// `num_vregs + num_args` with arguments in the top slots
/// (static_core/runtime/include/method.h); `to_method_body` declares
/// `num_vregs = num_regs`, so the arg slots of the lowered frame start
/// exactly at `Reg(num_regs)`. `alloc.num_regs` is final here — it already
/// includes the `copy_temp` reservation.
///
/// `mcs_color` pre-assigns every parameter a register home (there is no
/// accumulator coloring since B4), so an uncolored parameter can only come
/// from a hand-crafted allocation and is a hard error, never a silent
/// path. The prologue is pure `Mov`s (vendor `acc: none`) and does not
/// perturb the emission-time acc tracker.
///
/// Emission-point safety: `layout` inserts phi copies before predecessor
/// TERMINATORS (or into trampolines appended after all real blocks), never
/// at the start of a block, and the entry block has no predecessors in
/// practice — so code prepended at `codes[0..]` of the entry block cannot
/// interleave with phi-copy sequences.
fn emit_param_copy_in(
    func_id: FuncId,
    module: &Module,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<(), LowerError> {
    let Some(func) = module.func(func_id) else {
        return Err(LowerError::EmptyFunction(func_id));
    };
    for (i, &val) in func.params.iter().enumerate() {
        let home = home_of(func_id, val, alloc)?;
        let arg_slot = u32::from(alloc.num_regs) + i as u32;
        if arg_slot > u32::from(u16::MAX) {
            return Err(LowerError::RegisterOverflow(func_id));
        }
        codes.push(Bytecode::Mov(Reg(home), Reg(arg_slot as u16)));
    }
    Ok(())
}

/// Look up the register home allocation assigned to a value. A missing
/// entry means the operand was never colored (e.g. a dangling value
/// reference in unverified IR), which the old code silently treated as
/// acc-resident.
fn home_of(func_id: FuncId, val: ValueId, alloc: &RegAlloc) -> Result<u16, LowerError> {
    match alloc.allocation.get(&val).copied() {
        Some(RegSlot::Reg(r)) => Ok(r),
        None => Err(LowerError::UnallocatedOperand {
            func: func_id,
            value: val,
        }),
    }
}

/// Get the Reg for a value's register operand: its colored home.
///
/// High-register routing (S2): `sta`/`lda` are `op_v_8`-only in the vendored
/// ISA and — except for the auto-widening `mov` — every register operand
/// slot isel emits is u8-only as well (isa.yaml format audit: all `v`/`vN`
/// operands are `_8`; the `op_imm_16_v_8`-style second formats widen only
/// the imm). A value colored to a register ≥ 256 is therefore routed
/// through the reserved LOW scratch block (`RegAlloc::low_scratch_base`),
/// one scratch per operand position, so simultaneous operands never alias.
/// `operand_idx` is the operand's position within its instruction. The
/// emitted `mov` never touches the accumulator (vendor `acc: none`), so
/// the emission-time acc tracker is unaffected.
fn val_reg(
    func_id: FuncId,
    val: ValueId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
    operand_idx: usize,
) -> Result<Reg, LowerError> {
    let r = home_of(func_id, val, alloc)?;
    if r <= 255 {
        return Ok(Reg(r));
    }
    let scratch = operand_scratch(func_id, alloc, operand_idx)?;
    codes.push(Bytecode::Mov(scratch, Reg(r)));
    Ok(scratch)
}

/// The low operand-routing scratch for position `idx` (high-register mode).
fn operand_scratch(func_id: FuncId, alloc: &RegAlloc, idx: usize) -> Result<Reg, LowerError> {
    let base = alloc
        .low_scratch_base
        .ok_or(LowerError::MissingLowScratch(func_id))?;
    if idx >= regalloc::LOW_OPERAND_SCRATCHES as usize {
        return Err(LowerError::LowScratchExhausted(func_id));
    }
    Ok(Reg(base + idx as u16))
}

/// The reserved low acc-routing scratch (high-register mode).
fn acc_scratch(func_id: FuncId, alloc: &RegAlloc) -> Result<Reg, LowerError> {
    alloc
        .low_scratch_base
        .map(|base| Reg(base + regalloc::LOW_OPERAND_SCRATCHES))
        .ok_or(LowerError::MissingLowScratch(func_id))
}

/// Emit `Sta(home)` for the register home `r` (a high home detours through
/// the reserved low acc scratch: `sta scratch; mov home, scratch`). `sta`
/// reads but never writes the accumulator (vendor `acc: in`), so the
/// emission-time acc tracker is the caller's concern.
fn emit_sta_home(
    func_id: FuncId,
    r: u16,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<(), LowerError> {
    if r <= 255 {
        codes.push(Bytecode::Sta(Reg(r)));
    } else {
        let scratch = acc_scratch(func_id, alloc)?;
        codes.push(Bytecode::Sta(scratch));
        codes.push(Bytecode::Mov(Reg(r), scratch));
    }
    Ok(())
}

/// Ensure a value's content is physically in the accumulator, consulting
/// the emission-time acc tracker (B4, acc-as-cache): a hit — the tracker
/// proves the acc already holds THIS value — is a no-op. A miss emits
/// `Lda(home)` (a high home first detours through the reserved low acc
/// scratch: `mov scratch, high; lda scratch`) and records the new content.
fn ensure_acc(
    tracker: &mut AccContent,
    func_id: FuncId,
    val: ValueId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<(), LowerError> {
    if *tracker == AccContent::Holds(val) {
        return Ok(());
    }
    let r = home_of(func_id, val, alloc)?;
    if r <= 255 {
        codes.push(Bytecode::Lda(Reg(r)));
    } else {
        let scratch = acc_scratch(func_id, alloc)?;
        codes.push(Bytecode::Mov(scratch, Reg(r)));
        codes.push(Bytecode::Lda(scratch));
    }
    *tracker = AccContent::Holds(val);
    Ok(())
}

/// Materialize one instruction's operands: resolve every register operand
/// to its home (high registers detour through a per-position low scratch —
/// `mov` never touches acc), then bring the acc operand into the
/// accumulator (tracker-aware: a hit elides the `Lda`).
///
/// The old spill-before-load dance (B3) is gone by construction: no
/// operand can be "acc-resident" anymore, because the accumulator is not a
/// coloring class — register operands always read their register homes,
/// and `ensure_acc` is the only acc writer here.
fn materialize_operands(
    tracker: &mut AccContent,
    func_id: FuncId,
    reg_operands: &[ValueId],
    acc_operand: Option<ValueId>,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<Vec<Reg>, LowerError> {
    let mut regs = Vec::with_capacity(reg_operands.len());
    for (idx, &v) in reg_operands.iter().enumerate() {
        regs.push(val_reg(func_id, v, alloc, codes, idx)?);
    }
    if let Some(acc_val) = acc_operand {
        ensure_acc(tracker, func_id, acc_val, alloc, codes)?;
    }
    Ok(regs)
}

/// Home an acc-writing instruction's result and update the emission-time
/// acc tracker.
///
/// The instruction's bytecode just wrote the accumulator (vendor
/// `acc: out`/`acc: inout` — every result-producing opcode isel emits has
/// one of those modes). A result with at least one use gets a `Sta(home)`
/// and the tracker records that acc now holds the value — the next acc use
/// of it is a cache hit. A dead result (no uses) needs no store; the acc
/// content is then not a tracked value (`Unknown`), so the next acc use of
/// ANY value reloads from its home.
fn home_result(
    tracker: &mut AccContent,
    result: Option<ValueId>,
    used: &HashSet<ValueId>,
    func_id: FuncId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<(), LowerError> {
    match result {
        Some(v) if used.contains(&v) => {
            let r = home_of(func_id, v, alloc)?;
            emit_sta_home(func_id, r, alloc, codes)?;
            *tracker = AccContent::Holds(v);
        }
        _ => *tracker = AccContent::Unknown,
    }
    Ok(())
}

/// The bytecode that materializes a constant into the accumulator (shared
/// by [`Op::LoadConst`] and the entry-top frame-initial materialization).
///
/// v0.1 mapping, inverted: Undefined → ldundefined, Hole → ldhole, Null →
/// ldnull, Bool → ldtrue/ldfalse, canonical-NaN bits → ldnan (the lift
/// pools `Ldnan` as `Const::number(f64::NAN)`), +∞ bits → ldinfinity (the
/// lift pools `Ldinfinity` likewise), other numbers → v0.1's
/// `LiteralNumber` rule (integral, negative-zero excluded → `ldai`; else
/// `fldai` on raw bits, N37), String → lda.str, BigInt → ldbigint. A bare
/// shape constant (literal tree / method ref) has no materialization —
/// shapes only flow through their dedicated ops.
fn const_load_bytecode(
    module: &Module,
    cid: ConstId,
    func_id: FuncId,
    tracer: &mut EntityTracer,
) -> Result<Bytecode, LowerError> {
    let Some(c) = module.consts.get(cid) else {
        return Err(LowerError::UnsupportedInstruction {
            func: func_id,
            message: format!("LoadConst of unknown constant {cid}"),
        });
    };
    Ok(match c {
        Const::Undefined => Bytecode::Ldundefined,
        Const::Hole => Bytecode::Ldhole,
        Const::Null => Bytecode::Ldnull,
        Const::Bool(true) => Bytecode::Ldtrue,
        Const::Bool(false) => Bytecode::Ldfalse,
        Const::Number(bits) => {
            if *bits == f64::NAN.to_bits() {
                Bytecode::Ldnan
            } else if *bits == f64::INFINITY.to_bits() {
                Bytecode::Ldinfinity
            } else {
                let n = f64::from_bits(*bits);
                // N37: `-0.0 == 0.0` in IEEE, so the plain integer check
                // took the `ldai 0` path for -0.0 and lost the sign bit
                // (observable: `1 / -0` is -Infinity, `Object.is(-0, 0)`
                // is false). Exclude negative zero from the Ldai path.
                if n == (n as i32) as f64 && !(n == 0.0 && n.is_sign_negative()) {
                    Bytecode::Ldai(Imm(n as i64))
                } else {
                    Bytecode::Fldai(Imm(*bits as i64))
                }
            }
        }
        Const::String(s) => Bytecode::LdaStr(tracer.eid(*s)),
        Const::BigInt(s) => Bytecode::Ldbigint(tracer.eid(*s)),
        Const::ArrayLiteral(_) | Const::ObjectLiteral { .. } | Const::MethodRef(_) => {
            return Err(LowerError::UnsupportedInstruction {
                func: func_id,
                message: format!(
                    "LoadConst of a literal shape / method reference ({c:?}) has no \
                     materialization bytecode — shapes flow through their dedicated ops"
                ),
            });
        }
    })
}

/// Recover the by-index immediate of a fused `LoadPropIdx`/`StorePropIdx`:
/// the value of the suppressed adjacent `LoadConst(number)`, as the
/// vendor's i64 imm truncated to u32 exactly the way v0.1's lift truncated
/// it (`index.0 as u32`).
fn fused_index_imm(module: &Module, index: ValueId, suppression: &Suppression) -> Option<Imm> {
    if !suppression.values.contains(&index) {
        return None;
    }
    let ValueDef::Inst(iid) = module.value(index)?.def else {
        return None;
    };
    let Op::LoadConst(cid) = &module.inst(iid)?.op else {
        return None;
    };
    let num = module.consts.get(*cid)?.as_f64()?;
    if num.fract() != 0.0 {
        return None;
    }
    Some(Imm((num as i64 as u32) as i64))
}

/// The [`FuncId`] of a `DefineFunc` body when `v` is (a possibly
/// closure-wrapped) fused define-chain value: directly a suppressed
/// `DefineFunc` result, or a suppressed `AllocClosure` result wrapping
/// one.
fn fused_definefunc_body(module: &Module, v: ValueId, suppression: &Suppression) -> Option<FuncId> {
    if !suppression.values.contains(&v) {
        return None;
    }
    let ValueDef::Inst(iid) = module.value(v)?.def else {
        return None;
    };
    match &module.inst(iid)?.op {
        Op::DefineFunc { body, .. } => Some(*body),
        Op::AllocClosure { func } => {
            let ValueDef::Inst(fiid) = module.value(*func)?.def else {
                return None;
            };
            let Op::DefineFunc { body, .. } = &module.inst(fiid)?.op else {
                return None;
            };
            Some(*body)
        }
        _ => None,
    }
}

/// Select bytecodes for a single IR instruction.
///
/// `inst` and `block_insts` (the owning block's instruction list) are
/// needed by the CondBranch compare-fusion soundness checks: fusion
/// re-reads another instruction's operands, which is only valid when the
/// comparison chain sits immediately before the branch in the same block.
///
/// `tracker` is the emission-time acc-content model (B4, acc-as-cache):
/// every acc load goes through `ensure_acc`/`materialize_operands` (the
/// only acc writers besides result homing), and every arm whose bytecode
/// writes the accumulator (vendor `acc: out`/`inout` — exactly the arms
/// with a result, plus `CopyDataProps`) ends with `home_result` or an
/// explicit tracker invalidation. Arms whose bytecodes only READ the acc
/// (`acc: in`, e.g. `stobjbyname`) or ignore it (`acc: none`, e.g. `mov`,
/// `throw.ifnotobject`) leave the tracker untouched.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn select_inst(
    node: &abcd_ir2::Inst,
    inst: InstId,
    block_insts: &[InstId],
    func_id: FuncId,
    module: &Module,
    alloc: &RegAlloc,
    used: &HashSet<ValueId>,
    suppression: &Suppression,
    tracer: &mut EntityTracer,
    codes: &mut Vec<Bytecode>,
    ic: &mut IcAllocator,
    tracker: &mut AccContent,
) -> Result<(), LowerError> {
    let data = &node.op;
    let result = node.result;
    match data {
        // ── Constants ────────────────────────────────────────────────
        Op::LoadConst(cid) => {
            let bc = const_load_bytecode(module, *cid, func_id, tracer)?;
            codes.push(bc);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }

        // ── Binary / Compare / Unary ─────────────────────────────────
        Op::BinaryOp { op, left, right } => {
            let regs =
                materialize_operands(tracker, func_id, &[*right], Some(*left), alloc, codes)?;
            let r = regs[0];
            let bc = match op {
                BinOp::Add => Bytecode::Add2(ic.one(), r),
                BinOp::Sub => Bytecode::Sub2(ic.one(), r),
                BinOp::Mul => Bytecode::Mul2(ic.one(), r),
                BinOp::Div => Bytecode::Div2(ic.one(), r),
                BinOp::Mod => Bytecode::Mod2(ic.one(), r),
                BinOp::Exp => Bytecode::Exp(ic.one(), r),
                BinOp::Shl => Bytecode::Shl2(ic.one(), r),
                BinOp::Shr => Bytecode::Shr2(ic.one(), r),
                BinOp::Ashr => Bytecode::Ashr2(ic.one(), r),
                BinOp::BitAnd => Bytecode::And2(ic.one(), r),
                BinOp::BitOr => Bytecode::Or2(ic.one(), r),
                BinOp::BitXor => Bytecode::Xor2(ic.one(), r),
            };
            codes.push(bc);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::Compare { op, left, right } => {
            let regs =
                materialize_operands(tracker, func_id, &[*right], Some(*left), alloc, codes)?;
            let r = regs[0];
            let bc = match op {
                CmpOp::Eq => Bytecode::Eq(ic.one(), r),
                CmpOp::NotEq => Bytecode::Noteq(ic.one(), r),
                CmpOp::StrictEq => Bytecode::Stricteq(ic.one(), r),
                CmpOp::StrictNotEq => Bytecode::Strictnoteq(ic.one(), r),
                CmpOp::Less => Bytecode::Less(ic.one(), r),
                CmpOp::LessEq => Bytecode::Lesseq(ic.one(), r),
                CmpOp::Greater => Bytecode::Greater(ic.one(), r),
                CmpOp::GreaterEq => Bytecode::Greatereq(ic.one(), r),
                CmpOp::In => Bytecode::Isin(ic.one(), r),
                CmpOp::InstanceOf => Bytecode::Instanceof(ic.one(), r),
            };
            codes.push(bc);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::UnaryOp { op, operand } => {
            ensure_acc(tracker, func_id, *operand, alloc, codes)?;
            let bc = match op {
                UnOp::Minus => Bytecode::Neg(ic.one()),
                UnOp::LogicalNot => Bytecode::Not(ic.one()),
                UnOp::Inc => Bytecode::Inc(ic.one()),
                UnOp::Dec => Bytecode::Dec(ic.one()),
                UnOp::TypeOf => Bytecode::Typeof(ic.one()),
                UnOp::ToNumber => Bytecode::Tonumber(ic.one()),
                UnOp::ToNumeric => Bytecode::Tonumeric(ic.one()),
                UnOp::BitNot => Bytecode::Not(ic.one()), // vendored `not` IS bitwise (N39)
                UnOp::Void => Bytecode::Ldundefined,     // void x → undefined
                UnOp::IsTrue => Bytecode::Istrue,
                UnOp::IsFalse => Bytecode::Isfalse,
            };
            codes.push(bc);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::Mov { src } => {
            // Pure register copy: no accumulator involvement (vendor
            // `mov` is `acc: none`). Never produced by the lift (v0.1
            // has no Mov either); lowered for robustness.
            if let Some(v) = result {
                if used.contains(&v) {
                    let d = home_of(func_id, v, alloc)?;
                    let s = home_of(func_id, *src, alloc)?;
                    if s != d {
                        codes.push(Bytecode::Mov(Reg(d), Reg(s)));
                    }
                }
            }
        }

        // ── Object / Array creation ──────────────────────────────────
        Op::AllocObject { shape } => {
            match module.consts.get(*shape) {
                Some(Const::ObjectLiteral { keys, values })
                    if keys.is_empty() && values.is_empty() =>
                {
                    // The lift's shared empty shape: createemptyobject.
                    codes.push(Bytecode::Createemptyobject);
                }
                Some(Const::ObjectLiteral { .. }) | Some(Const::ArrayLiteral(_)) => {
                    // Vendor createobjectwithbuffer: the OBJECT tag is
                    // op-carried (N60) — the shape is the flat literal
                    // buffer content ([k0, v0, ...] as a Const tree).
                    codes.push(Bytecode::Createobjectwithbuffer(
                        ic.one(),
                        tracer.literal_eid(*shape),
                    ));
                }
                _ => {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: format!(
                            "AllocObject shape {shape} is not a literal object/array shape"
                        ),
                    });
                }
            }
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::AllocArray { shape } => {
            match shape {
                None => {
                    codes.push(Bytecode::Createemptyarray(ic.one()));
                }
                Some(shape) => {
                    // Vendor createarraywithbuffer (N60: the ARRAY tag is
                    // op-carried).
                    codes.push(Bytecode::Createarraywithbuffer(
                        ic.one(),
                        tracer.literal_eid(*shape),
                    ));
                }
            }
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::AllocRegExp { pattern, flags } => {
            codes.push(Bytecode::Createregexpwithliteral(
                ic.one(),
                tracer.eid(*pattern),
                Imm(i64::from(*flags)),
            ));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::AllocClosure { func } => {
            // Fusion (compare.rs rule 3): an adjacent single-use
            // `DefineFunc` is suppressed; emit vendor definefunc (the
            // closure-creation bytecode) and home the CLOSURE's value.
            // Non-fused shapes never come from the lift: a bare
            // `DefineFunc` (result used elsewhere) already materialized
            // the function object, so the closure is a register copy.
            if suppression.values.contains(func) {
                // Fused: the DefineFunc was suppressed — emit definefunc.
                let Some(ValueDef::Inst(fiid)) = module.value(*func).map(|v| v.def) else {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: "AllocClosure of a non-instruction value".into(),
                    });
                };
                let Some(finst) = module.inst(fiid) else {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: "AllocClosure of a dangling DefineFunc".into(),
                    });
                };
                let Op::DefineFunc { body, length, .. } = &finst.op else {
                    return Err(LowerError::UnsupportedInstruction {
                        func: func_id,
                        message: "AllocClosure of a non-DefineFunc value".into(),
                    });
                };
                codes.push(Bytecode::Definefunc(
                    ic.one(),
                    tracer.method_eid(*body),
                    Imm(i64::from(*length)),
                ));
                home_result(tracker, result, used, func_id, alloc, codes)?;
            } else if let Some(v) = result {
                // Robustness fallback (never from the lift): the
                // function object already exists; the closure is a copy.
                if used.contains(&v) {
                    let d = home_of(func_id, v, alloc)?;
                    let s = home_of(func_id, *func, alloc)?;
                    if s != d {
                        codes.push(Bytecode::Mov(Reg(d), Reg(s)));
                    }
                }
            }
        }
        Op::CreateObjectWithExcludedKeys { obj, keys } => {
            // Vendor `createobjectwithexcludedkeys imm:u8, v1:in:top,
            // v2:in:top, acc: out:top` with `properties: [range_1]`
            // (isa.yaml:494-498): v2 is the START of a CONSECUTIVE
            // register range holding the `imm` keys. Regalloc never
            // guarantees consecutiveness (N4 class), so the keys are
            // mov-filled into the reserved per-function window — the
            // SAME window the range calls use (each fill+use sequence
            // completes within this instruction's selection;
            // `range_call_window_size` takes the max over both kinds of
            // site, N9). Width selection follows the S2 rule: ≤ 255 keys
            // keep the narrow form; 256..=65535 select
            // `wide.createobjectwithexcludedkeys` (u16 count, isa.yaml
            // :499-504); above u16::MAX, `fill_call_window` hard-errors
            // (CallArgcOverflow). The window base fits the u8 start
            // operand of BOTH forms (CallWindowOverflow otherwise).
            let regs = materialize_operands(tracker, func_id, &[*obj], None, alloc, codes)?;
            let obj_r = regs[0];
            let start_r = fill_call_window(func_id, keys, alloc, codes)?;
            let count = Imm(keys.len() as i64);
            let bc = if keys.len() <= 255 {
                Bytecode::Createobjectwithexcludedkeys(count, obj_r, start_r)
            } else {
                Bytecode::WideCreateobjectwithexcludedkeys(count, obj_r, start_r)
            };
            codes.push(bc);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::SetObjectWithProto { proto, obj } => {
            // Vendor `setobjectwithproto imm:u16, v:in:top, acc: in:top`
            // (isa.yaml:1333-1337): proto in the register operand, the
            // object in the accumulator; two-slot IC. Both the modern
            // source form and the folded deprecated form emit this
            // modern opcode.
            let regs = materialize_operands(tracker, func_id, &[*proto], Some(*obj), alloc, codes)?;
            codes.push(Bytecode::Setobjectwithproto(ic.two(), regs[0]));
        }

        // ── Property access ──────────────────────────────────────────
        Op::LoadProp { object, name } => {
            ensure_acc(tracker, func_id, *object, alloc, codes)?;
            codes.push(Bytecode::Ldobjbyname(ic.two(), tracer.eid(*name)));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::StoreProp {
            object,
            name,
            value,
        } => {
            // (N59 transitional state: own-store sources — stownbyname,
            // definefieldbyname, definepropertybyname — also lift here;
            // a reported IR gap. P2c's `Op::StoreOwnPropName` takes that
            // arm.)
            let regs =
                materialize_operands(tracker, func_id, &[*object], Some(*value), alloc, codes)?;
            codes.push(Bytecode::Stobjbyname(ic.two(), tracer.eid(*name), regs[0]));
        }
        Op::LoadPropDyn { object, key } => {
            let regs =
                materialize_operands(tracker, func_id, &[*object], Some(*key), alloc, codes)?;
            codes.push(Bytecode::Ldobjbyvalue(ic.two(), regs[0]));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::StorePropDyn { object, key, value } => {
            // Vendor `stobjbyvalue imm:u16, v1:in:top, v2:in:top,
            // acc: in:top` (isa.yaml:1353-1357): v1 = receiver, v2 =
            // propKey, acc = VALUE. Register operands first, then
            // the acc operand (B3 ordering).
            let regs = materialize_operands(
                tracker,
                func_id,
                &[*object, *key],
                Some(*value),
                alloc,
                codes,
            )?;
            codes.push(Bytecode::Stobjbyvalue(ic.two(), regs[0], regs[1]));
        }
        Op::LoadPropIdx { object, index } => {
            let Some(imm) = fused_index_imm(module, *index, suppression) else {
                return Err(LowerError::UnsupportedInstruction {
                    func: func_id,
                    message: "LoadPropIdx with a non-constant index has no by-index \
                         encoding (the ISA's ldobjbyindex takes a compile-time immediate)"
                        .into(),
                });
            };
            ensure_acc(tracker, func_id, *object, alloc, codes)?;
            codes.push(Bytecode::Ldobjbyindex(ic.two(), imm));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::StorePropIdx {
            object,
            index,
            value,
        } => {
            let Some(imm) = fused_index_imm(module, *index, suppression) else {
                return Err(LowerError::UnsupportedInstruction {
                    func: func_id,
                    message: "StorePropIdx with a non-constant index has no by-index \
                         encoding (the ISA's stobjbyindex takes a compile-time immediate)"
                        .into(),
                });
            };
            let regs =
                materialize_operands(tracker, func_id, &[*object], Some(*value), alloc, codes)?;
            codes.push(Bytecode::Stobjbyindex(ic.two(), regs[0], imm));
        }
        Op::StoreOwnPropName {
            object,
            name,
            value,
        } => {
            // Own-property DEFINITION (N60; v0.1 `StoreOwnProperty`):
            // vendor stownbyname — no setters, no prototype walk.
            let regs =
                materialize_operands(tracker, func_id, &[*object], Some(*value), alloc, codes)?;
            codes.push(Bytecode::Stownbyname(ic.two(), tracer.eid(*name), regs[0]));
        }
        Op::StoreOwnPropDyn { object, key, value } => {
            // Vendor stownbyvalue (v0.1 `StoreOwnProperty` ByValue):
            // v1 = receiver, v2 = propKey, acc = VALUE.
            let regs = materialize_operands(
                tracker,
                func_id,
                &[*object, *key],
                Some(*value),
                alloc,
                codes,
            )?;
            codes.push(Bytecode::Stownbyvalue(ic.two(), regs[0], regs[1]));
        }
        Op::StoreOwnPropIdx {
            object,
            index,
            value,
        } => {
            let Some(imm) = fused_index_imm(module, *index, suppression) else {
                return Err(LowerError::UnsupportedInstruction {
                    func: func_id,
                    message: "StoreOwnPropIdx with a non-constant index has no by-index \
                         encoding (the ISA's stownbyindex takes a compile-time immediate)"
                        .into(),
                });
            };
            let regs =
                materialize_operands(tracker, func_id, &[*object], Some(*value), alloc, codes)?;
            codes.push(Bytecode::Stownbyindex(ic.two(), regs[0], imm));
        }
        Op::DeleteProp { object, key } => {
            let regs =
                materialize_operands(tracker, func_id, &[*key], Some(*object), alloc, codes)?;
            codes.push(Bytecode::Delobjprop(regs[0]));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::TestProp { .. } => {
            return Err(LowerError::UnsupportedInstruction {
                func: func_id,
                message: "TestProp has no v0.1 lowering equivalent (never produced by \
                     the lift; the `in` family lowers through Compare)"
                    .into(),
            });
        }
        Op::CopyDataProps { dst, src } => {
            // Vendor `copydataproperties v:in:top, acc: inout:top`: the
            // register operand is the target, the accumulator carries the
            // source (and receives the result). dst is resolved to its
            // home first, then src is brought into acc (tracker-aware).
            // No entity operands — nothing for the tracer/relocation
            // channel. The bytecode writes acc but the IR instruction has
            // no result, so the acc content is afterwards untracked.
            let regs = materialize_operands(tracker, func_id, &[*dst], Some(*src), alloc, codes)?;
            codes.push(Bytecode::Copydataproperties(regs[0]));
            *tracker = AccContent::Unknown;
        }
        Op::ArraySpread { dst, index, src } => {
            // Vendor `starrayspread v1:in:top, v2:in:top, acc: inout:top`
            // (isa.yaml:1329-1332): v1 = destination array, v2 = start
            // index, acc = source iterable; acc out = the NEW INDEX (the
            // IR result). Register operands first, then the acc operand
            // (B3 ordering); the result is homed per `acc: inout`.
            let regs =
                materialize_operands(tracker, func_id, &[*dst, *index], Some(*src), alloc, codes)?;
            codes.push(Bytecode::Starrayspread(regs[0], regs[1]));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }

        // ── Private properties ───────────────────────────────────────
        Op::LoadPrivate { level, slot, obj } => {
            // Vendor `ldprivateproperty imm1:u8, imm2:u16, imm3:u16,
            // acc: inout:top` (isa.yaml:436-440, two_slot): acc in =
            // the object, acc out = the private value.
            ensure_acc(tracker, func_id, *obj, alloc, codes)?;
            codes.push(Bytecode::Ldprivateproperty(
                ic.two(),
                Imm(*level as i64),
                Imm(*slot as i64),
            ));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::StorePrivate {
            level,
            slot,
            obj,
            value,
        } => {
            // Vendor `stprivateproperty imm1, imm2, imm3, v:in:top,
            // acc: in:top` (isa.yaml:441-445, two_slot): obj = register
            // operand, value = acc. The bytecode only READS acc — the
            // tracker is untouched.
            let regs = materialize_operands(tracker, func_id, &[*obj], Some(*value), alloc, codes)?;
            codes.push(Bytecode::Stprivateproperty(
                ic.two(),
                Imm(*level as i64),
                Imm(*slot as i64),
                regs[0],
            ));
        }
        Op::DefinePrivate {
            level,
            slot,
            obj,
            value,
        } => {
            // Vendor `callruntime.defineprivateproperty imm1, imm2,
            // imm3, v:in:top, acc: in:top` (isa.yaml:849-854,
            // two_slot): obj = register operand, value = acc. acc
            // read-only — the tracker is untouched.
            let regs = materialize_operands(tracker, func_id, &[*obj], Some(*value), alloc, codes)?;
            codes.push(Bytecode::CallruntimeDefineprivateproperty(
                ic.two(),
                Imm(*level as i64),
                Imm(*slot as i64),
                regs[0],
            ));
        }
        Op::TestPrivate { level, slot, obj } => {
            // Vendor `testin imm1:u8, imm2:u16, imm3:u16,
            // acc: inout:top` (isa.yaml:446-450, two_slot): acc in =
            // the object, acc out = the boolean result.
            ensure_acc(tracker, func_id, *obj, alloc, codes)?;
            codes.push(Bytecode::Testin(
                ic.two(),
                Imm(*level as i64),
                Imm(*slot as i64),
            ));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::CreatePrivateNames { count, names } => {
            // Vendor `callruntime.createprivateproperty imm:u16,
            // literalarray_id, acc: none` (isa.yaml:843-848): no acc
            // effect — the tracker is untouched.
            codes.push(Bytecode::CallruntimeCreateprivateproperty(
                Imm(*count as i64),
                tracer.literal_eid(*names),
            ));
        }
        Op::LoadSuper { key } => {
            match key {
                SuperKey::Name(name) => {
                    codes.push(Bytecode::Ldsuperbyname(ic.two(), tracer.eid(*name)));
                }
                SuperKey::Dynamic(k) => {
                    let key_r = val_reg(func_id, *k, alloc, codes, 0)?;
                    codes.push(Bytecode::Ldsuperbyvalue(ic.two(), key_r));
                }
            }
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::StoreSuper { key, value } => match key {
            SuperKey::Name(name) => {
                let val_r = val_reg(func_id, *value, alloc, codes, 0)?;
                codes.push(Bytecode::Stsuperbyname(ic.two(), tracer.eid(*name), val_r));
            }
            SuperKey::Dynamic(k) => {
                let regs =
                    materialize_operands(tracker, func_id, &[*k, *value], None, alloc, codes)?;
                codes.push(Bytecode::Stsuperbyvalue(ic.two(), regs[0], regs[1]));
            }
        },

        // ── Global variables ─────────────────────────────────────────
        Op::TryGetGlobal { name, default } => {
            match default {
                None => {
                    // The THROWING form: ldglobalvar.
                    codes.push(Bytecode::Ldglobalvar(ic.one(), tracer.eid(*name)));
                }
                Some(dflt) => {
                    // The tolerant form: the default must be the fused
                    // `LoadConst(undefined)` (suppressed — or the shared
                    // frame-initial undefined constant), else there is no
                    // vendor encoding.
                    let fused = suppression.values.contains(dflt)
                        || matches!(
                            module.value(*dflt).map(|v| v.def),
                            Some(ValueDef::Const(cid))
                                if matches!(module.consts.get(cid), Some(Const::Undefined))
                        );
                    if !fused {
                        return Err(LowerError::UnsupportedInstruction {
                            func: func_id,
                            message: "TryGetGlobal with a non-undefined default has no \
                                 vendor encoding (tryldglobalbyname's fallback is undefined)"
                                .into(),
                        });
                    }
                    codes.push(Bytecode::Tryldglobalbyname(ic.one(), tracer.eid(*name)));
                }
            }
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::StoreGlobal { name, value } => {
            ensure_acc(tracker, func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Stglobalvar(ic.one(), tracer.eid(*name)));
        }
        Op::TryStoreGlobal { name, value } => {
            // The tolerant store (N61; v0.1 `TryStoreGlobalByName`):
            // acc := value, then trystglobalbyname with ONE IC slot.
            ensure_acc(tracker, func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Trystglobalbyname(ic.one(), tracer.eid(*name)));
        }

        // ── Lexical variables ────────────────────────────────────────
        Op::GetLexVar { level, slot } => {
            codes.push(Bytecode::Ldlexvar(Imm(*level as i64), Imm(*slot as i64)));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::PutLexVar { level, slot, value } => {
            ensure_acc(tracker, func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Stlexvar(Imm(*level as i64), Imm(*slot as i64)));
        }
        Op::NewLexEnv { num_vars } => {
            codes.push(Bytecode::Newlexenv(Imm(*num_vars as i64)));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::NewLexEnvWithName {
            num_vars,
            scope_names,
        } => {
            codes.push(Bytecode::Newlexenvwithname(
                Imm(*num_vars as i64),
                tracer.literal_eid(*scope_names),
            ));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::PopLexEnv => {
            codes.push(Bytecode::Poplexenv);
        }

        // ── Module variables ─────────────────────────────────────────
        Op::LoadModuleVar { index } => {
            codes.push(Bytecode::Ldlocalmodulevar(Imm(*index as i64)));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::StoreModuleVar { index, value } => {
            ensure_acc(tracker, func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Stmodulevar(Imm(*index as i64)));
        }
        Op::GetModuleNamespace { index } => {
            codes.push(Bytecode::Getmodulenamespace(Imm(*index as i64)));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::DynamicImport { specifier } => {
            ensure_acc(tracker, func_id, *specifier, alloc, codes)?;
            codes.push(Bytecode::Dynamicimport);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }

        // ── Function / Class definition ──────────────────────────────
        Op::DefineFunc {
            body,
            captures,
            length,
        } => {
            // A standalone DefineFunc (never produced by the lift except
            // fused into AllocClosure/DefineMethod — then it is
            // suppressed): vendor definefunc IS the closure creation.
            if !captures.is_empty() {
                return Err(LowerError::UnsupportedInstruction {
                    func: func_id,
                    message: "DefineFunc with explicit captures has no vendor encoding \
                         (es2abc closure captures are lexenv-based)"
                        .into(),
                });
            }
            codes.push(Bytecode::Definefunc(
                ic.one(),
                tracer.method_eid(*body),
                Imm(i64::from(*length)),
            ));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::DefineMethod {
            object,
            func,
            length,
            ..
        } => {
            // Fusion: the DefineFunc+AllocClosure chain is suppressed;
            // emit vendor definemethod (define + bind in one), like
            // v0.1's DefineMethod arm. The method's entity identity is
            // the DefineFunc body's function-table index.
            let Some(body) = fused_definefunc_body(module, *func, suppression) else {
                return Err(LowerError::UnsupportedInstruction {
                    func: func_id,
                    message: "DefineMethod of a non-fused closure (expected the lift's \
                         DefineFunc + AllocClosure chain)"
                        .into(),
                });
            };
            ensure_acc(tracker, func_id, *object, alloc, codes)?;
            codes.push(Bytecode::Definemethod(
                ic.one(),
                tracer.method_eid(body),
                Imm(i64::from(*length)),
            ));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::DefineClass {
            ctor,
            heritage,
            members,
            count,
        } => {
            let Some(base) = heritage else {
                return Err(LowerError::UnsupportedInstruction {
                    func: func_id,
                    message: "DefineClass without a heritage register has no \
                         defineclasswithbuffer encoding"
                        .into(),
                });
            };
            let base_r = val_reg(func_id, *base, alloc, codes, 0)?;
            codes.push(Bytecode::Defineclasswithbuffer(
                ic.one(),
                tracer.method_eid(*ctor),
                tracer.literal_eid(*members),
                // Vendor imm2 (_count): consumed by the runtime as the
                // constructor's .length (RuntimeSetClassConstructorLength).
                Imm(i64::from(*count)),
                base_r,
            ));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::DefineGetterSetterByValue {
            obj,
            key,
            getter,
            setter,
        } => {
            let regs = materialize_operands(
                tracker,
                func_id,
                &[*obj, *key, *getter, *setter],
                None,
                alloc,
                codes,
            )?;
            codes.push(Bytecode::Definegettersetterbyvalue(
                regs[0], regs[1], regs[2], regs[3],
            ));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }

        // ── Calls ────────────────────────────────────────────────────
        Op::Call {
            callee,
            this,
            args,
            kind,
        } => {
            select_call(
                *kind, *callee, *this, args, func_id, alloc, codes, ic, tracker,
            )?;
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }

        // ── Special value loaders ────────────────────────────────────
        Op::LoadNewTarget => {
            codes.push(Bytecode::Ldnewtarget);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::LoadGlobalObject => {
            codes.push(Bytecode::Ldglobal);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::LoadFunction => {
            codes.push(Bytecode::Ldfunction);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::GetUnmappedArgs => {
            codes.push(Bytecode::Getunmappedargs);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::CopyRestArgs { start_index } => {
            codes.push(Bytecode::Copyrestargs(Imm(*start_index as i64)));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::GetTemplateObject { literal } => {
            // Vendor `gettemplateobject imm:u16, acc: inout:top`
            // (isa.yaml:1279-1283): ONE IC slot (`one_slot`); acc in =
            // the template literal, acc out = the cached template
            // object.
            ensure_acc(tracker, func_id, *literal, alloc, codes)?;
            codes.push(Bytecode::Gettemplateobject(ic.one()));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }

        // ── Iterators ────────────────────────────────────────────────
        Op::GetIterator { obj } => {
            ensure_acc(tracker, func_id, *obj, alloc, codes)?;
            codes.push(Bytecode::Getiterator(ic.two()));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::GetAsyncIterator { obj } => {
            ensure_acc(tracker, func_id, *obj, alloc, codes)?;
            codes.push(Bytecode::Getasynciterator(ic.two()));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::GetPropIterator { obj } => {
            ensure_acc(tracker, func_id, *obj, alloc, codes)?;
            codes.push(Bytecode::Getpropiterator);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::IteratorNext { .. } | Op::IteratorThrow { .. } => {
            return Err(LowerError::UnsupportedInstruction {
                func: func_id,
                message: "IteratorNext/IteratorThrow has no v0.1 lowering equivalent \
                     (never produced by the lift)"
                    .into(),
            });
        }
        Op::IteratorReturn { iterator } => {
            // v0.1's CloseIterator → closeiterator.
            let iter_r = val_reg(func_id, *iterator, alloc, codes, 0)?;
            codes.push(Bytecode::Closeiterator(ic.two(), iter_r));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::NextPropName { iterator } => {
            // Vendor `getnextpropname v:in:top, acc: out:top`
            // (isa.yaml:1289-1292): the iterator is a REGISTER operand
            // (materialized from its home), the result name goes to acc.
            let iter_r = val_reg(func_id, *iterator, alloc, codes, 0)?;
            codes.push(Bytecode::Getnextpropname(iter_r));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }

        // ── Generator / Async ────────────────────────────────────────
        Op::CreateGenerator { func } => {
            let func_r = val_reg(func_id, *func, alloc, codes, 0)?;
            codes.push(Bytecode::Creategeneratorobj(func_r));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::SuspendGenerator { genobj, value } => {
            // Vendor `suspendgenerator v:in:top, acc: inout:top`
            // (isa.yaml:1302-1305): the register operand is the generator
            // object, the acc carries the yield value (and receives the
            // resume result).
            let regs =
                materialize_operands(tracker, func_id, &[*genobj], Some(*value), alloc, codes)?;
            codes.push(Bytecode::Suspendgenerator(regs[0]));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::ResumeGenerator { genobj } => {
            // Vendor `resumegenerator` (isa.yaml:1261-1264):
            // `acc: inout:top`, no register operand — genobj in acc,
            // resume result back to acc.
            ensure_acc(tracker, func_id, *genobj, alloc, codes)?;
            codes.push(Bytecode::Resumegenerator);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::GetResumeMode { genobj } => {
            // Vendor `getresumemode` (isa.yaml:1270-1273):
            // `acc: inout:top`, no register operand — genobj in acc,
            // resume mode back to acc.
            ensure_acc(tracker, func_id, *genobj, alloc, codes)?;
            codes.push(Bytecode::Getresumemode);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::Await { .. } => {
            return Err(LowerError::UnsupportedInstruction {
                func: func_id,
                message: "Await has no v0.1 lowering equivalent (es2abc's await form is \
                     asyncfunctionawaituncaught — Op::AwaitUncaught)"
                    .into(),
            });
        }
        Op::AwaitUncaught { value } => {
            let val_r = val_reg(func_id, *value, alloc, codes, 0)?;
            codes.push(Bytecode::Asyncfunctionawaituncaught(val_r));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::AsyncFunctionEnter => {
            codes.push(Bytecode::Asyncfunctionenter);
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::AsyncResolve { value } => {
            let val_r = val_reg(func_id, *value, alloc, codes, 0)?;
            codes.push(Bytecode::Asyncfunctionresolve(val_r));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::AsyncReject { value } => {
            let val_r = val_reg(func_id, *value, alloc, codes, 0)?;
            codes.push(Bytecode::Asyncfunctionreject(val_r));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }
        Op::CreateIterResultObj { value, done } => {
            let regs =
                materialize_operands(tracker, func_id, &[*value, *done], None, alloc, codes)?;
            codes.push(Bytecode::Createiterresultobj(regs[0], regs[1]));
            home_result(tracker, result, used, func_id, alloc, codes)?;
        }

        // ── Exception handling ───────────────────────────────────────
        Op::Throw { value } => {
            ensure_acc(tracker, func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Throw);
        }
        Op::ThrowIfNotObject { value } => {
            let val_r = val_reg(func_id, *value, alloc, codes, 0)?;
            codes.push(Bytecode::ThrowIfnotobject(val_r));
        }
        Op::ThrowConstAssignment { name } => {
            // Vendor `throw.constassignment v:in:top, acc: none`
            // (isa.yaml:987-991): the register operand carries the name
            // VALUE. No accumulator traffic.
            let name_r = val_reg(func_id, *name, alloc, codes, 0)?;
            codes.push(Bytecode::ThrowConstassignment(name_r));
        }
        Op::ThrowUndefinedIfHole { name, value } => {
            // Vendor `throw.undefinedifhole v1:in:top, v2:in:top,
            // acc: none` (isa.yaml:998-1002): v1 = name value, v2 =
            // checked value; no accumulator traffic.
            let regs =
                materialize_operands(tracker, func_id, &[*name, *value], None, alloc, codes)?;
            codes.push(Bytecode::ThrowUndefinedifhole(regs[0], regs[1]));
        }
        Op::ThrowUndefinedIfHoleWithName { name, value } => {
            // Vendor `throw.undefinedifholewithname string_id,
            // acc: in:top` (isa.yaml:1010-1015): the checked value rides
            // the accumulator, the name is a compile-time string id.
            ensure_acc(tracker, func_id, *value, alloc, codes)?;
            codes.push(Bytecode::ThrowUndefinedifholewithname(tracer.eid(*name)));
        }
        Op::ThrowIfSuperNotCalled { value, kind } => {
            // Vendor `throw.ifsupernotcorrectcall imm:u16, acc: in:top`
            // (isa.yaml:1003-1008): the checked `this` value rides the
            // accumulator; imm is the check kind.
            let k = match kind {
                SuperCheck::NotCalled => 0,
                SuperCheck::Rebind => 1,
            };
            ensure_acc(tracker, func_id, *value, alloc, codes)?;
            codes.push(Bytecode::ThrowIfsupernotcorrectcall(Imm(k)));
        }
        Op::ThrowNotExists => {
            codes.push(Bytecode::ThrowNotexists);
        }
        Op::ThrowPatternNonCoercible => {
            codes.push(Bytecode::ThrowPatternnoncoercible);
        }
        Op::ThrowDeleteSuperProperty => {
            codes.push(Bytecode::ThrowDeletesuperproperty);
        }

        // ── Terminators ──────────────────────────────────────────────
        // Branch/CondBranch are handled in layout.rs (jump target resolution).
        // We emit placeholder labels here; layout will fix them.
        Op::Branch { dest } => {
            codes.push(Bytecode::Jmp(Label(dest.0)));
        }
        Op::CondBranch {
            cond,
            true_dest,
            false_dest,
        } => {
            // Try compare-branch fusion: if cond is IsTrue(CmpOp(a, b)),
            // emit a fused Jeq/Jne/Jstricteq/Jnstricteq instead of Jnez.
            // Fusion re-reads the COMPARISON's operands at this branch, so
            // it fires only when that re-read is provably sound (S6; see
            // try_fuse_cmp_branch). Otherwise fall back to the unfused
            // path, which is sound: `cond` is the branch's own operand and
            // the tracker reloads it from its home unless the acc provably
            // still holds it (the common def→use chain).
            if let Some(fused) = try_fuse_cmp_branch(
                *cond,
                *true_dest,
                inst,
                block_insts,
                func_id,
                module,
                alloc,
                codes,
                tracker,
            )? {
                codes.push(fused);
            } else {
                ensure_acc(tracker, func_id, *cond, alloc, codes)?;
                // Emit: if acc truthy → jump to true_dest, fall through to false_dest
                codes.push(Bytecode::Jnez(Label(true_dest.0)));
            }
            // The fall-through to false_dest is implicit if it's the next block.
            // Layout will insert a Jmp if needed.
            let _ = false_dest;
        }
        Op::Return { value } => {
            if let Some(val) = value {
                ensure_acc(tracker, func_id, *val, alloc, codes)?;
                codes.push(Bytecode::Return);
            } else {
                codes.push(Bytecode::Returnundefined);
            }
        }
        Op::Unreachable => {
            codes.push(Bytecode::Returnundefined);
        }

        // ── Phi / Debug ──────────────────────────────────────────────
        Op::Phi { .. } => {
            // Handled by phi elimination, not emitted directly.
        }
        Op::Debugger => {
            codes.push(Bytecode::Debugger);
        }
    }
    Ok(())
}

/// Select call bytecodes based on kind and argument count.
///
/// Every arm materializes operands the same way: the argument registers
/// are resolved to their homes first (pure reads, plus scratch `mov`s for
/// high homes), then the callee is brought into the acc (tracker-aware).
///
/// v0.2's single `Call` op maps back onto the vendor families per the §5.3
/// binding table: `Dynamic`/`Direct` (never produced by the lift — treated
/// identically) with `this: None` → callarg*/callrange, with `this:
/// Some` → callthis*/callthisrange (v0.1's CallThis); `Super` → the
/// supercall*range family; `New` → newobjrange.
#[allow(clippy::too_many_arguments)]
fn select_call(
    kind: CallKind,
    callee: ValueId,
    this: Option<ValueId>,
    args: &[ValueId],
    func_id: FuncId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
    ic: &mut IcAllocator,
    tracker: &mut AccContent,
) -> Result<(), LowerError> {
    match kind {
        CallKind::Dynamic | CallKind::Direct => match this {
            None => match args.len() {
                0 => {
                    materialize_operands(tracker, func_id, &[], Some(callee), alloc, codes)?;
                    codes.push(Bytecode::Callarg0(ic.two()));
                }
                n @ (1..=3) => {
                    let regs =
                        materialize_operands(tracker, func_id, args, Some(callee), alloc, codes)?;
                    let bc = match n {
                        1 => Bytecode::Callarg1(ic.two(), regs[0]),
                        2 => Bytecode::Callargs2(ic.two(), regs[0], regs[1]),
                        _ => Bytecode::Callargs3(ic.two(), regs[0], regs[1], regs[2]),
                    };
                    codes.push(bc);
                }
                _ => emit_range_call(
                    RangeForm::Call,
                    callee,
                    args,
                    func_id,
                    alloc,
                    codes,
                    ic,
                    tracker,
                )?,
            },
            Some(this_val) => {
                // v0.1's CallThis: the window/operand list is [this, args...].
                // (N57 transitional state: `apply` sources also lift to
                // this exact shape — a reported IR gap. P2c's
                // `CallKind::Apply` takes that arm; the 1-arg shape then
                // unambiguously means callthis1.)
                let mut values = Vec::with_capacity(args.len() + 1);
                values.push(this_val);
                values.extend_from_slice(args);
                match values.len() {
                    n @ (1..=4) => {
                        let regs = materialize_operands(
                            tracker,
                            func_id,
                            &values,
                            Some(callee),
                            alloc,
                            codes,
                        )?;
                        let bc = match n {
                            1 => Bytecode::Callthis0(ic.two(), regs[0]),
                            2 => Bytecode::Callthis1(ic.two(), regs[0], regs[1]),
                            3 => Bytecode::Callthis2(ic.two(), regs[0], regs[1], regs[2]),
                            _ => Bytecode::Callthis3(ic.two(), regs[0], regs[1], regs[2], regs[3]),
                        };
                        codes.push(bc);
                    }
                    _ => emit_range_call(
                        RangeForm::CallThis,
                        callee,
                        &values,
                        func_id,
                        alloc,
                        codes,
                        ic,
                        tracker,
                    )?,
                }
            }
        },
        CallKind::Super => {
            // v0.1's SuperCall → supercallthisrange (an explicit-arguments
            // super call). Corpus supercallthisrange is always argc=0.
            emit_range_call(
                RangeForm::SuperCallThis,
                callee,
                args,
                func_id,
                alloc,
                codes,
                ic,
                tracker,
            )?;
        }
        CallKind::Apply => {
            // Vendor `apply imm:u8, v1:in:top, v2:in:top` (isa.yaml:1104):
            // func = acc, this = v1, args array = v2 — exactly one
            // receiver and one array (N16/N57; v0.1's Apply arm).
            let (Some(this_val), [array]) = (this, args) else {
                return Err(LowerError::UnsupportedInstruction {
                    func: func_id,
                    message: format!(
                        "apply requires exactly (this, args array), got this={} args={}",
                        this.is_some(),
                        args.len()
                    ),
                });
            };
            let regs = materialize_operands(
                tracker,
                func_id,
                &[this_val, *array],
                Some(callee),
                alloc,
                codes,
            )?;
            codes.push(Bytecode::Apply(ic.two(), regs[0], regs[1]));
        }
        CallKind::SuperSpread => {
            // Vendor `supercallspread imm:u8, v:in:top` — the spread array
            // is the register operand, the callee rides the acc (v0.1's
            // SuperCallSpread arm).
            let regs = materialize_operands(
                tracker,
                func_id,
                &args[..1.min(args.len())],
                Some(callee),
                alloc,
                codes,
            )?;
            let arg_r = if args.is_empty() { Reg(0) } else { regs[0] };
            codes.push(Bytecode::Supercallspread(ic.two(), arg_r));
        }
        CallKind::SuperForwardAllArgs => {
            // v0.1's representation kept verbatim (N58): a default derived
            // constructor forwarding all args lowers through the
            // supercallthisrange form with the window holding the
            // forwarded args (args = [this] at the lift).
            emit_range_call(
                RangeForm::SuperCallThis,
                callee,
                args,
                func_id,
                alloc,
                codes,
                ic,
                tracker,
            )?;
        }
        CallKind::New => {
            emit_construct(callee, args, func_id, alloc, codes, ic)?;
        }
    }
    Ok(())
}

/// The range-call families and their narrow/wide bytecode forms. Vendor
/// (isa.yaml ~:1082-1167): narrow `*range imm1:u8, imm2:u8, v:in:top`
/// (imm1 = IC slot, imm2 = argc, v = window start); wide
/// `wide.*range imm:u16, v:in:top` (imm = argc, v = window start — STILL
/// u8, and NO IC slot operand on the wide forms).
#[derive(Clone, Copy)]
enum RangeForm {
    Call,
    CallThis,
    SuperCallThis,
}

/// Emit a range-form call: copy the arguments into the reserved consecutive
/// per-function window (`RegAlloc::call_window_base`) in call order, then
/// encode the call with the window base as the start register.
///
/// This replaces the historical "args are assumed consecutive from
/// val_reg(args[0])" approximation (N4): regalloc never guaranteed
/// consecutiveness, so the window copy is the only sound encoding. The
/// window registers are scratch — dead before and after the fill+call
/// sequence; sites share one per-function window because each sequence
/// completes before the next instruction is emitted, including nested
/// calls (the inner call's fill+call is fully emitted inside its own
/// instruction's selection before the outer call's fill begins).
///
/// Width selection: argc ≤ 255 keeps the narrow form (with IC slot); argc
/// in 256..=65535 selects the wide form (u16 argc, no IC slot consumed);
/// argc above u16::MAX is a hard error — nothing is silently truncated.
/// The window base must fit the u8 start operand of BOTH forms; regalloc
/// guarantees this for allocations it produced, and hand-crafted
/// allocations are hard-errored here.
#[allow(clippy::too_many_arguments)]
fn emit_range_call(
    form: RangeForm,
    callee: ValueId,
    args: &[ValueId],
    func_id: FuncId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
    ic: &mut IcAllocator,
    tracker: &mut AccContent,
) -> Result<(), LowerError> {
    let start = fill_call_window(func_id, args, alloc, codes)?;

    ensure_acc(tracker, func_id, callee, alloc, codes)?;

    let argc = args.len();
    let argc_imm = Imm(argc as i64);
    let bc = match (form, argc <= 255) {
        (RangeForm::Call, true) => Bytecode::Callrange(ic.two(), argc_imm, start),
        (RangeForm::Call, false) => Bytecode::WideCallrange(argc_imm, start),
        (RangeForm::CallThis, true) => Bytecode::Callthisrange(ic.two(), argc_imm, start),
        (RangeForm::CallThis, false) => Bytecode::WideCallthisrange(argc_imm, start),
        (RangeForm::SuperCallThis, true) => Bytecode::Supercallthisrange(ic.two(), argc_imm, start),
        (RangeForm::SuperCallThis, false) => Bytecode::WideSupercallthisrange(argc_imm, start),
    };
    codes.push(bc);
    Ok(())
}

/// Emit a construct call (`new callee(args...)`) — vendor
/// `newobjrange imm1:u16, imm2:u8, v:in:top` /
/// `wide.newobjrange imm:u16, v:in:top`
/// (abcd-isa-sys/vendor/isa/isa.yaml ~:535/:540).
///
/// The reserved consecutive window is filled [callee, args...] IN ORDER:
/// the runtime reads the constructor from the FIRST register of the range
/// and passes it as BOTH func and newTarget
/// (`SlowRuntimeStub::NewObjRange(thread, ctor, ctor, ...)`,
/// arkcompiler_ets_runtime-master/ecmascript/interpreter/interpreter-inl.cpp:4205),
/// and the encoded argc counts it (argc = args.len() + 1). Unlike the
/// plain-call range forms the accumulator is NOT an input (vendor
/// `acc: out:top`), so no `ensure_acc` is emitted for the callee.
///
/// Width selection inherits the S2 rule: argc+1 ≤ 255 keeps the narrow
/// form (with its two-slot IC); 256..=65535 selects the wide form (u16
/// argc, NO IC slot consumed — verified for newobjrange specifically:
/// isa.yaml ~:540 has no ic_slot property); argc+1 above u16::MAX, a
/// window base above 255, or a window end past the register space are the
/// same hard errors as the plain range calls (shared `fill_call_window`).
fn emit_construct(
    callee: ValueId,
    args: &[ValueId],
    func_id: FuncId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
    ic: &mut IcAllocator,
) -> Result<(), LowerError> {
    let mut window_values = Vec::with_capacity(args.len() + 1);
    window_values.push(callee);
    window_values.extend_from_slice(args);
    let start = fill_call_window(func_id, &window_values, alloc, codes)?;

    let argc = window_values.len();
    let argc_imm = Imm(argc as i64);
    let bc = if argc <= 255 {
        Bytecode::Newobjrange(ic.two(), argc_imm, start)
    } else {
        Bytecode::WideNewobjrange(argc_imm, start)
    };
    codes.push(bc);
    Ok(())
}

/// Fill the reserved consecutive per-function call window
/// (`RegAlloc::call_window_base`) with `values` in order and return the
/// encoded start register. Shared by the plain range calls (values = the
/// arguments) and construct calls (values = [callee, args...]).
///
/// An empty `values` encodes start = Reg(0): argc = 0 reads no argument
/// registers, so the start operand is dead and no window is needed (or
/// reserved) for the site.
///
/// Hard errors (S2 contract — nothing is silently truncated): argc above
/// u16::MAX (`CallArgcOverflow`), a window base above 255
/// (`CallWindowOverflow` — BOTH the narrow and the wide forms carry a u8
/// start operand), and a window end past the register space
/// (`RegisterOverflow`).
///
/// The fill is pure `mov`s from the values' register homes (every value
/// has one — B4), so it never touches the accumulator and needs no
/// tracker update (vendor `mov` is `acc: none`).
fn fill_call_window(
    func_id: FuncId,
    values: &[ValueId],
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<Reg, LowerError> {
    let argc = values.len();
    if argc > u16::MAX as usize {
        return Err(LowerError::CallArgcOverflow {
            func: func_id,
            argc,
        });
    }
    if argc == 0 {
        return Ok(Reg(0));
    }

    let base = alloc
        .call_window_base
        .ok_or(LowerError::MissingCallWindow(func_id))?;
    if base > 255 {
        return Err(LowerError::CallWindowOverflow(func_id));
    }
    if base as u32 + argc as u32 - 1 > u16::MAX as u32 {
        return Err(LowerError::RegisterOverflow(func_id));
    }
    // Fill the window in order. `mov` auto-widens to its v16 form,
    // so both the window slot (which may exceed 255) and the value's
    // colored home are always encodable.
    for (j, &val) in values.iter().enumerate() {
        let dst = Reg(base + j as u16);
        let r = home_of(func_id, val, alloc)?;
        codes.push(Bytecode::Mov(dst, Reg(r)));
    }
    Ok(Reg(base))
}

/// Try to fuse a compare + branch into a single bytecode.
///
/// Pattern: `CondBranch(cond: IsTrue(Compare { op: Eq|StrictEq|..., left, right }), true_dest)`
/// → `Jeq(right_reg, true_dest)` with left in acc.
///
/// Fusion re-reads the COMPARISON's operands (`left`, `right`) at the
/// branch site, extending their live ranges beyond what register
/// allocation computed: allocation lets them die at the comparison, and
/// the comparison plus the `IsTrue` wrapper both write the accumulator.
/// Fusing is therefore only sound when ALL of the following hold (S6):
///
/// 1. The comparison — and the `IsTrue` wrapper, if present — are the
///    instructions immediately preceding this branch IN THE SAME BLOCK.
///    Any instruction in between could reuse an operand slot whose live
///    range ended at the comparison.
/// 2. Both `left` and `right` are Reg-colored. Since B4 EVERY value is
///    Reg-colored, so this holds by construction — the operands are read
///    from their register homes, and the emission-time acc tracker makes
///    the fused `ensure_acc(left)` reload `left` from its home (the acc at
///    the branch provably holds `cond`, not `left`, so the tracker miss
///    is correct, never a stale no-op).
/// 3. Neither the comparison result nor the `IsTrue` result reuses an
///    operand's slot. An operand that dies at the comparison does not
///    interfere with those results, so the allocator may co-locate them;
///    the fused re-read would then observe the result, not the operand.
///
/// Returns `Ok(Some(fused_bytecode))` if fusion succeeded, `Ok(None)`
/// when any precondition fails — the caller then emits the unfused
/// `ensure_acc(cond)` + `Jnez` sequence.
#[allow(clippy::too_many_arguments)]
fn try_fuse_cmp_branch(
    cond: ValueId,
    true_dest: BlockId,
    branch_inst: InstId,
    block_insts: &[InstId],
    func_id: FuncId,
    module: &Module,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
    tracker: &mut AccContent,
) -> Result<Option<Bytecode>, LowerError> {
    let cond_inst = match module.value(cond).map(|v| v.def) {
        Some(ValueDef::Inst(i)) => i,
        _ => return Ok(None),
    };
    let Some(cond_node) = module.inst(cond_inst) else {
        return Ok(None);
    };

    // Unwrap the IsTrue wrapper: the comparison is the instruction whose
    // result feeds the branch, directly or through the wrapper.
    let (cmp_inst, wrapper) = match &cond_node.op {
        Op::UnaryOp {
            op: UnOp::IsTrue,
            operand,
        } => match module.value(*operand).map(|v| v.def) {
            Some(ValueDef::Inst(i)) => (i, Some(cond_inst)),
            _ => return Ok(None),
        },
        // If cond is directly a comparison (without IsTrue wrapper), also fuse.
        Op::Compare { .. } => (cond_inst, None),
        _ => return Ok(None),
    };
    let Some(cmp_node) = module.inst(cmp_inst) else {
        return Ok(None);
    };
    let Op::Compare { op, left, right } = &cmp_node.op else {
        return Ok(None);
    };

    // Precondition 1: same-block adjacency — the block's instruction tail
    // must be exactly [comparison, (IsTrue,) branch].
    let tail: &[InstId] = match wrapper {
        Some(w) => &[cmp_inst, w, branch_inst],
        None => &[cmp_inst, branch_inst],
    };
    if !block_insts.ends_with(tail) {
        return Ok(None);
    }

    // Precondition 2: both comparison operands Reg-colored.
    let (Some(RegSlot::Reg(left_r)), Some(RegSlot::Reg(right_r))) = (
        alloc.allocation.get(left).copied(),
        alloc.allocation.get(right).copied(),
    ) else {
        return Ok(None);
    };

    // Precondition 3: the comparison/IsTrue results (the only stores
    // between the comparison and the branch, by precondition 1) must not
    // occupy an operand slot.
    for result in [cmp_node.result, cond_node.result].into_iter().flatten() {
        if let Some(RegSlot::Reg(r)) = alloc.allocation.get(&result).copied() {
            if r == left_r || r == right_r {
                return Ok(None);
            }
        }
    }

    fuse_cmp_branch(
        *op, *left, *right, true_dest, func_id, alloc, codes, tracker,
    )
}

/// Emit a fused compare-branch for a CmpOp comparison.
///
/// The comparison's operands materialize like any two-operand instruction:
/// the register operand reads its home, then the acc operand loads
/// (tracker-aware). Soundness preconditions (adjacency, Reg-colored
/// operands, no result-slot sharing) are enforced by the caller,
/// `try_fuse_cmp_branch`.
#[allow(clippy::too_many_arguments)]
fn fuse_cmp_branch(
    op: CmpOp,
    left: ValueId,
    right: ValueId,
    true_dest: BlockId,
    func_id: FuncId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
    tracker: &mut AccContent,
) -> Result<Option<Bytecode>, LowerError> {
    // Only the Eq family has fused branch bytecodes in the ABC ISA; for
    // Less/Greater/etc there is nothing to fuse.
    if !matches!(
        op,
        CmpOp::Eq | CmpOp::NotEq | CmpOp::StrictEq | CmpOp::StrictNotEq
    ) {
        return Ok(None);
    }
    let label = Label(true_dest.0);
    let regs = materialize_operands(tracker, func_id, &[right], Some(left), alloc, codes)?;
    let r = regs[0];
    Ok(Some(match op {
        CmpOp::Eq => Bytecode::Jeq(r, label),
        CmpOp::NotEq => Bytecode::Jne(r, label),
        CmpOp::StrictEq => Bytecode::Jstricteq(r, label),
        // Only StrictNotEq remains (guarded above).
        _ => Bytecode::Jnstricteq(r, label),
    }))
}

#[cfg(test)]
mod tests {
    use super::{
        AccContent, LowerError, RegAlloc, RegSlot, ensure_acc, home_result, materialize_operands,
        val_reg,
    };
    use abcd_ir2::{FuncId, ValueId};
    use abcd_isa::{Bytecode, Reg};
    use std::collections::{HashMap, HashSet};

    const F: FuncId = FuncId(0);

    fn alloc_with(slots: &[(ValueId, u16)]) -> RegAlloc {
        RegAlloc {
            allocation: slots.iter().map(|&(v, r)| (v, RegSlot::Reg(r))).collect(),
            phi_copies: HashMap::new(),
            handler_phi_stores: Vec::new(),
            num_regs: 8,
            copy_temp: None,
            call_window_base: None,
            low_scratch_base: None,
        }
    }

    fn used_set(values: &[ValueId]) -> HashSet<ValueId> {
        values.iter().copied().collect()
    }

    #[test]
    fn reg_colored_operand_passes_through_without_emission() {
        let v = ValueId::new(1);
        let alloc = alloc_with(&[(v, 2)]);
        let mut codes = Vec::new();
        let r = val_reg(F, v, &alloc, &mut codes, 0).expect("reg operand must resolve");
        assert_eq!(r, Reg(2));
        assert!(codes.is_empty(), "no lda/sta expected, got {codes:?}");
    }

    #[test]
    fn unallocated_operand_is_a_hard_error_not_silent_acc() {
        let alloc = alloc_with(&[]);
        let mut codes = Vec::new();
        let mut tracker = AccContent::Hole;
        let dangling = ValueId::new(42);
        assert!(matches!(
            val_reg(F, dangling, &alloc, &mut codes, 0),
            Err(LowerError::UnallocatedOperand { value, .. }) if value == dangling
        ));
        assert!(matches!(
            ensure_acc(&mut tracker, F, dangling, &alloc, &mut codes),
            Err(LowerError::UnallocatedOperand { value, .. }) if value == dangling
        ));
    }

    #[test]
    fn ensure_acc_loads_the_home_on_a_miss_and_records_the_content() {
        let v = ValueId::new(1);
        let alloc = alloc_with(&[(v, 3)]);
        let mut codes = Vec::new();
        let mut tracker = AccContent::Hole;
        ensure_acc(&mut tracker, F, v, &alloc, &mut codes).expect("load must succeed");
        assert!(
            matches!(codes.as_slice(), [Bytecode::Lda(Reg(3))]),
            "a tracker miss must emit Lda(home), got {codes:?}"
        );
        assert_eq!(tracker, AccContent::Holds(v));
    }

    #[test]
    fn ensure_acc_hit_emits_no_load() {
        let v = ValueId::new(1);
        let alloc = alloc_with(&[(v, 3)]);
        let mut codes = Vec::new();
        let mut tracker = AccContent::Holds(v);
        ensure_acc(&mut tracker, F, v, &alloc, &mut codes).expect("hit must succeed");
        assert!(codes.is_empty(), "a cache hit must not emit, got {codes:?}");
        // A DIFFERENT value is a miss even when the tracker holds something.
        let w = ValueId::new(2);
        let alloc = alloc_with(&[(v, 3), (w, 4)]);
        ensure_acc(&mut tracker, F, w, &alloc, &mut codes).expect("miss must succeed");
        assert!(
            matches!(codes.as_slice(), [Bytecode::Lda(Reg(4))]),
            "a different value must reload from its own home, got {codes:?}"
        );
        assert_eq!(tracker, AccContent::Holds(w));
    }

    #[test]
    fn used_results_are_homed_and_tracked_dead_results_are_not() {
        let live = ValueId::new(1);
        let dead = ValueId::new(2);
        let alloc = alloc_with(&[(live, 5), (dead, 6)]);
        let used = used_set(&[live]);
        let mut codes = Vec::new();
        let mut tracker = AccContent::Hole;

        home_result(&mut tracker, Some(live), &used, F, &alloc, &mut codes)
            .expect("homing must succeed");
        assert!(
            matches!(codes.as_slice(), [Bytecode::Sta(Reg(5))]),
            "a used result must be homed with Sta, got {codes:?}"
        );
        assert_eq!(tracker, AccContent::Holds(live));

        codes.clear();
        home_result(&mut tracker, Some(dead), &used, F, &alloc, &mut codes)
            .expect("dead result must not error");
        assert!(codes.is_empty(), "a dead result gets no Sta, got {codes:?}");
        assert_eq!(
            tracker,
            AccContent::Unknown,
            "a dead result's acc content is untracked"
        );
    }

    #[test]
    fn register_operands_read_homes_and_the_acc_operand_loads_last() {
        // obj in R7, key in R0: val_reg emits nothing (low homes), then
        // ensure_acc(key) emits the Lda. No spill slot, no Sta — the old
        // B3 spill-before-load dance is gone by construction.
        let obj = ValueId::new(1);
        let key = ValueId::new(2);
        let alloc = alloc_with(&[(obj, 7), (key, 0)]);
        let mut codes = Vec::new();
        let mut tracker = AccContent::Hole;
        let regs = materialize_operands(&mut tracker, F, &[obj], Some(key), &alloc, &mut codes)
            .expect("materialization must succeed");
        assert_eq!(regs, vec![Reg(7)]);
        assert!(
            matches!(codes.as_slice(), [Bytecode::Lda(Reg(0))]),
            "expected exactly the key's Lda(home), got {codes:?}"
        );
        assert_eq!(tracker, AccContent::Holds(key));
    }
}
