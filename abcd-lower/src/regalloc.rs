//! SSA-based register allocation (port of v0.1 `abcd_ir::lower::regalloc`
//! onto the v0.2 IR).
//!
//! 1. Exact backward dataflow liveness analysis.
//! 2. Interference graph construction (SSA guarantees chordal graph).
//! 3. MCS (Maximum Cardinality Search) ordering + greedy coloring to
//!    register homes. Every value is colored to a REGISTER: the
//!    accumulator is not a coloring class but one physical location whose
//!    content is tracked at emission time by isel ("acc-as-cache", B4).
//! 4. Boissinot SSA destruction: coalesce same-color phi operands, collect
//!    the per-edge parallel copy sets for different colors. The copies are
//!    resolved (sequentialized) at slot level at the emission point in
//!    `layout`, because coalescing can make distinct values share a slot.
//!
//! v0.2 adaptations:
//!
//! - phis are the leading [`Op::Phi`] prefix of `block.insts`, keyed by
//!   `(Edge, value)` — the pred of an entry is `edge.from`;
//! - exception values are first-class [`ValueDef::ExceptionParam`]
//!   recorded on the try regions' [`Catch`](abcd_ir2::Catch) entries
//!   (v0.1's `exception_values`);
//! - frame-initial values are [`ValueDef::Const`] constants (v0.1
//!   materialized seed instructions at the entry top); they are colored
//!   like any value and modeled as defined at the entry block's start.

use std::collections::{BinaryHeap, HashMap, HashSet};

use abcd_ir2::{BlockId, FuncId, Module, Op, ValueDef, ValueId};

use crate::analysis::{self, augmented_succs};
use crate::fusion::Suppression;

/// The result of register allocation for a function.
#[derive(Debug)]
pub struct RegAlloc {
    /// Value → allocated register home. Every value lives in a register;
    /// the accumulator is a physical emission-time resource tracked by
    /// isel (acc-as-cache, B4), never a coloring class.
    pub allocation: HashMap<ValueId, RegSlot>,
    /// Parallel copies for phi elimination.
    /// Key: (predecessor, successor). Value: (src, dst) copies.
    /// Never carries exception-edge copies: phis in catch-handler blocks
    /// lower to [`Self::handler_phi_stores`] instead (N21).
    pub phi_copies: HashMap<(BlockId, BlockId), Vec<(ValueId, ValueId)>>,
    /// N21 pinned stores for handler-block phis, as `(pred, incoming value,
    /// phi result)` triples sorted by index — one per phi entry whose source
    /// is not already co-located with the result.
    ///
    /// A phi in a catch handler means "the handler sees the variable as of
    /// the dynamic exception point", and the VM dispatches directly to the
    /// handler's flat offset — no copy code can run on an exception edge
    /// (trampolines cannot serve it). The phi result's slot S therefore
    /// tracks the variable imperatively, like the vendored vreg home: isel
    /// emits `S ← slot(src)` at the pred's block start, or — when `src` is
    /// defined by an instruction inside the pred — immediately after that
    /// instruction (the closest implementable point to the vendored `sta`;
    /// an exception at an earlier instruction of the pred then correctly
    /// observes the previous writer, exactly like the original bytecode).
    /// `allocate` adds interference edges keeping S free of any value live
    /// into or defined in the pred, so the store never clobbers the normal
    /// path either.
    pub handler_phi_stores: Vec<(BlockId, ValueId, ValueId)>,
    /// Total registers used, including the reserved `copy_temp` register
    /// when present.
    pub num_regs: u16,
    /// Reserved real register for breaking slot-level copy cycles in layout.
    /// `Some` iff the function has any phi copies; never assigned to a value.
    pub copy_temp: Option<RegSlot>,
    /// Base of the reserved consecutive range-call argument window. `Some`
    /// iff the function contains a range-form call (isel's
    /// Callrange/Callthisrange/Supercallthisrange/Supercallarrowrange arms,
    /// narrow or wide). Every vendored range-call form encodes only a u8
    /// START register and reads argc consecutive slots, while the args'
    /// colored slots are not guaranteed consecutive (N4) — isel copies the
    /// args into `base .. base + argc` with auto-widening `mov`s and encodes
    /// `base` as the start. The window is reserved ONCE per function (sized
    /// to the largest range call); windows of different call sites overlap
    /// because each site's fill+call sequence completes before the next
    /// instruction is emitted — the window registers are dead outside the
    /// fill sequence. Coloring never assigns these slots to a value.
    /// Guaranteed ≤ 255 (checked at reservation; isel re-checks).
    pub call_window_base: Option<u16>,
    /// Base of the [`LOW_SCRATCH_COUNT`] consecutive reserved low (≤ 255)
    /// scratch registers, present iff the frame may exceed the u8 register
    /// operand encodings ("high-register mode"): indices `base .. base+3`
    /// route high register OPERANDS (one per operand position, so a
    /// 4-register-operand instruction never aliases two operands), index
    /// `base + 4` routes acc traffic (`sta scratch; mov high, scratch` for
    /// result homing, `mov scratch, high; lda scratch` for acc loads).
    /// `sta`/`lda` are `op_v_8`-only in the vendored ISA, so high registers
    /// are reachable only via `mov` (the sole auto-widening mnemonic,
    /// op_v1_16_v2_16). Never assigned to a value.
    pub low_scratch_base: Option<u16>,
}

/// Number of low scratch registers reserved in high-register mode for
/// routing register OPERANDS of one instruction: the maximum simultaneous
/// register operands of any instruction isel emits is 4
/// (`definegettersetterbyvalue`, `callthis3`).
pub const LOW_OPERAND_SCRATCHES: u16 = 4;
/// Total size of the reserved low scratch block: the operand scratches plus
/// one acc-routing scratch at index [`LOW_OPERAND_SCRATCHES`]. The acc
/// scratch must be distinct from the operand scratches: operand registers
/// stay live in their scratches across the acc operand's `lda`.
pub const LOW_SCRATCH_COUNT: u16 = LOW_OPERAND_SCRATCHES + 1;

/// Register allocation failure modes.
#[derive(Debug, thiserror::Error)]
pub enum RegAllocError {
    /// The function requires more registers than the frame can hold.
    #[error("function requires more than 65535 registers")]
    RegisterOverflow,
    /// The range-call window cannot start low enough.
    #[error(
        "range-call argument window needs a start register <= 255 (u8 in every vendored \
         callrange form, narrow and wide), but the parameter/scratch area already extends past it"
    )]
    WindowBaseOverflow,
    /// A same-slot result/incoming handler-phi pair interferes.
    #[error(
        "a catch-handler phi has a same-slot result/incoming pair that interferes — greedy \
         coloring never assigns one slot to an interfering pair, so this is inconsistent \
         (hand-crafted) input"
    )]
    HandlerPhiSlotConflict,
    /// A handler-phi result or incoming value was never colored.
    #[error("a catch-handler phi result or one of its incoming values was never colored")]
    HandlerPhiUncoalesced,
}

/// Where a value lives after allocation. Single-variant by design (B4):
/// the accumulator used to be a second "color" (`RegSlot::Acc`), but acc
/// is one physical location whose content any `Lda`/acc-writing
/// instruction destroys — an assignment the allocator cannot keep honest.
/// Every value now gets a register home and isel tracks the physical acc
/// content at emission time (acc-as-cache).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RegSlot {
    /// A virtual register home.
    Reg(u16),
}

/// Ceiling for allocated (and reserved) registers. Slots at or above this
/// base are outside the declared frame; nothing may be assigned there.
pub const TEMP_REG_BASE: u16 = 0xfff0;

/// Re-export compute_rpo for backward compatibility.
pub fn compute_rpo(module: &Module, func_id: FuncId) -> Vec<BlockId> {
    analysis::compute_rpo(module, func_id)
}

/// All phi-instruction entries of a block: `(pred, incoming value, phi
/// result)` — the v0.1 view of the v0.2 `(Edge, value)` phi entries.
/// Duplicate `pred`s (a Normal and an Exceptional edge from one block)
/// appear once per entry, like v0.1's per-edge list.
fn phi_entries(module: &Module, block: BlockId) -> Vec<(BlockId, ValueId, ValueId)> {
    let mut out = Vec::new();
    let Some(bb) = module.block(block) else {
        return out;
    };
    for &iid in &bb.insts {
        let Some(inst) = module.inst(iid) else {
            continue;
        };
        let Op::Phi { entries } = &inst.op else {
            break; // phis form the leading prefix
        };
        let Some(result) = inst.result else { continue };
        for (edge, val) in entries {
            out.push((edge.from, *val, result));
        }
    }
    out
}

/// Iterate a block's phi instructions (the leading [`Op::Phi`] prefix).
fn for_each_phi(module: &Module, block: BlockId, mut f: impl FnMut(&abcd_ir2::Inst)) {
    let Some(bb) = module.block(block) else {
        return;
    };
    for &iid in &bb.insts {
        let Some(inst) = module.inst(iid) else { break };
        if !inst.op.is_phi() {
            break;
        }
        f(inst);
    }
}

/// The frame-initial constant values owned by `func_id` — v0.1's
/// entry-top seed literals.
///
/// `used_only` selects between the two v0.1 pipeline variants'
/// behaviors, and is what makes ONE implementation byte-faithful to
/// both:
///
/// - `false` (lift parity): include UNUSED constants. v0.1's lift
///   creates the seed as an entry-top instruction and its lower emits
///   the seed's load unconditionally (only the homing `Sta` is
///   use-gated). Lift creates seeds lazily but a DISCARDED operand read
///   can leave one unused, so unused seeds do occur at lift.
/// - `true` (opt parity): only constants with at least one operand use
///   in the function's instructions. v0.1's optimizer sweeps the seed
///   instruction with ADCE once its last use is gone; the v0.2 seed is
///   an instruction-less `ValueDef::Const` value, so nothing remains to
///   sweep and the lower must skip it instead. (Post-pipeline, dead
///   instructions are swept, so "used by any instruction" is exactly
///   "used by a live instruction" — ADCE's survival criterion.)
///
/// v0.2's `ValueDef::Const` values carry no owning-function back-pointer,
/// but the lift creates values function-by-function in function-table
/// order, so each function's values form a contiguous id range. A const
/// value is attributed to the function whose range contains it: the
/// function with the greatest anchor minimum ≤ the const's id, where a
/// function's anchors are its params, exception params, and instruction
/// results (all function-scoped by construction).
///
/// Boundary note: a const created as a 0-parameter function's VERY FIRST
/// value (before any anchor) sorts into the previous function's range —
/// the only placement ambiguity the id ranges cannot resolve; v0.1 would
/// place it in the owning function. Never observed in the corpus.
pub fn frame_init_consts(module: &Module, func_id: FuncId, used_only: bool) -> Vec<ValueId> {
    // The use gate (opt parity): constants with at least one operand use
    // in the owning function (phi entries are operands). Fusion
    // suppression never hides a frame-initial const's use: suppressed
    // instructions are the fused-away LoadConst/constant-index producers,
    // which carry no SSA operands of their own.
    let mut used: HashSet<ValueId> = HashSet::new();
    if used_only {
        if let Some(func) = module.func(func_id) {
            for &bb in &func.blocks {
                let Some(block) = module.block(bb) else {
                    continue;
                };
                for &iid in &block.insts {
                    if let Some(inst) = module.inst(iid) {
                        used.extend(inst.op.operands());
                    }
                }
            }
        }
    }

    // Each function's anchor minimum, in function-table order.
    let mut starts: Vec<(FuncId, u32)> = Vec::new();
    for (i, f) in module.functions.iter().enumerate() {
        let mut lo = u32::MAX;
        for v in &f.params {
            lo = lo.min(v.0);
        }
        for region in &f.try_regions {
            for catch in &region.catches {
                lo = lo.min(catch.exception.0);
            }
        }
        for &bb in &f.blocks {
            let Some(block) = module.block(bb) else {
                continue;
            };
            for &iid in &block.insts {
                if let Some(result) = module.inst(iid).and_then(|inst| inst.result) {
                    lo = lo.min(result.0);
                }
            }
        }
        if lo != u32::MAX {
            starts.push((FuncId::new(i as u32), lo));
        }
    }
    let mut out = Vec::new();
    for (vid, value) in module.values.iter().enumerate() {
        if !matches!(value.def, ValueDef::Const(_)) {
            continue;
        }
        let id = vid as u32;
        // The owning function: the last one whose anchor minimum is <= id.
        if let Some((owner, _)) = starts.iter().rev().find(|(_, lo)| *lo <= id) {
            if *owner == func_id && (!used_only || used.contains(&ValueId::new(id))) {
                out.push(ValueId::new(id));
            }
        }
    }
    out
}

/// Allocate registers for a function using SSA-based chordal coloring.
///
/// `suppression` (fusion analysis) names the v0.2-expansion values that
/// must be invisible to allocation — v0.1's allocator never saw them,
/// and coloring them would drift every other value's home.
///
/// Default options (v0.1-lift-faithful); see [`crate::LowerOptions`].
pub fn allocate(
    module: &Module,
    func_id: FuncId,
    suppression: &Suppression,
) -> Result<RegAlloc, RegAllocError> {
    allocate_with_options(module, func_id, suppression, crate::LowerOptions::default())
}

/// [`allocate`] with explicit [`crate::LowerOptions`].
pub fn allocate_with_options(
    module: &Module,
    func_id: FuncId,
    suppression: &Suppression,
    options: crate::LowerOptions,
) -> Result<RegAlloc, RegAllocError> {
    let Some(func) = module.func(func_id) else {
        return Ok(RegAlloc {
            allocation: HashMap::new(),
            phi_copies: HashMap::new(),
            handler_phi_stores: Vec::new(),
            num_regs: 0,
            copy_temp: None,
            call_window_base: None,
            low_scratch_base: None,
        });
    };
    let rpo = analysis::compute_rpo(module, func_id);

    // Catch-handler blocks of this function (N13/N21).
    let handler_blocks: HashSet<BlockId> = func
        .try_regions
        .iter()
        .flat_map(|region| region.catches.iter().map(|c| c.handler))
        .collect();

    // Handler → exception value (N13). One value per handler block by
    // construction (lift seeds exactly one ExceptionParam per handler).
    let mut handler_exc: Vec<(BlockId, ValueId)> = Vec::new();
    for region in &func.try_regions {
        for catch in &region.catches {
            let pair = (catch.handler, catch.exception);
            if !handler_exc.contains(&pair) {
                handler_exc.push(pair);
            }
        }
    }

    // Collect all values in the function, skipping suppressed results
    // (v0.1-invisible expansion values — see `fusion`). The frame-initial
    // constants owned by this function (v0.1's entry-top seed literals;
    // use-gated — see `frame_init_consts`) come FIRST — v0.1's seeds are
    // the entry block's first
    // instructions, so v0.1's scan pushes them first, in reverse creation
    // order (each new seed was inserted at entry index 0). The insertion
    // order matters: MCS's heap pops equal (weight, rank) keys in
    // heap-structural order.
    let const_values = frame_init_consts(module, func_id, options.prune_unused_frame_init_consts);
    let entry = rpo.first().copied();
    let mut all_values: Vec<ValueId> = Vec::new();
    for &bb in &rpo {
        if Some(bb) == entry {
            for &c in const_values.iter().rev() {
                all_values.push(c);
            }
        }
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &inst_id in &block.insts {
            if suppression.insts.contains(&inst_id) {
                continue;
            }
            if let Some(result) = module.inst(inst_id).and_then(|i| i.result) {
                all_values.push(result);
            }
        }
    }
    // Values with at least one use (any instruction or phi operand). A phi
    // result with NO use needs no copies/stores at all: its slot content is
    // never read, and emitting its edge copies can only CLOBBER the live
    // value that legally shares the dead result's slot (dead values do not
    // interfere with anyone). See boissinot_destruction. Suppressed values
    // never count as used (they are never read from a register home).
    let mut used: HashSet<ValueId> = HashSet::new();
    for &bb in &rpo {
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
    // Add function parameters. `params` is the authoritative parameter
    // identity (lift entry seeding); an arena-index convention would name
    // values of OTHER functions in a multi-function module.
    for &val in &func.params {
        if !all_values.contains(&val) {
            all_values.push(val);
        }
    }
    // Add the catch-handler exception values (N13) that are actually used.
    // An unused one needs no register home and no handler prologue store.
    for &(_, exc) in &handler_exc {
        if used.contains(&exc) && !all_values.contains(&exc) {
            all_values.push(exc);
        }
    }

    if all_values.is_empty() {
        return Ok(RegAlloc {
            allocation: HashMap::new(),
            phi_copies: HashMap::new(),
            handler_phi_stores: Vec::new(),
            num_regs: 0,
            copy_temp: None,
            call_window_base: None,
            low_scratch_base: None,
        });
    }

    // Range-call argument window + low scratch block reservation (S2/N4).
    //
    // The vendored range-call forms encode only a u8 START register and read
    // argc consecutive slots, and `sta`/`lda` are op_v_8-only, so:
    //
    // 1. `window` = the largest range-call argc in the function. When > 0, a
    //    consecutive window of that many slots is reserved right after the
    //    parameter homes (plus the scratch block in high-register mode) and
    //    coloring never assigns it; isel copies each call's args into it in
    //    call order (auto-widening `mov`, encodable for any slot). The
    //    window start must be ≤ 255 even for the wide forms.
    // 2. High-register mode: when even the most compact packing (values +
    //    params + window + the copy-temp top reservation) cannot keep
    //    every slot ≤ 255, some value may be colored to a register ≥ 256,
    //    which `sta`/`lda` cannot encode. LOW_SCRATCH_COUNT low scratch
    //    registers are then reserved between the parameter homes and the
    //    window, and isel routes all high-register acc traffic through
    //    them. Coloring skips the reserved slots, so the reservation is
    //    honest: the scratches are never live across any instruction.
    //
    // Both reservations are computed BEFORE liveness/interference: the
    // overflow checks are cheap hard errors even for pathological inputs
    // (e.g. a > u16::MAX-arg call would otherwise build a quadratic
    //    interference graph before failing).
    let window = range_call_window_size(module, &rpo) as u64;
    let param_count = func.params.len() as u64;
    let n_values = all_values.len() as u64;
    // Low mode must also fit the copy_temp top reservation (+ 1).
    let low_mode_fits = param_count + window + n_values + 1 <= 256;
    let low_scratches = if low_mode_fits {
        0
    } else {
        LOW_SCRATCH_COUNT as u64
    };
    let window_base = param_count + low_scratches;
    if window > 0 {
        if window_base > 255 {
            return Err(RegAllocError::WindowBaseOverflow);
        }
        if window_base + window > u16::MAX as u64 {
            // The frame cannot hold the window (this also rejects
            // argc > u16::MAX, which no vendored form can encode).
            return Err(RegAllocError::RegisterOverflow);
        }
    }
    if low_scratches > 0 && param_count + low_scratches > 256 {
        // The scratch block itself would not be low-addressable.
        return Err(RegAllocError::RegisterOverflow);
    }
    let reserved_start = param_count as u16;
    let reserved_len = (low_scratches + window) as u16;

    // Step 1: Exact backward dataflow liveness (exception edges included).
    let (live_in, live_out) = compute_liveness(module, func_id, &rpo, &const_values);

    // Step 2: Build interference graph.
    let mut interference = build_interference(module, &rpo, &live_out, &const_values);

    // N13: an exception value has no defining instruction, so it never
    // acquires interference edges at a definition point. It is live from
    // handler entry and must not share its register home with any value
    // live into the handler.
    for &(handler, exc) in &handler_exc {
        if let Some(live) = live_in.get(&handler) {
            for &w in live {
                if w != exc {
                    interference.entry(exc).or_default().insert(w);
                    interference.entry(w).or_default().insert(exc);
                }
            }
        }
    }

    // N21 store-site safety. Every handler-phi entry (pred, src) lowers to
    // a store `S ← slot(src)` where S is the phi result's slot, emitted at
    // the pred's block start — or, when src is defined by an instruction
    // inside the pred, immediately after that instruction (the closest
    // implementable point to the vendored `sta`; an exception at an earlier
    // instruction of the pred then correctly observes the PREVIOUS writer,
    // exactly like the original bytecode). For this to be sound, no value
    // colored S may be live across the store (everything in live_in[pred]
    // for a block-start store) nor defined in the pred after the store
    // point (its definition would overwrite S mid-block): hence result ×
    // (live_in[pred] ∪ defs[pred]). defs[pred] ∪ live_in[pred] also covers
    // live_out[pred] and the terminator's operands, so normal-path
    // continuation and conditional branch conditions are safe as well.
    for &handler in &handler_blocks {
        for &(pred, _, result) in &phi_entries(module, handler) {
            if !used.contains(&result) {
                continue; // dead phi result: no stores (same class as edge copies)
            }
            let mut forbid: HashSet<ValueId> = live_in.get(&pred).cloned().unwrap_or_default();
            if let Some(pred_block) = module.block(pred) {
                for &inst_id in &pred_block.insts {
                    if let Some(r) = module.inst(inst_id).and_then(|i| i.result) {
                        forbid.insert(r);
                    }
                }
            }
            // The frame-initial constants are entry-block defs (v0.1's
            // seed literals are entry instructions, so they land in
            // defs[entry] there).
            if Some(pred) == entry {
                forbid.extend(const_values.iter().copied());
            }
            for w in forbid {
                if w != result {
                    interference.entry(result).or_default().insert(w);
                    interference.entry(w).or_default().insert(result);
                }
            }
        }
    }

    // Step 3: MCS ordering + greedy coloring. The reserved parameter homes
    // are pre-assigned; the reserved window/scratch range is skipped by the
    // smallest-slot scan. Every value lands in a register — the accumulator
    // is a physical emission-time resource (acc-as-cache, B4), not a color.
    let (allocation, colored_regs) = mcs_color(
        &all_values,
        &interference,
        func.params.len() as u16,
        &func.params,
        reserved_start,
        reserved_len,
    )?;

    // N21: handler-block phi slot consistency + the pinned store list
    // (computed before SSA destruction, which skips handler blocks).
    let handler_phi_stores =
        collect_handler_phi_stores(module, &handler_blocks, &allocation, &interference, &used)?;

    // The frame must cover the reserved window/scratch range even when
    // coloring stayed below it.
    let mut num_regs = colored_regs.max(reserved_start + reserved_len);

    // Step 5: Boissinot SSA destruction — collect the per-edge value-level
    // copy sets. Slot-level resolution happens at the emission point in
    // `layout`, so no value-level cycle breaking (or pseudo-temp) is done here.
    let phi_copies = boissinot_destruction(module, &rpo, &allocation, &handler_blocks, &used);

    // Step 6: When any edge carries phi copies, reserve exactly one real temp
    // register for slot-level cycle breaking. Overflow is a hard error, not
    // a silent saturation.
    let copy_temp = if phi_copies.values().any(|copies| !copies.is_empty()) {
        let temp = num_regs;
        if temp >= TEMP_REG_BASE {
            return Err(RegAllocError::RegisterOverflow);
        }
        num_regs += 1;
        Some(RegSlot::Reg(temp))
    } else {
        None
    };

    Ok(RegAlloc {
        allocation,
        phi_copies,
        handler_phi_stores,
        num_regs,
        copy_temp,
        call_window_base: if window > 0 {
            Some(window_base as u16)
        } else {
            None
        },
        low_scratch_base: if low_scratches > 0 {
            Some(param_count as u16)
        } else {
            None
        },
    })
}

/// Largest operand count among the function's range-form instructions —
/// the arms where isel encodes a start register and the VM reads N
/// consecutive slots (v0.1's `range_call_window_size` on the v0.2 op
/// shapes): `Call{Dynamic, this: None}` with > 3 args (callrange),
/// `Call{Dynamic, this: Some}` with > 4 window values (callthisrange —
/// the window holds [this, args...]), every `Call{Super}` (the
/// supercall*range forms are always range), every `Call{New}` (the
/// window holds [callee, args...] — the constructor counts), and
/// `CreateObjectWithExcludedKeys` (vendor `properties: [range_1]` — the
/// keys are read from a consecutive range starting at the encoded
/// register, isa.yaml:494-504; N9). Fixed-arity forms and spread/apply
/// calls pass individual register operands and need no window. All sites
/// share ONE window (each fill+use sequence completes within its own
/// instruction's selection), so the size is the max over all of them.
fn range_call_window_size(module: &Module, rpo: &[BlockId]) -> usize {
    use abcd_ir2::CallKind;
    let mut window = 0usize;
    for &bb in rpo {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &inst_id in &block.insts {
            let Some(inst) = module.inst(inst_id) else {
                continue;
            };
            match &inst.op {
                Op::Call {
                    kind, this, args, ..
                } => {
                    let range_argc = match kind {
                        CallKind::Dynamic | CallKind::Direct if this.is_none() => {
                            (args.len() > 3).then_some(args.len())
                        }
                        CallKind::Dynamic | CallKind::Direct => {
                            // this + args ride the window.
                            (args.len() + 1 > 4).then_some(args.len() + 1)
                        }
                        CallKind::Super | CallKind::SuperForwardAllArgs => Some(args.len()),
                        CallKind::New => Some(args.len() + 1),
                        // Fixed-arity forms: apply passes (this, array) as
                        // two register operands, supercallspread one — no
                        // consecutive window (v0.1 parity).
                        CallKind::Apply | CallKind::SuperSpread => None,
                    };
                    if let Some(argc) = range_argc {
                        window = window.max(argc);
                    }
                }
                Op::CreateObjectWithExcludedKeys { keys, .. } => {
                    window = window.max(keys.len());
                }
                _ => {}
            }
        }
    }
    window
}

// ─── Step 1: Exact backward dataflow liveness ────────────────────────────────

/// Compute live_in and live_out sets for each block.
/// Phi operands are treated as uses in the predecessor block.
///
/// Exception edges participate (`analysis::augmented_succs`): a catch
/// handler is a control-flow successor of every block in its try region —
/// an exception can transfer control from any protected instruction to
/// the handler, so values the handler uses are live out of every try
/// block. Terminator-only successors (`block_succs`) miss this: a try
/// body may end in `Throw`/`Unreachable` while the handler still reads
/// values defined there (S6 — without these edges such values look dead
/// past their definition, never interfere, and can all be colored Acc).
///
/// `const_values` (the used frame-initial constants) are modeled as
/// defined at the ENTRY block's start — v0.1 materialized their seed
/// literals as the entry block's first instructions.
fn compute_liveness(
    module: &Module,
    func_id: FuncId,
    rpo: &[BlockId],
    const_values: &[ValueId],
) -> (
    HashMap<BlockId, HashSet<ValueId>>,
    HashMap<BlockId, HashSet<ValueId>>,
) {
    // Augmented successor map: terminator successors plus, for every try
    // region, an edge from each protected block to each of its handlers.
    let succs: HashMap<BlockId, Vec<BlockId>> = rpo
        .iter()
        .map(|&bb| (bb, augmented_succs(module, func_id, bb)))
        .collect();

    let entry = rpo.first().copied();

    // Compute use and def sets per block.
    let mut block_use: HashMap<BlockId, HashSet<ValueId>> = HashMap::new();
    let mut block_def: HashMap<BlockId, HashSet<ValueId>> = HashMap::new();

    for &bb in rpo {
        let mut uses = HashSet::new();
        let mut defs = HashSet::new();
        let Some(block) = module.block(bb) else {
            continue;
        };

        for &inst_id in &block.insts {
            let Some(node) = module.inst(inst_id) else {
                continue;
            };
            if node.op.is_phi() {
                // Phi results are defs, but phi operands are NOT uses in
                // this block — they're uses in the predecessor blocks.
                if let Some(result) = node.result {
                    defs.insert(result);
                }
                continue;
            }
            // Uses that aren't already defined in this block.
            for val in node.op.operands() {
                if !defs.contains(&val) {
                    uses.insert(val);
                }
            }
            if let Some(result) = node.result {
                defs.insert(result);
            }
        }

        block_use.insert(bb, uses);
        block_def.insert(bb, defs);
    }

    // The used frame-initial constants are defined at the entry block's
    // start (v0.1's seed literals were the entry block's first insts).
    if let Some(entry) = entry {
        for &c in const_values {
            block_def.entry(entry).or_default().insert(c);
        }
    }

    // Add phi operands as uses in predecessor blocks.
    for &bb in rpo {
        for &(pred, val, _) in &phi_entries(module, bb) {
            let pred_def = block_def.get(&pred).cloned().unwrap_or_default();
            if !pred_def.contains(&val) {
                block_use.entry(pred).or_default().insert(val);
            }
        }
    }

    // Iterative dataflow: live_in[B] = use[B] ∪ (live_out[B] \ def[B])
    //                      live_out[B] = ∪ live_in[S] for S ∈ succs(B)
    let mut live_in: HashMap<BlockId, HashSet<ValueId>> = HashMap::new();
    let mut live_out: HashMap<BlockId, HashSet<ValueId>> = HashMap::new();

    for &bb in rpo {
        live_in.insert(bb, HashSet::new());
        live_out.insert(bb, HashSet::new());
    }

    let mut changed = true;
    while changed {
        changed = false;
        // Process in reverse RPO for faster convergence.
        for &bb in rpo.iter().rev() {
            let empty: Vec<BlockId> = Vec::new();
            let bb_succs = succs.get(&bb).unwrap_or(&empty);
            // live_out = union of live_in of successors
            let mut new_out = HashSet::new();
            for &succ in bb_succs {
                if let Some(succ_in) = live_in.get(&succ) {
                    new_out.extend(succ_in);
                }
            }
            // Also add phi operands from successors that come from this block.
            for &succ in bb_succs {
                for &(pred, val, _) in &phi_entries(module, succ) {
                    if pred == bb {
                        new_out.insert(val);
                    }
                }
            }

            // live_in = use ∪ (live_out \ def)
            let uses = block_use.get(&bb).cloned().unwrap_or_default();
            let defs = block_def.get(&bb).cloned().unwrap_or_default();
            let mut new_in: HashSet<ValueId> = uses;
            for &v in &new_out {
                if !defs.contains(&v) {
                    new_in.insert(v);
                }
            }

            if new_in != *live_in.get(&bb).unwrap() || new_out != *live_out.get(&bb).unwrap() {
                changed = true;
                live_in.insert(bb, new_in);
                live_out.insert(bb, new_out);
            }
        }
    }

    (live_in, live_out)
}

// ─── Step 2: Interference graph ──────────────────────────────────────────────

type InterferenceGraph = HashMap<ValueId, HashSet<ValueId>>;

/// Build interference graph by scanning each block backward from live_out.
/// After the entry block's backward walk, the used frame-initial constants
/// are defined (v0.1's entry-top seed literals): each interferes with
/// everything live across the entry block.
fn build_interference(
    module: &Module,
    rpo: &[BlockId],
    live_out: &HashMap<BlockId, HashSet<ValueId>>,
    const_values: &[ValueId],
) -> InterferenceGraph {
    let mut graph: InterferenceGraph = HashMap::new();
    let entry = rpo.first().copied();

    for &bb in rpo {
        let Some(block) = module.block(bb) else {
            continue;
        };
        let mut live: HashSet<ValueId> = live_out.get(&bb).cloned().unwrap_or_default();

        // Walk instructions backward.
        for &inst_id in block.insts.iter().rev() {
            let Some(node) = module.inst(inst_id) else {
                continue;
            };

            if let Some(result) = node.result {
                // result interferes with everything currently live (except itself).
                for &v in &live {
                    if v != result {
                        graph.entry(result).or_default().insert(v);
                        graph.entry(v).or_default().insert(result);
                    }
                }
                // result is no longer live above its definition.
                live.remove(&result);
            }

            if node.op.is_phi() {
                continue; // phi operands are uses in the preds, not here
            }
            // Operands become live.
            for val in node.op.operands() {
                live.insert(val);
            }
        }

        // Entry block: define the used frame-initial constants at its
        // start (v0.1's seed literals). Ascending id order is
        // creation order — the pairwise edges are symmetric, so the
        // resulting graph is order-independent.
        if Some(bb) == entry {
            for &c in const_values {
                for &v in &live {
                    if v != c {
                        graph.entry(c).or_default().insert(v);
                        graph.entry(v).or_default().insert(c);
                    }
                }
                live.remove(&c);
            }
        }
    }

    graph
}

// ─── Step 3: MCS + Greedy coloring ──────────────────────────────────────────

/// MCS ordering followed by reverse greedy coloring.
/// Returns (allocation, num_regs).
///
/// Parameters are pre-assigned to their vreg homes: `params[i]` gets
/// `Reg(i)`, the bottom of the frame. isel's copy-in prologue moves the
/// ABI top slots into these homes. `param_count` still seeds `next_reg`
/// so a hand-built function that declares more args than it created
/// values for keeps the bottom slots reserved, preserving the historical
/// frame size.
///
/// Every value is colored to a register: the accumulator is not a
/// coloring class (B4, acc-as-cache) — an acc-"colored" value used after
/// an intervening acc write reads garbage, and only emission-time
/// tracking (isel) can know the physical acc content.
///
/// `reserved_start .. reserved_start + reserved_len` is the reserved
/// low-slot range (low scratch block + range-call argument window, starting
/// right after the parameter homes): the smallest-slot scan never hands
/// those slots to a value, so isel can use them as dead scratch at any
/// emission point.
fn mcs_color(
    all_values: &[ValueId],
    interference: &InterferenceGraph,
    param_count: u16,
    params: &[ValueId],
    reserved_start: u16,
    reserved_len: u16,
) -> Result<(HashMap<ValueId, RegSlot>, u16), RegAllocError> {
    let n = all_values.len();
    let val_set: HashSet<ValueId> = all_values.iter().copied().collect();

    // MCS tie-breaking must match v0.1 byte-exactly. v0.1's heap pops
    // (weight, value-id) max-first; v0.2's ABSOLUTE value ids are shifted
    // by the suppressed expansion values (fusion) interleaved in the id
    // space, which would flip equal-weight ties against v0.1. The
    // non-suppressed values in id order are exactly v0.1's values in
    // creation order (same translation algorithm), so rank among the
    // non-suppressed is the correct tie-break key.
    let mut sorted = all_values.to_vec();
    sorted.sort_unstable();
    let rank_of: HashMap<ValueId, u32> = sorted
        .iter()
        .enumerate()
        .map(|(i, &v)| (v, i as u32))
        .collect();

    // MCS: repeatedly pick the unvisited vertex with the most visited
    // neighbors. A heap avoids rescanning the complete value set for every
    // vertex on high-register-pressure methods.
    let mut weight: HashMap<ValueId, u32> = HashMap::new();
    let mut visited = HashSet::new();
    let mut mcs_order: Vec<ValueId> = Vec::with_capacity(n);
    let mut heap: BinaryHeap<(u32, u32)> = BinaryHeap::new();
    for &value in all_values {
        heap.push((0, rank_of[&value]));
    }

    for _ in 0..n {
        let v = loop {
            let Some((w, rank)) = heap.pop() else {
                return Err(RegAllocError::RegisterOverflow);
            };
            let value = sorted[rank as usize];
            if visited.contains(&value) || weight.get(&value).copied().unwrap_or(0) != w {
                continue;
            }
            break value;
        };

        visited.insert(v);
        mcs_order.push(v);

        // Increment weight of unvisited neighbors.
        if let Some(neighbors) = interference.get(&v) {
            for &nb in neighbors {
                if !visited.contains(&nb) && val_set.contains(&nb) {
                    let new_weight = weight.entry(nb).or_default();
                    *new_weight += 1;
                    heap.push((*new_weight, rank_of[&nb]));
                }
            }
        }
    }

    // Greedy coloring in reverse MCS order.
    let mut allocation: HashMap<ValueId, RegSlot> = HashMap::new();
    let mut next_reg = param_count;

    // Pre-assign params to their vreg homes at the bottom of the frame.
    for (i, &val) in params.iter().enumerate() {
        allocation.insert(val, RegSlot::Reg(i as u16));
    }

    for &v in mcs_order.iter().rev() {
        if allocation.contains_key(&v) {
            continue;
        }

        // Collect colors used by neighbors.
        let mut used_colors: HashSet<u16> = HashSet::new();
        if let Some(neighbors) = interference.get(&v) {
            for nb in neighbors {
                if let Some(&RegSlot::Reg(color)) = allocation.get(nb) {
                    used_colors.insert(color);
                }
            }
        }

        // Find smallest available register, skipping the reserved
        // scratch/window range: those slots must stay dead for isel.
        let mut reg = 0u16;
        loop {
            if reg >= reserved_start && reg < reserved_start + reserved_len {
                reg = reserved_start + reserved_len;
                continue;
            }
            if !used_colors.contains(&reg) {
                break;
            }
            if reg == u16::MAX {
                return Err(RegAllocError::RegisterOverflow);
            }
            reg += 1;
        }
        if reg >= TEMP_REG_BASE {
            return Err(RegAllocError::RegisterOverflow);
        }
        if reg >= next_reg {
            next_reg = reg + 1;
        }
        allocation.insert(v, RegSlot::Reg(reg));
    }

    Ok((allocation, next_reg))
}

// ─── Step 5: Boissinot SSA destruction ───────────────────────────────────────

/// Boissinot-style SSA destruction:
/// - Same-color phi operands: coalesce (no copy needed).
/// - Different-color: record a copy on the (pred, block) edge.
///
/// The returned per-edge lists are parallel copy *sets* in value space.
/// They are NOT sequentialized here: coalescing lets distinct values share
/// a slot, so the safe emission order (and any cycle breaking through the
/// reserved `copy_temp` register) is computed at slot level in `layout`.
///
/// A phi whose RESULT has no use (`used` does not contain it) gets no
/// copies at all: its slot content is never read, so the copies are dead
/// traffic — and they are worse than dead, because a dead result does not
/// interfere with any value, so its slot can legally be shared with a
/// LIVE value whose home the copy would clobber at the edge (the
/// typescript-enum regression at the B4 refactor: a dead phi's `mov`
/// overwrote the live phi result sharing its slot on the fall-through
/// edge). Live phi results always interfere pairwise when both are live,
/// so their slots never collide this way.
fn boissinot_destruction(
    module: &Module,
    rpo: &[BlockId],
    allocation: &HashMap<ValueId, RegSlot>,
    handler_blocks: &HashSet<BlockId>,
    used: &HashSet<ValueId>,
) -> HashMap<(BlockId, BlockId), Vec<(ValueId, ValueId)>> {
    let mut copies: HashMap<(BlockId, BlockId), Vec<(ValueId, ValueId)>> = HashMap::new();

    for &bb in rpo {
        // N21: phis in catch-handler blocks lower to def-site write-through
        // stores (`collect_handler_phi_stores`), never edge copies — no
        // code may run on an exception edge, and the store covers the
        // normal-path arrival too when a handler block is also reachable by
        // a terminator edge.
        if handler_blocks.contains(&bb) {
            continue;
        }
        for_each_phi(module, bb, |inst_node| {
            let dst = match inst_node.result {
                Some(v) => v,
                None => return,
            };
            if !used.contains(&dst) {
                return; // dead phi result: no copies (see the fn doc)
            }
            let dst_color = allocation.get(&dst);

            if let Op::Phi { entries } = &inst_node.op {
                for (edge, src) in entries {
                    let src_color = allocation.get(src);
                    // Only insert copy if colors differ.
                    if src_color != dst_color {
                        copies.entry((edge.from, bb)).or_default().push((*src, dst));
                    }
                }
            }
        });
    }

    copies
}

// ─── N21: handler-phi slot pinning (pinned stores) ──────────────────────────

/// Collect the pinned stores for handler-block phis as `(pred, src,
/// result)` triples sorted by index, and check slot consistency.
///
/// A phi in a catch handler means "the handler sees the variable as of the
/// dynamic exception point". The VM dispatches directly to the handler's
/// flat offset, so no copy code may run on the exception edge; instead the
/// phi result's slot S tracks the variable imperatively (the vendored vreg
/// home): isel emits `S ← slot(src)` at the pred's block start — or
/// immediately after the defining instruction when `src` is defined inside
/// the pred. `allocate` added interference edges `result × (live_in[pred]
/// ∪ defs[pred])` so that no value colored S is live across or defined
/// after the store point; the store is therefore invisible to the normal
/// path as well.
///
/// Hard checks (never silent):
///
/// - the result must be colored (it always has a register home — there is
///   no accumulator coloring since B4);
/// - every differently-keyed incoming source must be colored;
/// - a same-slot result/incoming pair must not interfere — coloring never
///   assigns one slot to an interfering pair, so this can only fire on
///   hand-crafted allocations.
fn collect_handler_phi_stores(
    module: &Module,
    handler_blocks: &HashSet<BlockId>,
    allocation: &HashMap<ValueId, RegSlot>,
    interference: &InterferenceGraph,
    used: &HashSet<ValueId>,
) -> Result<Vec<(BlockId, ValueId, ValueId)>, RegAllocError> {
    let mut stores: Vec<(BlockId, ValueId, ValueId)> = Vec::new();
    for &handler in handler_blocks {
        let Some(block) = module.block(handler) else {
            continue;
        };
        for &iid in &block.insts {
            let Some(node) = module.inst(iid) else { break };
            let Op::Phi { entries } = &node.op else {
                break; // phis form the leading prefix
            };
            let Some(result) = node.result else { continue };
            if !used.contains(&result) {
                continue; // dead phi result: no stores (same class as edge copies)
            }
            let result_slot = allocation
                .get(&result)
                .copied()
                .ok_or(RegAllocError::HandlerPhiUncoalesced)?;
            for (edge, src) in entries {
                if *src == result {
                    continue; // self-reference (loop phi)
                }
                let src_slot = allocation
                    .get(src)
                    .copied()
                    .ok_or(RegAllocError::HandlerPhiUncoalesced)?;
                if src_slot == result_slot {
                    if interference.get(&result).is_some_and(|n| n.contains(src)) {
                        return Err(RegAllocError::HandlerPhiSlotConflict);
                    }
                    continue; // already co-located: no store needed
                }
                stores.push((edge.from, *src, result));
            }
        }
    }
    stores.sort_unstable();
    stores.dedup();
    Ok(stores)
}
