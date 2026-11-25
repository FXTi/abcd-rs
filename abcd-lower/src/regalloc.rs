//! SSA-based chordal register allocation (`design/ir.md` §5,
//! `design/decisions.md` `ADR-03`, `ADR-04`).
//!
//! 1. Exact backward dataflow liveness analysis (including exception edges).
//! 2. Interference graph construction (SSA guarantees chordality).
//! 3. MCS (Maximum Cardinality Search) ordering + greedy coloring to
//!    register homes. Every value is colored to a REGISTER: the
//!    accumulator is not a coloring class but one physical location whose
//!    content is tracked at emission time by isel ("acc-as-cache", `ADR-03`).
//! 4. Boissinot SSA destruction: coalesce same-color phi operands, collect
//!    the per-edge parallel copy sets for different colors. The copies are
//!    resolved (sequentialized) at slot level at the emission point in
//!    `layout`, because coalescing can make distinct values share a slot.
//!
//! IR representation notes:
//!
//! - phis are the leading [`Op::Phi`] prefix of `block.insts`, keyed by
//!   `(Edge, value)` — the predecessor of an entry is `edge.from`;
//! - exception values are first-class [`ValueDef::ExceptionParam`]
//!   recorded on the try regions' [`Catch`](abcd_ir::Catch) entries;
//! - frame-initial values are [`ValueDef::Const`] constants recorded on
//!   [`abcd_ir::FunctionData::frame_init_consts`]; they are colored like any
//!   value and modeled as defined at the entry block's start.

use std::collections::{BinaryHeap, HashMap, HashSet};

use abcd_ir::{
    BlockId, EdgeKind, ExceptionHandlerMap, FuncId, Module, Op, ValueDef, ValueId,
    normal_succs_inline,
};

use crate::analysis;
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

/// All phi-instruction entries of a block as `(edge, incoming value, phi
/// result)` triples.
fn phi_edge_entries(module: &Module, block: BlockId) -> Vec<(abcd_ir::Edge, ValueId, ValueId)> {
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
        for &(edge, val) in entries {
            out.push((edge, val, result));
        }
    }
    out
}

/// Iterate a block's phi instructions (the leading [`Op::Phi`] prefix).
fn for_each_phi(module: &Module, block: BlockId, mut f: impl FnMut(&abcd_ir::Inst)) {
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

/// Per-function frame-initial constant values (`ValueDef::Const`, #30).
///
/// Ownership is recorded directly on [`abcd_ir::FunctionData::frame_init_consts`]
/// at lift/construction time (and swept of dead entries by `abcd-opt`'s ADCE).
/// For hand-built IR modules that construct a [`ValueDef::Const`] value and
/// reference it in an instruction without registering it on
/// `func.frame_init_consts`, any unrecorded `ValueDef::Const` operand used in
/// `func.blocks` is appended in encounter order (`O(|F|)`).
pub fn frame_init_consts(module: &Module, func_id: FuncId) -> Vec<ValueId> {
    let Some(func) = module.func(func_id) else {
        return Vec::new();
    };
    let mut out: Vec<ValueId> = Vec::with_capacity(func.frame_init_consts.len());
    let mut seen: HashSet<ValueId> = HashSet::with_capacity(func.frame_init_consts.len());
    for &vid in &func.frame_init_consts {
        if module
            .value(vid)
            .is_some_and(|v| matches!(v.def, ValueDef::Const(_)))
            && seen.insert(vid)
        {
            out.push(vid);
        }
    }
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &iid in &block.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            for operand in inst.op.operands() {
                if !seen.contains(&operand)
                    && module
                        .value(operand)
                        .is_some_and(|v| matches!(v.def, ValueDef::Const(_)))
                {
                    seen.insert(operand);
                    out.push(operand);
                }
            }
        }
    }
    out
}

/// Allocate registers for a function using SSA-based chordal coloring.
///
/// `suppression` (fusion analysis) names the expansion values that must be
/// invisible to allocation.
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
    _options: crate::LowerOptions,
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
    // (fusion expansion intermediates — see `fusion`). The frame-initial
    // constants owned by this function (`frame_init_consts`) come FIRST in
    // reverse creation order (matching entry-top materialization order). The
    // insertion order matters: MCS's heap pops equal `(weight, rank)` keys in
    // deterministic rank order.
    let const_values = frame_init_consts(module, func_id);
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
    let low_mode_fits = param_count + window + n_values < 256;
    let low_scratches = if low_mode_fits {
        0
    } else {
        LOW_SCRATCH_COUNT as u64
    };

    // R3-M7: Keep parameters at 0..param_count whenever low_scratches and
    // call_window still fit low registers; when a large parameter count would
    // push low_scratches past v255 or window_base past v255, place
    // low_scratches (0..low_scratches) and call_window (low_scratches..) at
    // the bottom of the frame and assign parameter homes above them (isel's
    // entry prologue copies incoming ABI args into each parameter's home).
    let params_at_bottom =
        param_count + low_scratches <= 256 && (window == 0 || param_count + low_scratches <= 255);

    let (param_base, reserved_start, reserved_len, window_base, low_scratch_base) =
        if params_at_bottom {
            let wb = param_count + low_scratches;
            if window > 0 && wb + window > u64::from(u16::MAX) {
                return Err(RegAllocError::RegisterOverflow);
            }
            (
                0u16,
                param_count as u16,
                (low_scratches + window) as u16,
                wb as u16,
                (low_scratches > 0).then_some(param_count as u16),
            )
        } else {
            let wb = low_scratches;
            if window > 0 && wb + window > u64::from(u16::MAX) {
                return Err(RegAllocError::RegisterOverflow);
            }
            let res_len = low_scratches + window;
            if res_len + param_count > u64::from(TEMP_REG_BASE) {
                return Err(RegAllocError::RegisterOverflow);
            }
            (
                res_len as u16,
                0u16,
                res_len as u16,
                wb as u16,
                (low_scratches > 0).then_some(0u16),
            )
        };

    // Exception edges `(protected_block, handler_block)` from structured TryRegions.
    let mut exception_edges: HashSet<(BlockId, BlockId)> = HashSet::new();
    for region in &func.try_regions {
        for &p in &region.protected {
            for catch in &region.catches {
                exception_edges.insert((p, catch.handler));
            }
        }
    }

    // Step 1 & 2: Exact bitset backward dataflow liveness + interference graph (R3-A2).
    let (live_in, mut interference) =
        compute_liveness_and_interference(module, func_id, &rpo, &all_values, &const_values);

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

    // R3-X3 + N21 store-site safety:
    // 1. Any handler-phi entry lowering via `handler_phi_stores` interferes with
    //    `live_in[pred] ∪ defs[pred]`.
    // 2. All distinct handler-phi results whose handlers share a common protected
    //    block `p` (nested/competing catch handlers) interfere pairwise so one
    //    handler's pinned store in `p` never clobbers another handler's phi home.
    let mut handler_phis_by_pred: HashMap<BlockId, Vec<ValueId>> = HashMap::new();
    for region in &func.try_regions {
        for catch in &region.catches {
            for &(_, _, result) in &phi_edge_entries(module, catch.handler) {
                if !used.contains(&result) {
                    continue;
                }
                for &p in &region.protected {
                    let list = handler_phis_by_pred.entry(p).or_default();
                    if !list.contains(&result) {
                        list.push(result);
                    }
                }
            }
        }
    }
    for &handler in &handler_blocks {
        for &(edge, _, result) in &phi_edge_entries(module, handler) {
            if !used.contains(&result) {
                continue;
            }
            if edge.kind != EdgeKind::Exceptional
                && !exception_edges.contains(&(edge.from, handler))
            {
                continue; // normal-only incoming edge lowers via phi_copies (R3-M2)
            }
            let pred = edge.from;
            let list = handler_phis_by_pred.entry(pred).or_default();
            if !list.contains(&result) {
                list.push(result);
            }
            let mut forbid: HashSet<ValueId> = live_in.get(&pred).cloned().unwrap_or_default();
            if let Some(pred_block) = module.block(pred) {
                for &inst_id in &pred_block.insts {
                    if let Some(r) = module.inst(inst_id).and_then(|i| i.result) {
                        forbid.insert(r);
                    }
                }
            }
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
    for phis in handler_phis_by_pred.values() {
        for (i, &r1) in phis.iter().enumerate() {
            for &r2 in &phis[i + 1..] {
                if r1 != r2 {
                    interference.entry(r1).or_default().insert(r2);
                    interference.entry(r2).or_default().insert(r1);
                }
            }
        }
    }

    // Step 3: MCS ordering + chordal greedy coloring (R3-X6).
    let (allocation, colored_regs) = mcs_color(
        &all_values,
        &interference,
        param_base,
        func.params.len() as u16,
        &func.params,
        reserved_start,
        reserved_len,
    )?;

    // N21: handler-block phi slot consistency + the pinned store list.
    let handler_phi_stores = collect_handler_phi_stores(
        module,
        &handler_blocks,
        &exception_edges,
        &allocation,
        &interference,
        &used,
    )?;

    let min_param_end = if func.params.is_empty() {
        0
    } else {
        param_base + func.params.len() as u16
    };
    let mut num_regs = colored_regs
        .max(reserved_start + reserved_len)
        .max(min_param_end);

    // Step 5: Boissinot SSA destruction — collect per-edge value-level copies.
    let phi_copies = boissinot_destruction(
        module,
        &rpo,
        &allocation,
        &handler_blocks,
        &exception_edges,
        &used,
    );

    // Step 6: Reserve one real temp register whenever edge copies exist or
    // same-block handler-phi stores share source/destination slots (R3-X3).
    let handler_store_cycle_possible =
        handler_phi_stores
            .iter()
            .enumerate()
            .any(|(i, &(p1, s1, d1))| {
                let s1_slot = allocation.get(&s1);
                let d1_slot = allocation.get(&d1);
                handler_phi_stores[i + 1..].iter().any(|&(p2, s2, d2)| {
                    p1 == p2 && (allocation.get(&s2) == d1_slot || allocation.get(&d2) == s1_slot)
                })
            });
    let need_copy_temp =
        phi_copies.values().any(|copies| !copies.is_empty()) || handler_store_cycle_possible;
    let copy_temp = if need_copy_temp {
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
        call_window_base: (window > 0).then_some(window_base),
        low_scratch_base,
    })
}

/// Largest operand count among the function's range-form instructions —
/// the arms where isel encodes a start register and the VM reads N
/// consecutive slots (`S2` / `N4`): `Call{Dynamic, this: None}` with > 3 args (callrange),
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
    use abcd_ir::CallKind;
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
                        CallKind::Super | CallKind::SuperArrow => Some(args.len()),
                        CallKind::New => Some(args.len() + 1),
                        // Fixed-arity / non-window forms: apply passes (this, array),
                        // supercallspread passes array, supercallforwardallargs passes
                        // thisFunc, newobjapply passes ctor, callinit passes this.
                        CallKind::Apply
                        | CallKind::SuperSpread
                        | CallKind::SuperForwardAllArgs
                        | CallKind::NewSpread
                        | CallKind::ClassInit => None,
                    };
                    if let Some(argc) = range_argc {
                        window = window.max(argc);
                    }
                }
                Op::CreateObjectWithExcludedKeys { keys, .. } => {
                    // Reserve >= 1 slot so empty `keys` also has a dead low scratch
                    // register for `createemptyobject + copydataproperties`.
                    window = window.max(keys.len().max(1));
                }
                _ => {}
            }
        }
    }
    window
}

// ─── Step 1 & 2: Dense Bitset Liveness & Interference (`R3-A2`) ──────────────

type InterferenceGraph = HashMap<ValueId, HashSet<ValueId>>;

#[inline]
fn bit_set(bits: &mut [u64], idx: usize) {
    bits[idx >> 6] |= 1u64 << (idx & 63);
}

#[inline]
fn bit_clear(bits: &mut [u64], idx: usize) {
    bits[idx >> 6] &= !(1u64 << (idx & 63));
}

#[inline]
fn bit_test(bits: &[u64], idx: usize) -> bool {
    (bits[idx >> 6] & (1u64 << (idx & 63))) != 0
}

fn bitset_to_values(bits: &[u64], bit_to_val: &[ValueId]) -> HashSet<ValueId> {
    let mut out = HashSet::new();
    for (w_idx, &word) in bits.iter().enumerate() {
        let mut w = word;
        while w != 0 {
            let tz = w.trailing_zeros() as usize;
            out.insert(bit_to_val[(w_idx << 6) + tz]);
            w &= w - 1;
        }
    }
    out
}

fn add_live_interferences(
    graph: &mut InterferenceGraph,
    def_val: ValueId,
    def_bit: usize,
    live: &[u64],
    bit_to_val: &[ValueId],
) {
    for (w_idx, &word) in live.iter().enumerate() {
        let mut w = word;
        while w != 0 {
            let tz = w.trailing_zeros() as usize;
            let bit = (w_idx << 6) + tz;
            if bit != def_bit {
                let other = bit_to_val[bit];
                graph.entry(def_val).or_default().insert(other);
                graph.entry(other).or_default().insert(def_val);
            }
            w &= w - 1;
        }
    }
}

/// Compute exact backward liveness (including exception edges) over dense `[u64]`
/// bitsets using [`ExceptionHandlerMap`] and pre-grouped phi incoming lists,
/// then construct the interference graph in a single backward scan (`#58` `R3-A2`).
fn compute_liveness_and_interference(
    module: &Module,
    func_id: FuncId,
    rpo: &[BlockId],
    all_values: &[ValueId],
    const_values: &[ValueId],
) -> (HashMap<BlockId, HashSet<ValueId>>, InterferenceGraph) {
    let num_blocks = rpo.len();
    if num_blocks == 0 {
        return (HashMap::new(), HashMap::new());
    }

    let mut bb_to_idx: HashMap<BlockId, usize> = HashMap::with_capacity(num_blocks);
    for (idx, &bb) in rpo.iter().enumerate() {
        bb_to_idx.entry(bb).or_insert(idx);
    }

    // Assign dense bit indices `0..V` to every value referenced in `all_values`,
    // `const_values`, or any instruction operand.
    let mut val_to_bit: HashMap<ValueId, usize> = HashMap::with_capacity(all_values.len() + 8);
    let mut bit_to_val: Vec<ValueId> = Vec::with_capacity(all_values.len() + 8);
    let mut intern_val = |v: ValueId| -> usize {
        if let Some(&b) = val_to_bit.get(&v) {
            b
        } else {
            let b = bit_to_val.len();
            val_to_bit.insert(v, b);
            bit_to_val.push(v);
            b
        }
    };
    for &v in all_values {
        let _ = intern_val(v);
    }
    for &c in const_values {
        let _ = intern_val(c);
    }
    for &bb in rpo {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for &iid in &block.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            if let Some(res) = inst.result {
                let _ = intern_val(res);
            }
            inst.op.for_each_operand(|op| {
                let _ = intern_val(op);
            });
        }
    }

    let words = bit_to_val.len().div_ceil(64).max(1);
    let exc_map = ExceptionHandlerMap::build(module, func_id);

    // Precompute augmented successor indices per RPO block once (`O(B + ∑|handlers|)`).
    let mut succ_indices: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];
    for (b_idx, &bb) in rpo.iter().enumerate() {
        let out = &mut succ_indices[b_idx];
        if let Some(term_op) = module
            .block(bb)
            .and_then(|b| b.insts.last())
            .and_then(|&iid| module.inst(iid))
            .map(|i| &i.op)
        {
            let (ns, nlen) = normal_succs_inline(term_op);
            for &succ_bb in &ns[..nlen] {
                if let Some(&si) = bb_to_idx.get(&succ_bb)
                    && !out.contains(&si)
                {
                    out.push(si);
                }
            }
        }
        if let Some(ref em) = exc_map {
            for &h_bb in em.handlers_of(bb) {
                if let Some(&hi) = bb_to_idx.get(&h_bb)
                    && !out.contains(&hi)
                {
                    out.push(hi);
                }
            }
        }
    }

    // Compute per-block `use` / `def` bitsets and pre-group phi incoming operands by `pred_idx`.
    let mut block_use: Vec<Vec<u64>> = vec![vec![0u64; words]; num_blocks];
    let mut block_def: Vec<Vec<u64>> = vec![vec![0u64; words]; num_blocks];
    let mut phi_out_bits: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];

    for (b_idx, &bb) in rpo.iter().enumerate() {
        let Some(block) = module.block(bb) else {
            continue;
        };
        let uses = &mut block_use[b_idx];
        let defs = &mut block_def[b_idx];
        for &iid in &block.insts {
            let Some(node) = module.inst(iid) else {
                continue;
            };
            if let Op::Phi { entries } = &node.op {
                if let Some(result) = node.result {
                    bit_set(defs, val_to_bit[&result]);
                }
                for &(edge, val) in entries {
                    if let Some(&pred_idx) = bb_to_idx.get(&edge.from)
                        && succ_indices[pred_idx].contains(&b_idx)
                    {
                        phi_out_bits[pred_idx].push(val_to_bit[&val]);
                    }
                }
                continue;
            }
            node.op.for_each_operand(|val| {
                let bit = val_to_bit[&val];
                if !bit_test(defs, bit) {
                    bit_set(uses, bit);
                }
            });
            if let Some(result) = node.result {
                bit_set(defs, val_to_bit[&result]);
            }
        }
    }

    // Frame-initial constants are defined at the entry block (`rpo[0]`) start.
    for &c in const_values {
        bit_set(&mut block_def[0], val_to_bit[&c]);
    }
    for pred_idx in 0..num_blocks {
        for &bit in &phi_out_bits[pred_idx] {
            if !bit_test(&block_def[pred_idx], bit) {
                bit_set(&mut block_use[pred_idx], bit);
            }
        }
    }

    // Iterative bitset dataflow in reverse RPO order.
    let mut live_in_bits: Vec<Vec<u64>> = vec![vec![0u64; words]; num_blocks];
    let mut live_out_bits: Vec<Vec<u64>> = vec![vec![0u64; words]; num_blocks];
    let mut scratch_out = vec![0u64; words];
    let mut scratch_in = vec![0u64; words];

    let mut changed = true;
    while changed {
        changed = false;
        for b_idx in (0..num_blocks).rev() {
            scratch_out.fill(0);
            for &succ_idx in &succ_indices[b_idx] {
                for (dst_w, &src_w) in scratch_out.iter_mut().zip(&live_in_bits[succ_idx]) {
                    *dst_w |= src_w;
                }
            }
            for &bit in &phi_out_bits[b_idx] {
                bit_set(&mut scratch_out, bit);
            }
            for w in 0..words {
                scratch_in[w] = block_use[b_idx][w] | (scratch_out[w] & !block_def[b_idx][w]);
            }
            if scratch_in != live_in_bits[b_idx] || scratch_out != live_out_bits[b_idx] {
                live_in_bits[b_idx].copy_from_slice(&scratch_in);
                live_out_bits[b_idx].copy_from_slice(&scratch_out);
                changed = true;
            }
        }
    }

    // Build interference graph directly over `live_out_bits`.
    let mut graph: InterferenceGraph = HashMap::new();
    let mut live = vec![0u64; words];
    for (b_idx, &bb) in rpo.iter().enumerate() {
        let Some(block) = module.block(bb) else {
            continue;
        };
        live.copy_from_slice(&live_out_bits[b_idx]);
        for &iid in block.insts.iter().rev() {
            let Some(node) = module.inst(iid) else {
                continue;
            };
            if let Some(result) = node.result {
                let res_bit = val_to_bit[&result];
                add_live_interferences(&mut graph, result, res_bit, &live, &bit_to_val);
                bit_clear(&mut live, res_bit);
            }
            if node.op.is_phi() {
                continue;
            }
            node.op.for_each_operand(|val| {
                bit_set(&mut live, val_to_bit[&val]);
            });
        }
        if b_idx == 0 {
            for &c in const_values {
                let c_bit = val_to_bit[&c];
                add_live_interferences(&mut graph, c, c_bit, &live, &bit_to_val);
                bit_clear(&mut live, c_bit);
            }
        }
    }

    let live_in_map: HashMap<BlockId, HashSet<ValueId>> = rpo
        .iter()
        .enumerate()
        .map(|(b_idx, &bb)| (bb, bitset_to_values(&live_in_bits[b_idx], &bit_to_val)))
        .collect();

    (live_in_map, graph)
}

// ─── Step 3: MCS + Chordal Greedy Coloring (`R3-X6`) ────────────────────────

fn mcs_color(
    all_values: &[ValueId],
    interference: &InterferenceGraph,
    param_base: u16,
    param_count: u16,
    params: &[ValueId],
    reserved_start: u16,
    reserved_len: u16,
) -> Result<(HashMap<ValueId, RegSlot>, u16), RegAllocError> {
    let n = all_values.len();
    let val_set: HashSet<ValueId> = all_values.iter().copied().collect();

    // Deterministic MCS tie-breaking (`N20`): `BinaryHeap` pops `(weight, rank)`
    // max-first, where `rank` is the dense creation-order rank among non-suppressed
    // values.
    let mut sorted = all_values.to_vec();
    sorted.sort_unstable();
    let rank_of: HashMap<ValueId, u32> = sorted
        .iter()
        .enumerate()
        .map(|(i, &v)| (v, i as u32))
        .collect();

    let mut allocation: HashMap<ValueId, RegSlot> = HashMap::with_capacity(n);
    let mut next_reg = if param_count == 0 {
        0
    } else {
        param_base + param_count
    };

    // Pre-assign parameters to their homes (`param_base .. param_base + param_count`).
    for (i, &val) in params.iter().enumerate() {
        let r = param_base + i as u16;
        if r >= TEMP_REG_BASE {
            return Err(RegAllocError::RegisterOverflow);
        }
        allocation.insert(val, RegSlot::Reg(r));
    }

    // Seed MCS with pre-colored parameters already visited so their uncolored
    // neighbors immediately accrue weight from pre-assigned parameter cliques.
    let mut weight: HashMap<ValueId, u32> = HashMap::with_capacity(n);
    let mut visited: HashSet<ValueId> = HashSet::with_capacity(n);
    let mut mcs_order: Vec<ValueId> = Vec::with_capacity(n);
    let mut heap: BinaryHeap<(u32, u32)> = BinaryHeap::with_capacity(n * 2);

    for &p in params {
        if val_set.contains(&p) && visited.insert(p) {
            mcs_order.push(p);
            if let Some(neighbors) = interference.get(&p) {
                for &nb in neighbors {
                    if !visited.contains(&nb) && val_set.contains(&nb) {
                        *weight.entry(nb).or_default() += 1;
                    }
                }
            }
        }
    }
    for &value in all_values {
        if !visited.contains(&value) {
            let w = weight.get(&value).copied().unwrap_or(0);
            heap.push((w, rank_of[&value]));
        }
    }

    while mcs_order.len() < n {
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

    // R3-X6: Greedy coloring in forward MCS simplicial-clique build order
    // (`&mcs_order`, NOT `.rev()`), which is reverse Perfect Elimination Order
    // and achieves optimal chordal coloring.
    let mut used_colors: HashSet<u16> = HashSet::new();
    for &v in &mcs_order {
        if allocation.contains_key(&v) {
            continue;
        }
        used_colors.clear();
        if let Some(neighbors) = interference.get(&v) {
            for nb in neighbors {
                if let Some(&RegSlot::Reg(color)) = allocation.get(nb) {
                    used_colors.insert(color);
                }
            }
        }

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
    exception_edges: &HashSet<(BlockId, BlockId)>,
    used: &HashSet<ValueId>,
) -> HashMap<(BlockId, BlockId), Vec<(ValueId, ValueId)>> {
    let mut copies: HashMap<(BlockId, BlockId), Vec<(ValueId, ValueId)>> = HashMap::new();

    for &bb in rpo {
        let is_handler = handler_blocks.contains(&bb);
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
                    // R3-M2: Exceptional edges (and any predecessor that also
                    // dispatches exceptionally to `bb`) lower via `handler_phi_stores`;
                    // pure normal edges into `bb` (e.g. loop back-edges inside a
                    // catch body) lower via standard edge copies.
                    if is_handler
                        && (edge.kind == EdgeKind::Exceptional
                            || exception_edges.contains(&(edge.from, bb)))
                    {
                        continue;
                    }
                    let src_color = allocation.get(src);
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

fn collect_handler_phi_stores(
    module: &Module,
    handler_blocks: &HashSet<BlockId>,
    exception_edges: &HashSet<(BlockId, BlockId)>,
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
                if edge.kind != EdgeKind::Exceptional
                    && !exception_edges.contains(&(edge.from, handler))
                {
                    continue; // pure normal edge into handler lowers via phi_copies (R3-M2)
                }
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
