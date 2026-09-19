//! Instruction selection: IR instructions → ArkCompiler bytecodes.
//!
//! Takes an IR function with register allocation results and produces
//! a sequence of ArkCompiler bytecodes per basic block.

use std::collections::HashMap;

use abcd_isa::{Bytecode, EntityId, EntityKind, Imm, Label, Reg};

use crate::entity::{Block, FuncId, Inst, StringId, Value};
use crate::inst::{BinOp, CallKind, InstData, PropKind, UnOp};
use crate::module::{Module, ValueDef};

use super::LowerError;
use super::copy_resolve::{CopyResolveError, emit_copy};
use super::regalloc::{self, RegAlloc, RegSlot};

/// Result of instruction selection for one function.
#[derive(Debug)]
pub struct IselResult {
    /// Bytecodes per block (in RPO order).
    pub block_codes: Vec<(Block, Vec<Bytecode>)>,
    /// String pool reverse map: StringId → EntityId for the output file.
    pub string_map: HashMap<StringId, EntityId>,
    /// Trace of every emitted entity operand, keyed by (entity kind, raw
    /// operand value). [`EntityTrace::Traced`] means the value is a
    /// source-file offset recorded by lift (string: via
    /// `module.string_entities`; method: carried on the defining IR
    /// instruction). [`EntityTrace::Untraced`] means at least one STRING use
    /// of the value fell back to the identity `EntityId(sid.0)` for an
    /// unmapped string (a hand-built module has no source file). An untraced
    /// use poisons the (kind, value) pair: identity relocation entries are
    /// only meaningful when every use of the value carries a real source
    /// offset. The key is kind-qualified so that an untraced StringId use of
    /// a raw value cannot poison a MethodId trace of the same number, and
    /// vice versa.
    pub entity_traces: HashMap<(EntityKind, u32), EntityTrace>,
    /// Total number of IC slots allocated for this function.
    pub ic_size: u32,
    pub unsupported: Option<String>,
}

/// Whether an emitted entity operand value is traceable to a source-file
/// offset recorded by lift (`module.string_entities`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EntityTrace {
    /// The operand value is the source-file offset recorded for the StringId.
    Traced,
    /// At least one use of this operand value had no recorded source offset
    /// and fell back to the identity `EntityId(sid.0)`.
    Untraced,
}

/// Resolves StringIds to emitted entity operand values and records whether
/// each emitted (kind, value) pair is traceable to a source-file offset.
struct EntityTracer<'a> {
    /// The caller-provided output map (may carry identity fallbacks).
    string_map: &'a HashMap<StringId, EntityId>,
    /// The module's own recorded source mappings (StringId → source offset).
    module_entities: &'a HashMap<StringId, EntityId>,
    traces: HashMap<(EntityKind, u32), EntityTrace>,
}

impl EntityTracer<'_> {
    /// Resolve `sid` exactly as the legacy `eid` helper did (string_map value,
    /// identity fallback), recording whether the emitted value is the
    /// module-recorded source offset. String operands only.
    fn eid(&mut self, sid: StringId) -> EntityId {
        let e = self
            .string_map
            .get(&sid)
            .copied()
            .unwrap_or(EntityId(sid.0));
        let traced = self.module_entities.get(&sid).copied() == Some(e);
        self.traces
            .entry((EntityKind::StringId, e.0))
            .and_modify(|t| {
                if !traced {
                    *t = EntityTrace::Untraced;
                }
            })
            .or_insert(if traced {
                EntityTrace::Traced
            } else {
                EntityTrace::Untraced
            });
        e
    }

    /// Emit a method-reference operand: the IR instruction carries the
    /// precise source-file offset of the referenced method (recorded by lift
    /// from the use-site's own `entity_offsets` entry), so the emitted value
    /// IS the source offset — by construction traced, never name-derived.
    /// `to_method_body` still validates the offset against the file's method
    /// set, so a hand-built module with a bogus offset is a hard error there.
    fn method_eid(&mut self, method_offset: u32) -> EntityId {
        self.traces
            .insert((EntityKind::MethodId, method_offset), EntityTrace::Traced);
        EntityId(method_offset)
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

/// Select instructions for a function.
pub fn select(
    module: &Module,
    func_id: FuncId,
    alloc: &RegAlloc,
    rpo: &[Block],
    string_map: &HashMap<StringId, EntityId>,
) -> Result<IselResult, LowerError> {
    let mut block_codes: Vec<(Block, Vec<Bytecode>)> = Vec::new();
    let mut ic = IcAllocator::new();
    let mut unsupported = None;
    let mut tracer = EntityTracer {
        string_map,
        module_entities: &module.string_entities,
        traces: HashMap::new(),
    };

    let entry_block = module.func(func_id).entry_block;

    // N13: handler block → its exception value. The exception is delivered
    // in acc by the dispatch itself; the prologue below materializes it
    // into its register home.
    let handler_exc: HashMap<Block, Value> = module
        .func(func_id)
        .exception_values
        .iter()
        .copied()
        .collect();
    // N21 pinned stores for handler-block phis, grouped by emission point.
    // Deterministic order: sorted by (pred, src, dst) / (src, dst).
    //
    // - AfterDef: the source is defined by an instruction inside the pred —
    //   the store is emitted immediately after that instruction (the
    //   closest implementable point to the vendored `sta`; if the source is
    //   Acc-colored its content is still physically in acc at that point —
    //   the instruction's own emission ends with store_result, which for an
    //   Acc home emits nothing — so `Sta(S)` reads the right value).
    // - BlockStart(pred): every other source — defined in a dominating
    //   block, a phi result (materialized by the incoming edge copies), a
    //   parameter (the entry copy-in prologue has run), or an exception
    //   value (the handler prologue has run). The store is emitted before
    //   the pred's first instruction, so an exception at any pred
    //   instruction observes it.
    let mut after_def_stores: HashMap<Value, Vec<(Value, Value)>> = HashMap::new();
    let mut block_start_stores: HashMap<Block, Vec<(Value, Value)>> = HashMap::new();
    for &(pred, src, dst) in &alloc.handler_phi_stores {
        let defined_in_pred = match module.value(src).def {
            ValueDef::Inst(i) => !module.inst(i).data.is_phi() && module.inst(i).block == pred,
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

    let acc_scratch_slot = alloc
        .low_scratch_base
        .map(|base| base + regalloc::LOW_OPERAND_SCRATCHES);

    for &bb in rpo {
        let mut codes = Vec::new();
        let block = module.block(bb);

        // Copy-in prologue: arguments arrive in the ABI top slots and are
        // moved into the parameters' vreg homes at the very start of the
        // entry block.
        if bb == entry_block {
            emit_param_copy_in(func_id, module, alloc, &mut codes)?;
        }

        // N13 handler prologue: exception dispatch physically delivers the
        // thrown object in acc (vendor `SET_ACC(exception)`,
        // interpreter_assembly.cpp:7860-7863) — materialize it into its
        // register home as the handler's FIRST bytecode, before anything
        // can clobber acc. This is exactly the vendored handler-entry
        // `sta vX`. Skipped when the handler never reads the exception (the
        // value is then uncolored).
        if let Some(&exc) = handler_exc.get(&bb) {
            if let Some(&home) = alloc.allocation.get(&exc) {
                if home != RegSlot::Acc {
                    emit_pinned_copy(func_id, RegSlot::Acc, home, acc_scratch_slot, &mut codes)?;
                }
            }
        }

        // N21 pinned stores at block start (phi-result / exception /
        // parameter sources). Runs after the exception prologue so a store
        // sourcing the exception reads its just-written home.
        if let Some(stores) = block_start_stores.get(&bb) {
            for &(src, dst) in stores {
                let s = slot_of(func_id, src, alloc)?;
                let d = slot_of(func_id, dst, alloc)?;
                if s != d {
                    emit_pinned_copy(func_id, s, d, acc_scratch_slot, &mut codes)?;
                }
            }
        }

        // Phi copies from predecessors are handled in layout (inserted before terminators).
        // Skip phi instructions — they don't produce bytecodes directly.

        for &inst in &block.insts {
            let node = module.inst(inst);
            if matches!(
                &node.data,
                InstData::LoadSuperProperty {
                    key: PropKind::ByIndex(_)
                } | InstData::StoreSuperProperty {
                    key: PropKind::ByIndex(_),
                    ..
                } | InstData::ThrowConstAssignment { .. }
            ) {
                unsupported = Some(match &node.data {
                    InstData::ThrowConstAssignment { .. } => "throw const assignment".to_string(),
                    _ => "super property access by index".to_string(),
                });
            }
            let result_slot = match node.result {
                Some(v) => Some(slot_of(func_id, v, alloc)?),
                None => None,
            };

            select_inst(
                &node.data,
                result_slot,
                inst,
                &block.insts,
                func_id,
                module,
                alloc,
                &mut tracer,
                &mut codes,
                &mut ic,
            )?;

            // N21 pinned stores right after the defining instruction (see
            // the ordering argument at `after_def_stores`).
            if let Some(v) = node.result {
                if let Some(stores) = after_def_stores.get(&v) {
                    for &(_, dst) in stores {
                        let d = slot_of(func_id, dst, alloc)?;
                        if let Some(s) = result_slot {
                            if s != d {
                                emit_pinned_copy(func_id, s, d, acc_scratch_slot, &mut codes)?;
                            }
                        }
                    }
                }
            }
        }

        block_codes.push((bb, codes));
    }

    Ok(IselResult {
        block_codes,
        string_map: string_map.clone(),
        entity_traces: tracer.traces,
        ic_size: ic.counter,
        unsupported,
    })
}

/// Emit the copy-in prologue at the very start of the entry block: for each
/// parameter `i`, `Mov(home_i, Reg(num_regs + i))` moves the ABI top slot
/// into the parameter's vreg home. The vendor frame is
/// `num_vregs + num_args` with arguments in the top slots
/// (static_core/runtime/include/method.h); `to_method_body` declares
/// `num_vregs = num_regs`, so the arg slots of the lowered frame start
/// exactly at `Reg(num_regs)`. `alloc.num_regs` is final here — it already
/// includes the `copy_temp`/`spill_slot` reservations.
///
/// `mcs_color` pre-assigns every parameter a register home, so an
/// Acc-colored parameter can only come from a hand-crafted allocation;
/// both that and an uncolored parameter are hard errors, never a silent
/// path.
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
    let func = module.func(func_id);
    for (i, &val) in func.param_values.iter().enumerate() {
        let home = match alloc.allocation.get(&val).copied() {
            Some(RegSlot::Reg(r)) => r,
            Some(RegSlot::Acc) => {
                return Err(LowerError::AccColoredParam {
                    func: func_id,
                    value: val,
                });
            }
            None => {
                return Err(LowerError::UnallocatedOperand {
                    func: func_id,
                    value: val,
                });
            }
        };
        let arg_slot = u32::from(alloc.num_regs) + i as u32;
        if arg_slot > u32::from(u16::MAX) {
            return Err(LowerError::RegisterOverflow(func_id));
        }
        codes.push(Bytecode::Mov(Reg(home), Reg(arg_slot as u16)));
    }
    Ok(())
}

/// Emit one pinned slot copy (the N13 handler exception prologue or an N21
/// handler-phi write-through store), routing acc↔high-register traffic
/// through the reserved low scratch (`sta`/`lda` are op_v_8-only; S2). A
/// single copy never cycles, so `CycleNeedsTemp` is unreachable; both error
/// arms still map to hard errors, never a silent drop.
fn emit_pinned_copy(
    func_id: FuncId,
    src: RegSlot,
    dst: RegSlot,
    acc_scratch: Option<u16>,
    codes: &mut Vec<Bytecode>,
) -> Result<(), LowerError> {
    let emitted = emit_copy(src, dst, acc_scratch).map_err(|e| match e {
        CopyResolveError::CycleNeedsTemp => LowerError::MissingCopyTemp(func_id),
        CopyResolveError::HighRegNeedsScratch => LowerError::MissingLowScratch(func_id),
    })?;
    codes.extend(emitted);
    Ok(())
}

/// Look up the slot register allocation assigned to a value. A missing entry
/// means the operand was never colored (e.g. a dangling value reference in
/// unverified IR), which the old code silently treated as acc-resident.
fn slot_of(func_id: FuncId, val: Value, alloc: &RegAlloc) -> Result<RegSlot, LowerError> {
    alloc
        .allocation
        .get(&val)
        .copied()
        .ok_or(LowerError::UnallocatedOperand {
            func: func_id,
            value: val,
        })
}

/// Get the Reg for a value, spilling an acc-resident value into the reserved
/// in-frame spill slot (`Sta`) when needed.
///
/// High-register routing (S2): `sta`/`lda` are `op_v_8`-only in the vendored
/// ISA and — except for the auto-widening `mov` — every register operand
/// slot isel emits is u8-only as well (isa.yaml format audit: all `v`/`vN`
/// operands are `_8`; the `op_imm_16_v_8`-style second formats widen only
/// the imm). A value colored to a register ≥ 256 is therefore routed
/// through the reserved LOW scratch block (`RegAlloc::low_scratch_base`):
/// register operands via `mov scratch[i], high` (one scratch per operand
/// position, so simultaneous operands never alias), acc spills via
/// `sta scratch[i]`. `operand_idx` is the operand's position within its
/// instruction.
fn val_reg(
    func_id: FuncId,
    val: Value,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
    operand_idx: usize,
) -> Result<Reg, LowerError> {
    match slot_of(func_id, val, alloc)? {
        RegSlot::Reg(r) if r <= 255 => Ok(Reg(r)),
        RegSlot::Reg(r) => {
            let scratch = operand_scratch(func_id, alloc, operand_idx)?;
            codes.push(Bytecode::Mov(scratch, Reg(r)));
            Ok(scratch)
        }
        RegSlot::Acc => {
            // Value is in acc — spill it to a reserved register. In
            // high-register mode that is the operand's low scratch (the
            // operand slot is u8-only anyway); otherwise it is the
            // top-of-frame spill slot. At most one operand per instruction
            // is Acc-colored (interference invariant, see
            // `materialize_operands`), so one slot per position suffices.
            let scratch = spill_scratch(func_id, alloc, operand_idx)?;
            codes.push(Bytecode::Sta(scratch));
            Ok(scratch)
        }
    }
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

/// The scratch an Acc-colored operand spills into: the operand's low
/// scratch in high-register mode, the reserved top-of-frame spill slot
/// otherwise.
fn spill_scratch(func_id: FuncId, alloc: &RegAlloc, idx: usize) -> Result<Reg, LowerError> {
    if alloc.low_scratch_base.is_some() {
        return operand_scratch(func_id, alloc, idx);
    }
    match alloc.spill_slot {
        Some(RegSlot::Reg(r)) => Ok(Reg(r)),
        _ => Err(LowerError::MissingSpillSlot(func_id)),
    }
}

/// The reserved low acc-routing scratch (high-register mode).
fn acc_scratch(func_id: FuncId, alloc: &RegAlloc) -> Result<Reg, LowerError> {
    alloc
        .low_scratch_base
        .map(|base| Reg(base + regalloc::LOW_OPERAND_SCRATCHES))
        .ok_or(LowerError::MissingLowScratch(func_id))
}

/// Ensure a value is in the accumulator. If it's in a register, emit lda;
/// a high register first detours through the reserved low acc scratch
/// (`mov scratch, high; lda scratch`).
fn ensure_acc(
    func_id: FuncId,
    val: Value,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<(), LowerError> {
    match slot_of(func_id, val, alloc)? {
        RegSlot::Reg(r) if r <= 255 => {
            codes.push(Bytecode::Lda(Reg(r)));
        }
        RegSlot::Reg(r) => {
            let scratch = acc_scratch(func_id, alloc)?;
            codes.push(Bytecode::Mov(scratch, Reg(r)));
            codes.push(Bytecode::Lda(scratch));
        }
        RegSlot::Acc => {
            // Already in acc, nothing to do.
        }
    }
    Ok(())
}

/// Materialize one instruction's operands in spill-before-load order.
///
/// (a) Resolve every register operand first: the — at most one —
///     Acc-colored register operand is spilled into the reserved in-frame
///     spill slot via `Sta`, which reads but never clobbers the acc.
/// (b) Only then bring the acc operand into the accumulator (`Lda` unless
///     it is the acc-resident value itself).
///
/// The invariant that makes a single spill slot sufficient comes from the
/// interference construction in `regalloc::build_interference`: all operands
/// of one instruction are simultaneously live at that instruction, hence
/// pairwise interfere (the later-defined operand's definition point sees the
/// other operand live), hence the greedy coloring can assign `RegSlot::Acc`
/// to at most one of them. A hand-crafted allocation may violate it; rather
/// than emitting a spill sequence that would overwrite the first spill,
/// selection fails hard.
fn materialize_operands(
    func_id: FuncId,
    reg_operands: &[Value],
    acc_operand: Option<Value>,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<Vec<Reg>, LowerError> {
    let mut acc_colored: Option<Value> = None;
    for &v in reg_operands.iter().chain(acc_operand.iter()) {
        if matches!(alloc.allocation.get(&v), Some(RegSlot::Acc)) {
            match acc_colored {
                None => acc_colored = Some(v),
                Some(prev) if prev != v => {
                    return Err(LowerError::MultipleAccOperands {
                        func: func_id,
                        a: prev,
                        b: v,
                    });
                }
                Some(_) => {}
            }
        }
    }

    let mut regs = Vec::with_capacity(reg_operands.len());
    for (idx, &v) in reg_operands.iter().enumerate() {
        regs.push(val_reg(func_id, v, alloc, codes, idx)?);
    }
    if let Some(acc_val) = acc_operand {
        ensure_acc(func_id, acc_val, alloc, codes)?;
    }
    Ok(regs)
}

/// If the result should go to a register (not acc), emit sta; a high
/// register detours through the reserved low acc scratch
/// (`sta scratch; mov high, scratch`).
fn store_result(
    func_id: FuncId,
    result_slot: Option<RegSlot>,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<(), LowerError> {
    match result_slot {
        Some(RegSlot::Reg(r)) if r <= 255 => codes.push(Bytecode::Sta(Reg(r))),
        Some(RegSlot::Reg(r)) => {
            let scratch = acc_scratch(func_id, alloc)?;
            codes.push(Bytecode::Sta(scratch));
            codes.push(Bytecode::Mov(Reg(r), scratch));
        }
        _ => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{LowerError, RegAlloc, RegSlot, ensure_acc, materialize_operands, val_reg};
    use crate::entity::{FuncId, Value};
    use abcd_isa::{Bytecode, Reg};
    use std::collections::HashMap;

    const F: FuncId = FuncId(0);

    fn alloc_with(slots: &[(Value, RegSlot)], spill_slot: Option<RegSlot>) -> RegAlloc {
        RegAlloc {
            allocation: slots.iter().copied().collect(),
            phi_copies: HashMap::new(),
            handler_phi_stores: Vec::new(),
            num_regs: 8,
            copy_temp: None,
            spill_slot,
            call_window_base: None,
            low_scratch_base: None,
        }
    }

    #[test]
    fn acc_operand_spills_into_the_reserved_in_frame_slot() {
        let v = Value::from_index(1);
        let alloc = alloc_with(&[(v, RegSlot::Acc)], Some(RegSlot::Reg(7)));
        let mut codes = Vec::new();
        let r = val_reg(F, v, &alloc, &mut codes, 0).expect("spill must succeed");
        assert_eq!(r, Reg(7));
        assert!(
            matches!(codes.as_slice(), [Bytecode::Sta(Reg(7))]),
            "expected a single Sta into the reserved slot, got {codes:?}"
        );
    }

    #[test]
    fn reg_colored_operand_passes_through_without_emission() {
        let v = Value::from_index(1);
        let alloc = alloc_with(&[(v, RegSlot::Reg(2))], None);
        let mut codes = Vec::new();
        let r = val_reg(F, v, &alloc, &mut codes, 0).expect("reg operand must resolve");
        assert_eq!(r, Reg(2));
        assert!(codes.is_empty(), "no lda/sta expected, got {codes:?}");
    }

    #[test]
    fn acc_spill_without_reserved_slot_is_a_hard_error() {
        let v = Value::from_index(1);
        let alloc = alloc_with(&[(v, RegSlot::Acc)], None);
        let mut codes = Vec::new();
        assert!(
            matches!(
                val_reg(F, v, &alloc, &mut codes, 0),
                Err(LowerError::MissingSpillSlot(_))
            ),
            "an Acc-colored register operand with no reserved spill slot must fail"
        );
    }

    #[test]
    fn unallocated_operand_is_a_hard_error_not_silent_acc() {
        let alloc = alloc_with(&[], None);
        let mut codes = Vec::new();
        let dangling = Value::from_index(42);
        assert!(matches!(
            val_reg(F, dangling, &alloc, &mut codes, 0),
            Err(LowerError::UnallocatedOperand { value, .. }) if value == dangling
        ));
        assert!(matches!(
            ensure_acc(F, dangling, &alloc, &mut codes),
            Err(LowerError::UnallocatedOperand { value, .. }) if value == dangling
        ));
    }

    #[test]
    fn spill_is_emitted_before_the_acc_load() {
        // obj is Acc-colored and needed as a register operand; key is
        // Reg-colored and needed in acc. The Sta must precede the Lda, or
        // the spill would capture the key (B3).
        let obj = Value::from_index(1);
        let key = Value::from_index(2);
        let alloc = alloc_with(
            &[(obj, RegSlot::Acc), (key, RegSlot::Reg(0))],
            Some(RegSlot::Reg(7)),
        );
        let mut codes = Vec::new();
        let regs = materialize_operands(F, &[obj], Some(key), &alloc, &mut codes)
            .expect("materialization must succeed");
        assert_eq!(regs, vec![Reg(7)]);
        assert!(
            matches!(
                codes.as_slice(),
                [Bytecode::Sta(Reg(7)), Bytecode::Lda(Reg(0))]
            ),
            "expected Sta(spill) then Lda(key), got {codes:?}"
        );
    }

    #[test]
    fn acc_resident_acc_operand_emits_no_load() {
        // The unique Acc-colored value is the acc operand: nothing to spill,
        // nothing to load.
        let k = Value::from_index(1);
        let o = Value::from_index(2);
        let alloc = alloc_with(
            &[(k, RegSlot::Acc), (o, RegSlot::Reg(0))],
            Some(RegSlot::Reg(7)),
        );
        let mut codes = Vec::new();
        let regs = materialize_operands(F, &[o], Some(k), &alloc, &mut codes)
            .expect("materialization must succeed");
        assert_eq!(regs, vec![Reg(0)]);
        assert!(codes.is_empty(), "no lda/sta expected, got {codes:?}");
    }

    #[test]
    fn the_same_acc_value_as_reg_and_acc_operand_spills_once() {
        let v = Value::from_index(1);
        let alloc = alloc_with(&[(v, RegSlot::Acc)], Some(RegSlot::Reg(7)));
        let mut codes = Vec::new();
        let regs = materialize_operands(F, &[v], Some(v), &alloc, &mut codes)
            .expect("one value in both roles is not a conflict");
        assert_eq!(regs, vec![Reg(7)]);
        assert!(matches!(codes.as_slice(), [Bytecode::Sta(Reg(7))]));
    }

    #[test]
    fn two_distinct_acc_colored_operands_are_rejected() {
        // Violates the interference invariant (possible only with a
        // hand-crafted allocation); must fail instead of overwriting the
        // first spill with the second.
        let a = Value::from_index(1);
        let b = Value::from_index(2);
        let alloc = alloc_with(
            &[(a, RegSlot::Acc), (b, RegSlot::Acc)],
            Some(RegSlot::Reg(7)),
        );
        let mut codes = Vec::new();
        assert!(matches!(
            materialize_operands(F, &[a], Some(b), &alloc, &mut codes),
            Err(LowerError::MultipleAccOperands { .. })
        ));
        assert!(matches!(
            materialize_operands(F, &[a, b], None, &alloc, &mut codes),
            Err(LowerError::MultipleAccOperands { .. })
        ));
    }
}

/// Select bytecodes for a single IR instruction.
///
/// `inst` and `block_insts` (the owning block's instruction list) are
/// needed by the CondBranch compare-fusion soundness checks: fusion
/// re-reads another instruction's operands, which is only valid when the
/// comparison chain sits immediately before the branch in the same block.
#[allow(clippy::too_many_arguments)]
fn select_inst(
    data: &InstData,
    result_slot: Option<RegSlot>,
    inst: Inst,
    block_insts: &[Inst],
    func_id: FuncId,
    module: &Module,
    alloc: &RegAlloc,
    tracer: &mut EntityTracer,
    codes: &mut Vec<Bytecode>,
    ic: &mut IcAllocator,
) -> Result<(), LowerError> {
    match data {
        // ── Literals ─────────────────────────────────────────────────
        InstData::LiteralUndefined => {
            codes.push(Bytecode::Ldundefined);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::LiteralNull => {
            codes.push(Bytecode::Ldnull);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::LiteralBool(true) => {
            codes.push(Bytecode::Ldtrue);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::LiteralBool(false) => {
            codes.push(Bytecode::Ldfalse);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::LiteralNumber(n) => {
            let bits = n.to_bits();
            if *n == (*n as i32) as f64 {
                codes.push(Bytecode::Ldai(Imm(*n as i64)));
            } else {
                codes.push(Bytecode::Fldai(Imm(bits as i64)));
            }
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::LiteralString(s) => {
            codes.push(Bytecode::LdaStr(tracer.eid(*s)));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::LiteralNaN => {
            codes.push(Bytecode::Ldnan);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::LiteralInfinity => {
            codes.push(Bytecode::Ldinfinity);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::LiteralHole => {
            codes.push(Bytecode::Ldhole);
            store_result(func_id, result_slot, alloc, codes)?;
        }

        // ── Binary operations ────────────────────────────────────────
        InstData::BinaryOp { op, left, right } => {
            let regs = materialize_operands(func_id, &[*right], Some(*left), alloc, codes)?;
            let r = regs[0];
            let bc = match op {
                BinOp::Add => Bytecode::Add2(ic.one(), r),
                BinOp::Sub => Bytecode::Sub2(ic.one(), r),
                BinOp::Mul => Bytecode::Mul2(ic.one(), r),
                BinOp::Div => Bytecode::Div2(ic.one(), r),
                BinOp::Mod => Bytecode::Mod2(ic.one(), r),
                BinOp::Exp => Bytecode::Exp(ic.one(), r),
                BinOp::Eq => Bytecode::Eq(ic.one(), r),
                BinOp::NotEq => Bytecode::Noteq(ic.one(), r),
                BinOp::StrictEq => Bytecode::Stricteq(ic.one(), r),
                BinOp::StrictNotEq => Bytecode::Strictnoteq(ic.one(), r),
                BinOp::Less => Bytecode::Less(ic.one(), r),
                BinOp::LessEq => Bytecode::Lesseq(ic.one(), r),
                BinOp::Greater => Bytecode::Greater(ic.one(), r),
                BinOp::GreaterEq => Bytecode::Greatereq(ic.one(), r),
                BinOp::Shl => Bytecode::Shl2(ic.one(), r),
                BinOp::Shr => Bytecode::Shr2(ic.one(), r),
                BinOp::Ashr => Bytecode::Ashr2(ic.one(), r),
                BinOp::BitAnd => Bytecode::And2(ic.one(), r),
                BinOp::BitOr => Bytecode::Or2(ic.one(), r),
                BinOp::BitXor => Bytecode::Xor2(ic.one(), r),
                BinOp::In => Bytecode::Isin(ic.one(), r),
                BinOp::InstanceOf => Bytecode::Instanceof(ic.one(), r),
            };
            codes.push(bc);
            store_result(func_id, result_slot, alloc, codes)?;
        }

        // ── Unary operations ─────────────────────────────────────────
        InstData::UnaryOp { op, operand } => {
            ensure_acc(func_id, *operand, alloc, codes)?;
            let bc = match op {
                UnOp::Minus => Bytecode::Neg(ic.one()),
                UnOp::LogicalNot => Bytecode::Not(ic.one()),
                UnOp::Inc => Bytecode::Inc(ic.one()),
                UnOp::Dec => Bytecode::Dec(ic.one()),
                UnOp::TypeOf => Bytecode::Typeof(ic.one()),
                UnOp::ToNumber => Bytecode::Tonumber(ic.one()),
                UnOp::ToNumeric => Bytecode::Tonumeric(ic.one()),
                UnOp::BitNot => Bytecode::Not(ic.one()), // approximate
                UnOp::Void => Bytecode::Ldundefined,     // void x → undefined
            };
            codes.push(bc);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::IsTrue { operand } => {
            ensure_acc(func_id, *operand, alloc, codes)?;
            codes.push(Bytecode::Istrue);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::IsFalse { operand } => {
            ensure_acc(func_id, *operand, alloc, codes)?;
            codes.push(Bytecode::Isfalse);
            store_result(func_id, result_slot, alloc, codes)?;
        }

        // ── Object / Array creation ──────────────────────────────────
        InstData::CreateEmptyObject => {
            codes.push(Bytecode::Createemptyobject);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::CreateEmptyArray => {
            codes.push(Bytecode::Createemptyarray(ic.one()));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::CreateArrayWithBuffer { literal_array } => {
            let la_eid = EntityId(*literal_array);
            codes.push(Bytecode::Createarraywithbuffer(ic.one(), la_eid));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::CreateObjectWithBuffer { literal_array } => {
            let la_eid = EntityId(*literal_array);
            codes.push(Bytecode::Createobjectwithbuffer(ic.one(), la_eid));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::CreateRegExp { pattern, flags } => {
            let p = tracer.eid(*pattern);
            let f_str = module.strings.get(*flags);
            let f_val: i64 = f_str.parse().unwrap_or(0);
            codes.push(Bytecode::Createregexpwithliteral(ic.one(), p, Imm(f_val)));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::CreateObjectWithExcludedKeys { obj, keys } => {
            // Only the object and the first key are register operands that
            // need materialization; the remaining keys are assumed to occupy
            // consecutive registers (approximate, pre-existing).
            let mut reg_operands = vec![*obj];
            if let Some(first) = keys.first() {
                reg_operands.push(*first);
            }
            let regs = materialize_operands(func_id, &reg_operands, None, alloc, codes)?;
            let obj_r = regs[0];
            let start_r = if keys.is_empty() { Reg(0) } else { regs[1] };
            codes.push(Bytecode::Createobjectwithexcludedkeys(
                Imm(keys.len() as i64),
                obj_r,
                start_r,
            ));
            store_result(func_id, result_slot, alloc, codes)?;
        }

        // ── Property access ──────────────────────────────────────────
        InstData::LoadProperty { object, key } => {
            match key {
                PropKind::ByName(name) => {
                    ensure_acc(func_id, *object, alloc, codes)?;
                    codes.push(Bytecode::Ldobjbyname(ic.two(), tracer.eid(*name)));
                }
                PropKind::ByValue(k) => {
                    let regs = materialize_operands(func_id, &[*object], Some(*k), alloc, codes)?;
                    codes.push(Bytecode::Ldobjbyvalue(ic.two(), regs[0]));
                }
                PropKind::ByIndex(idx) => {
                    ensure_acc(func_id, *object, alloc, codes)?;
                    codes.push(Bytecode::Ldobjbyindex(ic.two(), Imm(*idx as i64)));
                }
            }
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::StoreProperty { object, key, value } => match key {
            PropKind::ByName(name) => {
                let regs = materialize_operands(func_id, &[*object], Some(*value), alloc, codes)?;
                codes.push(Bytecode::Stobjbyname(ic.two(), tracer.eid(*name), regs[0]));
            }
            PropKind::ByValue(k) => {
                let regs =
                    materialize_operands(func_id, &[*object, *value], Some(*k), alloc, codes)?;
                codes.push(Bytecode::Stobjbyvalue(ic.two(), regs[0], regs[1]));
            }
            PropKind::ByIndex(idx) => {
                let regs = materialize_operands(func_id, &[*object], Some(*value), alloc, codes)?;
                codes.push(Bytecode::Stobjbyindex(ic.two(), regs[0], Imm(*idx as i64)));
            }
        },
        InstData::StoreOwnProperty { object, key, value } => match key {
            PropKind::ByName(name) => {
                let regs = materialize_operands(func_id, &[*object], Some(*value), alloc, codes)?;
                codes.push(Bytecode::Stownbyname(ic.two(), tracer.eid(*name), regs[0]));
            }
            PropKind::ByValue(k) => {
                let regs =
                    materialize_operands(func_id, &[*object, *k], Some(*value), alloc, codes)?;
                codes.push(Bytecode::Stownbyvalue(ic.two(), regs[0], regs[1]));
            }
            PropKind::ByIndex(idx) => {
                let regs = materialize_operands(func_id, &[*object], Some(*value), alloc, codes)?;
                codes.push(Bytecode::Stownbyindex(ic.two(), regs[0], Imm(*idx as i64)));
            }
        },
        InstData::DeleteProperty { object, key } => {
            let regs = materialize_operands(func_id, &[*key], Some(*object), alloc, codes)?;
            codes.push(Bytecode::Delobjprop(regs[0]));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::CopyDataProperties { dst, src } => {
            // Vendor `copydataproperties v:in:top, acc: inout:top`: the
            // register operand is the target, the accumulator carries the
            // source (and receives the result). Spill-before-load order
            // via materialize_operands: dst is resolved first (an
            // Acc-colored dst spills through the reserved slot), then src
            // is brought into acc. No entity operands — nothing for the
            // tracer/relocation channel. Both vendor forms lower to the
            // modern opcode (the codebase's deprecated-opcode convention).
            let regs = materialize_operands(func_id, &[*dst], Some(*src), alloc, codes)?;
            codes.push(Bytecode::Copydataproperties(regs[0]));
        }
        InstData::LoadSuperProperty { key } => {
            match key {
                PropKind::ByName(name) => {
                    codes.push(Bytecode::Ldsuperbyname(ic.two(), tracer.eid(*name)));
                }
                PropKind::ByValue(k) => {
                    let key_r = val_reg(func_id, *k, alloc, codes, 0)?;
                    codes.push(Bytecode::Ldsuperbyvalue(ic.two(), key_r));
                }
                PropKind::ByIndex(_) => {
                    // No direct bytecode; approximate with ByValue
                }
            }
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::StoreSuperProperty { key, value } => match key {
            PropKind::ByName(name) => {
                let val_r = val_reg(func_id, *value, alloc, codes, 0)?;
                codes.push(Bytecode::Stsuperbyname(ic.two(), tracer.eid(*name), val_r));
            }
            PropKind::ByValue(k) => {
                let regs = materialize_operands(func_id, &[*k, *value], None, alloc, codes)?;
                codes.push(Bytecode::Stsuperbyvalue(ic.two(), regs[0], regs[1]));
            }
            PropKind::ByIndex(_) => {}
        },

        // ── Global variables ─────────────────────────────────────────
        InstData::LoadGlobalVar { name } => {
            codes.push(Bytecode::Ldglobalvar(ic.one(), tracer.eid(*name)));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::StoreGlobalVar { name, value } => {
            ensure_acc(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Stglobalvar(ic.one(), tracer.eid(*name)));
        }
        InstData::TryLoadGlobalByName { name } => {
            codes.push(Bytecode::Tryldglobalbyname(ic.one(), tracer.eid(*name)));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::TryStoreGlobalByName { name, value } => {
            ensure_acc(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Trystglobalbyname(ic.one(), tracer.eid(*name)));
        }

        // ── Lexical variables ────────────────────────────────────────
        InstData::LoadLexVar { level, slot } => {
            codes.push(Bytecode::Ldlexvar(Imm(*level as i64), Imm(*slot as i64)));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::StoreLexVar { level, slot, value } => {
            ensure_acc(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Stlexvar(Imm(*level as i64), Imm(*slot as i64)));
        }
        InstData::NewLexEnv { num_vars } => {
            codes.push(Bytecode::Newlexenv(Imm(*num_vars as i64)));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::NewLexEnvWithName {
            num_vars,
            scope_literal_array,
        } => {
            codes.push(Bytecode::Newlexenvwithname(
                Imm(*num_vars as i64),
                EntityId(*scope_literal_array),
            ));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::PopLexEnv => {
            codes.push(Bytecode::Poplexenv);
        }

        // ── Module variables ─────────────────────────────────────────
        InstData::LoadLocalModuleVar { index } => {
            codes.push(Bytecode::Ldlocalmodulevar(Imm(*index as i64)));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::LoadExternalModuleVar { index } => {
            codes.push(Bytecode::Ldexternalmodulevar(Imm(*index as i64)));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::StoreModuleVar { index, value } => {
            ensure_acc(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Stmodulevar(Imm(*index as i64)));
        }
        InstData::GetModuleNamespace { index } => {
            codes.push(Bytecode::Getmodulenamespace(Imm(*index as i64)));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::DynamicImport { specifier } => {
            ensure_acc(func_id, *specifier, alloc, codes)?;
            codes.push(Bytecode::Dynamicimport);
            store_result(func_id, result_slot, alloc, codes)?;
        }

        // ── Function / Class definition ──────────────────────────────
        InstData::DefineFunc {
            method_offset,
            length,
            ..
        } => {
            codes.push(Bytecode::Definefunc(
                ic.one(),
                tracer.method_eid(*method_offset),
                Imm(*length as i64),
            ));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::DefineMethod {
            method_offset,
            length,
            home_object,
            ..
        } => {
            ensure_acc(func_id, *home_object, alloc, codes)?;
            codes.push(Bytecode::Definemethod(
                ic.one(),
                tracer.method_eid(*method_offset),
                Imm(*length as i64),
            ));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::DefineClassWithBuffer {
            method_offset,
            literal_array,
            base,
            ..
        } => {
            let base_r = val_reg(func_id, *base, alloc, codes, 0)?;
            codes.push(Bytecode::Defineclasswithbuffer(
                ic.one(),
                tracer.method_eid(*method_offset),
                EntityId(*literal_array),
                Imm(0),
                base_r,
            ));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::DefineGetterSetterByValue {
            obj,
            key,
            getter,
            setter,
        } => {
            let regs =
                materialize_operands(func_id, &[*obj, *key, *getter, *setter], None, alloc, codes)?;
            codes.push(Bytecode::Definegettersetterbyvalue(
                regs[0], regs[1], regs[2], regs[3],
            ));
            store_result(func_id, result_slot, alloc, codes)?;
        }

        // ── Calls ────────────────────────────────────────────────────
        InstData::Call { kind, callee, args } => {
            select_call(*kind, *callee, args, func_id, alloc, codes, ic)?;
            store_result(func_id, result_slot, alloc, codes)?;
        }

        // ── Special value loaders ────────────────────────────────────
        InstData::LoadThis => {
            codes.push(Bytecode::Ldthis);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::LoadNewTarget => {
            codes.push(Bytecode::Ldnewtarget);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::LoadGlobalObject => {
            codes.push(Bytecode::Ldglobal);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::LoadFunction => {
            codes.push(Bytecode::Ldfunction);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::GetUnmappedArgs => {
            codes.push(Bytecode::Getunmappedargs);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::CopyRestArgs { start_index } => {
            codes.push(Bytecode::Copyrestargs(Imm(*start_index as i64)));
            store_result(func_id, result_slot, alloc, codes)?;
        }

        // ── Iterators ────────────────────────────────────────────────
        InstData::GetIterator { obj } => {
            ensure_acc(func_id, *obj, alloc, codes)?;
            codes.push(Bytecode::Getiterator(ic.two()));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::GetAsyncIterator { obj } => {
            ensure_acc(func_id, *obj, alloc, codes)?;
            codes.push(Bytecode::Getasynciterator(ic.two()));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::GetPropIterator { obj } => {
            ensure_acc(func_id, *obj, alloc, codes)?;
            codes.push(Bytecode::Getpropiterator);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::CloseIterator { iterator } => {
            let iter_r = val_reg(func_id, *iterator, alloc, codes, 0)?;
            codes.push(Bytecode::Closeiterator(ic.two(), iter_r));
            store_result(func_id, result_slot, alloc, codes)?;
        }

        // ── Generator / Async ────────────────────────────────────────
        InstData::CreateGeneratorObj { func } => {
            let func_r = val_reg(func_id, *func, alloc, codes, 0)?;
            codes.push(Bytecode::Creategeneratorobj(func_r));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::SuspendGenerator { genobj, value } => {
            // Vendor `suspendgenerator v:in:top, acc: inout:top`
            // (isa.yaml:1302-1305): the register operand is the generator
            // object, the acc carries the yield value (and receives the
            // resume result). Spill-before-load (B3): resolve the register
            // operand first via materialize_operands, ensure_acc the
            // yield value LAST. No entity operands.
            let regs = materialize_operands(func_id, &[*genobj], Some(*value), alloc, codes)?;
            codes.push(Bytecode::Suspendgenerator(regs[0]));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::ResumeGenerator { genobj } => {
            // Vendor `resumegenerator` (isa.yaml:1261-1264):
            // `acc: inout:top`, no register operand — genobj in acc,
            // resume result back to acc.
            ensure_acc(func_id, *genobj, alloc, codes)?;
            codes.push(Bytecode::Resumegenerator);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::GetResumeMode { genobj } => {
            // Vendor `getresumemode` (isa.yaml:1270-1273):
            // `acc: inout:top`, no register operand — genobj in acc,
            // resume mode back to acc.
            ensure_acc(func_id, *genobj, alloc, codes)?;
            codes.push(Bytecode::Getresumemode);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::AsyncFunctionEnter => {
            codes.push(Bytecode::Asyncfunctionenter);
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::AsyncFunctionAwaitUncaught { value } => {
            let val_r = val_reg(func_id, *value, alloc, codes, 0)?;
            codes.push(Bytecode::Asyncfunctionawaituncaught(val_r));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::AsyncFunctionResolve { value } => {
            let val_r = val_reg(func_id, *value, alloc, codes, 0)?;
            codes.push(Bytecode::Asyncfunctionresolve(val_r));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::AsyncFunctionReject { value } => {
            let val_r = val_reg(func_id, *value, alloc, codes, 0)?;
            codes.push(Bytecode::Asyncfunctionreject(val_r));
            store_result(func_id, result_slot, alloc, codes)?;
        }
        InstData::CreateIterResultObj { value, done } => {
            let regs = materialize_operands(func_id, &[*value, *done], None, alloc, codes)?;
            codes.push(Bytecode::Createiterresultobj(regs[0], regs[1]));
            store_result(func_id, result_slot, alloc, codes)?;
        }

        // ── Exception handling ───────────────────────────────────────
        InstData::Throw { value } => {
            ensure_acc(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Throw);
        }
        InstData::ThrowIfNotObject { value } => {
            let val_r = val_reg(func_id, *value, alloc, codes, 0)?;
            codes.push(Bytecode::ThrowIfnotobject(val_r));
        }
        InstData::ThrowConstAssignment { .. } => {
            // ThrowConstassignment takes a Reg; use a dummy
            codes.push(Bytecode::ThrowConstassignment(Reg(0)));
        }
        InstData::ThrowUndefinedIfHole { name, value } => {
            // ThrowUndefinedifholewithname reads the value from the acc.
            ensure_acc(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::ThrowUndefinedifholewithname(tracer.eid(*name)));
        }
        InstData::ThrowIfSuperNotCorrectCall { value } => {
            ensure_acc(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::ThrowIfsupernotcorrectcall(Imm(0)));
        }
        InstData::ThrowNotExists => {
            codes.push(Bytecode::ThrowNotexists);
        }
        InstData::ThrowPatternNonCoercible => {
            codes.push(Bytecode::ThrowPatternnoncoercible);
        }
        InstData::ThrowDeleteSuperProperty => {
            codes.push(Bytecode::ThrowDeletesuperproperty);
        }

        // ── Terminators ──────────────────────────────────────────────
        // Branch/CondBranch are handled in layout.rs (jump target resolution).
        // We emit placeholder labels here; layout will fix them.
        InstData::Branch { dest } => {
            codes.push(Bytecode::Jmp(Label(dest.0)));
        }
        InstData::CondBranch {
            cond,
            true_dest,
            false_dest,
        } => {
            // Try compare-branch fusion: if cond is IsTrue(CmpOp(a, b)),
            // emit a fused Jeq/Jne/Jstricteq/Jnstricteq instead of Jnez.
            // Fusion re-reads the COMPARISON's operands at this branch, so
            // it fires only when that re-read is provably sound (S6; see
            // try_fuse_cmp_branch). Otherwise fall back to the unfused
            // path, which is sound: `cond` is the branch's own operand —
            // physically in acc right after its definition (Acc-colored)
            // or reloaded from its register (Reg-colored).
            if let Some(fused) = try_fuse_cmp_branch(
                *cond,
                *true_dest,
                inst,
                block_insts,
                func_id,
                module,
                alloc,
                codes,
            )? {
                codes.push(fused);
            } else {
                ensure_acc(func_id, *cond, alloc, codes)?;
                // Emit: if acc truthy → jump to true_dest, fall through to false_dest
                codes.push(Bytecode::Jnez(Label(true_dest.0)));
            }
            // The fall-through to false_dest is implicit if it's the next block.
            // Layout will insert a Jmp if needed.
            let _ = false_dest;
        }
        InstData::Return { value } => {
            if let Some(val) = value {
                ensure_acc(func_id, *val, alloc, codes)?;
                codes.push(Bytecode::Return);
            } else {
                codes.push(Bytecode::Returnundefined);
            }
        }
        InstData::Unreachable => {
            codes.push(Bytecode::Returnundefined);
        }

        // ── Phi / Debug ──────────────────────────────────────────────
        InstData::Phi { .. } => {
            // Handled by phi elimination, not emitted directly.
        }
        InstData::Debugger => {
            codes.push(Bytecode::Debugger);
        }
    }
    Ok(())
}

/// Select call bytecodes based on kind and argument count.
///
/// Every arm materializes operands in spill-before-load order: the argument
/// registers are resolved first (spilling the at-most-one Acc-colored
/// register operand), then the callee is brought into the acc.
fn select_call(
    kind: CallKind,
    callee: Value,
    args: &[Value],
    func_id: FuncId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
    ic: &mut IcAllocator,
) -> Result<(), LowerError> {
    match kind {
        CallKind::Call => match args.len() {
            0 => {
                materialize_operands(func_id, &[], Some(callee), alloc, codes)?;
                codes.push(Bytecode::Callarg0(ic.two()));
            }
            n @ (1..=3) => {
                let regs = materialize_operands(func_id, args, Some(callee), alloc, codes)?;
                let bc = match n {
                    1 => Bytecode::Callarg1(ic.two(), regs[0]),
                    2 => Bytecode::Callargs2(ic.two(), regs[0], regs[1]),
                    _ => Bytecode::Callargs3(ic.two(), regs[0], regs[1], regs[2]),
                };
                codes.push(bc);
            }
            _ => emit_range_call(RangeForm::Call, callee, args, func_id, alloc, codes, ic)?,
        },
        CallKind::CallThis => {
            // args[0] = this, args[1..] = actual args
            match args.len() {
                0 => {
                    // No this — shouldn't happen, but handle gracefully
                    materialize_operands(func_id, &[], Some(callee), alloc, codes)?;
                    codes.push(Bytecode::Callarg0(ic.two()));
                }
                n @ (1..=4) => {
                    let regs = materialize_operands(func_id, args, Some(callee), alloc, codes)?;
                    let bc = match n {
                        1 => Bytecode::Callthis0(ic.two(), regs[0]),
                        2 => Bytecode::Callthis1(ic.two(), regs[0], regs[1]),
                        3 => Bytecode::Callthis2(ic.two(), regs[0], regs[1], regs[2]),
                        _ => Bytecode::Callthis3(ic.two(), regs[0], regs[1], regs[2], regs[3]),
                    };
                    codes.push(bc);
                }
                _ => emit_range_call(RangeForm::CallThis, callee, args, func_id, alloc, codes, ic)?,
            }
        }
        CallKind::SuperCall => {
            emit_range_call(
                RangeForm::SuperCallThis,
                callee,
                args,
                func_id,
                alloc,
                codes,
                ic,
            )?;
        }
        CallKind::SuperCallArrow => {
            emit_range_call(
                RangeForm::SuperCallArrow,
                callee,
                args,
                func_id,
                alloc,
                codes,
                ic,
            )?;
        }
        CallKind::SuperCallSpread => {
            let regs = materialize_operands(
                func_id,
                &args[..1.min(args.len())],
                Some(callee),
                alloc,
                codes,
            )?;
            let arg_r = if args.is_empty() { Reg(0) } else { regs[0] };
            codes.push(Bytecode::Supercallspread(ic.two(), arg_r));
        }
        CallKind::Apply => {
            if args.len() >= 2 {
                let regs = materialize_operands(func_id, &args[..2], Some(callee), alloc, codes)?;
                codes.push(Bytecode::Apply(ic.two(), regs[0], regs[1]));
            } else if args.len() == 1 {
                let regs = materialize_operands(func_id, &args[..1], Some(callee), alloc, codes)?;
                codes.push(Bytecode::Newobjapply(ic.two(), regs[0]));
            } else {
                materialize_operands(func_id, &[], Some(callee), alloc, codes)?;
                codes.push(Bytecode::Callarg0(ic.two()));
            }
        }
        CallKind::Construct => {
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
    SuperCallArrow,
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
fn emit_range_call(
    form: RangeForm,
    callee: Value,
    args: &[Value],
    func_id: FuncId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
    ic: &mut IcAllocator,
) -> Result<(), LowerError> {
    let start = fill_call_window(func_id, args, alloc, codes)?;

    ensure_acc(func_id, callee, alloc, codes)?;

    let argc = args.len();
    let argc_imm = Imm(argc as i64);
    let bc = match (form, argc <= 255) {
        (RangeForm::Call, true) => Bytecode::Callrange(ic.two(), argc_imm, start),
        (RangeForm::Call, false) => Bytecode::WideCallrange(argc_imm, start),
        (RangeForm::CallThis, true) => Bytecode::Callthisrange(ic.two(), argc_imm, start),
        (RangeForm::CallThis, false) => Bytecode::WideCallthisrange(argc_imm, start),
        (RangeForm::SuperCallThis, true) => Bytecode::Supercallthisrange(ic.two(), argc_imm, start),
        (RangeForm::SuperCallThis, false) => Bytecode::WideSupercallthisrange(argc_imm, start),
        (RangeForm::SuperCallArrow, true) => {
            Bytecode::Supercallarrowrange(ic.two(), argc_imm, start)
        }
        (RangeForm::SuperCallArrow, false) => Bytecode::WideSupercallarrowrange(argc_imm, start),
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
    callee: Value,
    args: &[Value],
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
/// start operand), a window end past the register space
/// (`RegisterOverflow`), and more than one Acc-colored value in the fill
/// (`MultipleAccOperands`; the interference invariant guarantees at most
/// one).
fn fill_call_window(
    func_id: FuncId,
    values: &[Value],
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
    // colored slot are always encodable. The — at most one, by the
    // interference invariant — Acc-colored value spills into scratch
    // BEFORE any later acc load in the caller's sequence
    // (spill-before-load order).
    let mut acc_arg: Option<Value> = None;
    for (j, &val) in values.iter().enumerate() {
        let dst = Reg(base + j as u16);
        match slot_of(func_id, val, alloc)? {
            RegSlot::Reg(r) => codes.push(Bytecode::Mov(dst, Reg(r))),
            RegSlot::Acc => {
                if let Some(prev) = acc_arg {
                    return Err(LowerError::MultipleAccOperands {
                        func: func_id,
                        a: prev,
                        b: val,
                    });
                }
                acc_arg = Some(val);
                let scratch = spill_scratch(func_id, alloc, 0)?;
                codes.push(Bytecode::Sta(scratch));
                codes.push(Bytecode::Mov(dst, scratch));
            }
        }
    }
    Ok(Reg(base))
}

/// Try to fuse a compare + branch into a single bytecode.
///
/// Pattern: `CondBranch(cond: IsTrue(BinaryOp { op: Eq|StrictEq|..., left, right }), true_dest)`
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
/// 2. Both `left` and `right` are Reg-colored. At the branch the physical
///    acc holds `cond`, not `left`: `ensure_acc(left)` on an Acc-colored
///    `left` would no-op with the wrong value, and `val_reg(right)` on an
///    Acc-colored `right` would spill `cond`. (A hand-crafted allocation
///    can also color both operands Acc — they are operands of the
///    comparison, not of this branch, so the single-acc-per-instruction
///    interference invariant does not apply at this materialization
///    point.)
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
    cond: Value,
    true_dest: Block,
    branch_inst: Inst,
    block_insts: &[Inst],
    func_id: FuncId,
    module: &Module,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<Option<Bytecode>, LowerError> {
    let cond_inst = match module.value(cond).def {
        crate::module::ValueDef::Inst(i) => i,
        _ => return Ok(None),
    };

    // Unwrap the IsTrue wrapper: the comparison is the instruction whose
    // result feeds the branch, directly or through the wrapper.
    let (cmp_inst, wrapper) = match &module.inst(cond_inst).data {
        InstData::IsTrue { operand } => match module.value(*operand).def {
            crate::module::ValueDef::Inst(i) => (i, Some(cond_inst)),
            _ => return Ok(None),
        },
        // If cond is directly a comparison (without IsTrue wrapper), also fuse.
        InstData::BinaryOp { .. } => (cond_inst, None),
        _ => return Ok(None),
    };
    let InstData::BinaryOp { op, left, right } = &module.inst(cmp_inst).data else {
        return Ok(None);
    };

    // Precondition 1: same-block adjacency — the block's instruction tail
    // must be exactly [comparison, (IsTrue,) branch].
    let tail: &[Inst] = match wrapper {
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
    for result in [module.inst(cmp_inst).result, module.inst(cond_inst).result]
        .into_iter()
        .flatten()
    {
        if let Some(RegSlot::Reg(r)) = alloc.allocation.get(&result).copied() {
            if r == left_r || r == right_r {
                return Ok(None);
            }
        }
    }

    fuse_binop_branch(*op, *left, *right, true_dest, func_id, alloc, codes)
}

/// Emit a fused compare-branch for a BinOp comparison.
///
/// The comparison's operands follow the same spill-before-load ordering as
/// any two-operand instruction: spill the register operand first, then load
/// the acc operand. Soundness preconditions (adjacency, Reg-colored
/// operands, no result-slot sharing) are enforced by the caller,
/// `try_fuse_cmp_branch`.
fn fuse_binop_branch(
    op: BinOp,
    left: Value,
    right: Value,
    true_dest: Block,
    func_id: FuncId,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<Option<Bytecode>, LowerError> {
    // Only the Eq family has fused branch bytecodes in the ABC ISA; for
    // Less/Greater/etc there is nothing to fuse.
    if !matches!(
        op,
        BinOp::Eq | BinOp::NotEq | BinOp::StrictEq | BinOp::StrictNotEq
    ) {
        return Ok(None);
    }
    let label = Label(true_dest.0);
    let regs = materialize_operands(func_id, &[right], Some(left), alloc, codes)?;
    let r = regs[0];
    Ok(Some(match op {
        BinOp::Eq => Bytecode::Jeq(r, label),
        BinOp::NotEq => Bytecode::Jne(r, label),
        BinOp::StrictEq => Bytecode::Jstricteq(r, label),
        // Only StrictNotEq remains (guarded above).
        _ => Bytecode::Jnstricteq(r, label),
    }))
}
