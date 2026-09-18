//! Instruction selection: IR instructions → ArkCompiler bytecodes.
//!
//! Takes an IR function with register allocation results and produces
//! a sequence of ArkCompiler bytecodes per basic block.

use std::collections::HashMap;

use abcd_isa::{Bytecode, EntityId, Imm, Label, Reg};

use crate::entity::{Block, FuncId, Inst, StringId, Value};
use crate::inst::{BinOp, CallKind, InstData, PropKind, UnOp};
use crate::module::Module;

use super::LowerError;
use super::regalloc::{RegAlloc, RegSlot};

/// Result of instruction selection for one function.
#[derive(Debug)]
pub struct IselResult {
    /// Bytecodes per block (in RPO order).
    pub block_codes: Vec<(Block, Vec<Bytecode>)>,
    /// String pool reverse map: StringId → EntityId for the output file.
    pub string_map: HashMap<StringId, EntityId>,
    /// Trace of every entity operand emitted through the string map, keyed by
    /// the emitted raw operand value. [`EntityTrace::Traced`] means the value
    /// is the source-file offset recorded in `module.string_entities`;
    /// [`EntityTrace::Untraced`] means at least one use of the value fell
    /// back to the identity `EntityId(sid.0)` for an unmapped string (a
    /// hand-built module has no source file). An untraced use poisons the
    /// raw value: identity relocation entries are only meaningful when every
    /// use of the value carries a real source offset.
    pub entity_traces: HashMap<u32, EntityTrace>,
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
/// each emitted value is traceable to a source-file offset.
struct EntityTracer<'a> {
    /// The caller-provided output map (may carry identity fallbacks).
    string_map: &'a HashMap<StringId, EntityId>,
    /// The module's own recorded source mappings (StringId → source offset).
    module_entities: &'a HashMap<StringId, EntityId>,
    traces: HashMap<u32, EntityTrace>,
}

impl EntityTracer<'_> {
    /// Resolve `sid` exactly as the legacy `eid` helper did (string_map value,
    /// identity fallback), recording whether the emitted value is the
    /// module-recorded source offset.
    fn eid(&mut self, sid: StringId) -> EntityId {
        let e = self
            .string_map
            .get(&sid)
            .copied()
            .unwrap_or(EntityId(sid.0));
        let traced = self.module_entities.get(&sid).copied() == Some(e);
        self.traces
            .entry(e.0)
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

    for &bb in rpo {
        let mut codes = Vec::new();
        let block = module.block(bb);

        // Copy-in prologue: arguments arrive in the ABI top slots and are
        // moved into the parameters' vreg homes at the very start of the
        // entry block.
        if bb == entry_block {
            emit_param_copy_in(func_id, module, alloc, &mut codes)?;
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
                func_id,
                module,
                alloc,
                &mut tracer,
                &mut codes,
                &mut ic,
            )?;
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
fn val_reg(
    func_id: FuncId,
    val: Value,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<Reg, LowerError> {
    match slot_of(func_id, val, alloc)? {
        RegSlot::Reg(r) => Ok(Reg(r)),
        RegSlot::Acc => {
            // Value is in acc — spill it to the reserved in-frame register.
            // The register allocator reserves exactly one such slot whenever
            // any value is Acc-colored; at most one operand per instruction
            // is Acc-colored (interference invariant, see
            // `materialize_operands`), so one slot suffices.
            match alloc.spill_slot {
                Some(RegSlot::Reg(r)) => {
                    codes.push(Bytecode::Sta(Reg(r)));
                    Ok(Reg(r))
                }
                _ => Err(LowerError::MissingSpillSlot(func_id)),
            }
        }
    }
}

/// Ensure a value is in the accumulator. If it's in a register, emit lda.
fn ensure_acc(
    func_id: FuncId,
    val: Value,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<(), LowerError> {
    match slot_of(func_id, val, alloc)? {
        RegSlot::Reg(r) => {
            codes.push(Bytecode::Lda(Reg(r)));
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
    for &v in reg_operands {
        regs.push(val_reg(func_id, v, alloc, codes)?);
    }
    if let Some(acc_val) = acc_operand {
        ensure_acc(func_id, acc_val, alloc, codes)?;
    }
    Ok(regs)
}

/// If the result should go to a register (not acc), emit sta.
fn store_result(result_slot: Option<RegSlot>, codes: &mut Vec<Bytecode>) {
    if let Some(RegSlot::Reg(r)) = result_slot {
        codes.push(Bytecode::Sta(Reg(r)));
    }
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
            num_regs: 8,
            copy_temp: None,
            spill_slot,
        }
    }

    #[test]
    fn acc_operand_spills_into_the_reserved_in_frame_slot() {
        let v = Value::from_index(1);
        let alloc = alloc_with(&[(v, RegSlot::Acc)], Some(RegSlot::Reg(7)));
        let mut codes = Vec::new();
        let r = val_reg(F, v, &alloc, &mut codes).expect("spill must succeed");
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
        let r = val_reg(F, v, &alloc, &mut codes).expect("reg operand must resolve");
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
                val_reg(F, v, &alloc, &mut codes),
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
            val_reg(F, dangling, &alloc, &mut codes),
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
#[allow(clippy::too_many_arguments)]
fn select_inst(
    data: &InstData,
    result_slot: Option<RegSlot>,
    _inst: Inst,
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
            store_result(result_slot, codes);
        }
        InstData::LiteralNull => {
            codes.push(Bytecode::Ldnull);
            store_result(result_slot, codes);
        }
        InstData::LiteralBool(true) => {
            codes.push(Bytecode::Ldtrue);
            store_result(result_slot, codes);
        }
        InstData::LiteralBool(false) => {
            codes.push(Bytecode::Ldfalse);
            store_result(result_slot, codes);
        }
        InstData::LiteralNumber(n) => {
            let bits = n.to_bits();
            if *n == (*n as i32) as f64 {
                codes.push(Bytecode::Ldai(Imm(*n as i64)));
            } else {
                codes.push(Bytecode::Fldai(Imm(bits as i64)));
            }
            store_result(result_slot, codes);
        }
        InstData::LiteralString(s) => {
            codes.push(Bytecode::LdaStr(tracer.eid(*s)));
            store_result(result_slot, codes);
        }
        InstData::LiteralNaN => {
            codes.push(Bytecode::Ldnan);
            store_result(result_slot, codes);
        }
        InstData::LiteralInfinity => {
            codes.push(Bytecode::Ldinfinity);
            store_result(result_slot, codes);
        }
        InstData::LiteralHole => {
            codes.push(Bytecode::Ldhole);
            store_result(result_slot, codes);
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
            store_result(result_slot, codes);
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
            store_result(result_slot, codes);
        }
        InstData::IsTrue { operand } => {
            ensure_acc(func_id, *operand, alloc, codes)?;
            codes.push(Bytecode::Istrue);
            store_result(result_slot, codes);
        }
        InstData::IsFalse { operand } => {
            ensure_acc(func_id, *operand, alloc, codes)?;
            codes.push(Bytecode::Isfalse);
            store_result(result_slot, codes);
        }

        // ── Object / Array creation ──────────────────────────────────
        InstData::CreateEmptyObject => {
            codes.push(Bytecode::Createemptyobject);
            store_result(result_slot, codes);
        }
        InstData::CreateEmptyArray => {
            codes.push(Bytecode::Createemptyarray(ic.one()));
            store_result(result_slot, codes);
        }
        InstData::CreateArrayWithBuffer { literal_array } => {
            let la_eid = EntityId(*literal_array);
            codes.push(Bytecode::Createarraywithbuffer(ic.one(), la_eid));
            store_result(result_slot, codes);
        }
        InstData::CreateObjectWithBuffer { literal_array } => {
            let la_eid = EntityId(*literal_array);
            codes.push(Bytecode::Createobjectwithbuffer(ic.one(), la_eid));
            store_result(result_slot, codes);
        }
        InstData::CreateRegExp { pattern, flags } => {
            let p = tracer.eid(*pattern);
            let f_str = module.strings.get(*flags);
            let f_val: i64 = f_str.parse().unwrap_or(0);
            codes.push(Bytecode::Createregexpwithliteral(ic.one(), p, Imm(f_val)));
            store_result(result_slot, codes);
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
            store_result(result_slot, codes);
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
            store_result(result_slot, codes);
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
            store_result(result_slot, codes);
        }
        InstData::LoadSuperProperty { key } => {
            match key {
                PropKind::ByName(name) => {
                    codes.push(Bytecode::Ldsuperbyname(ic.two(), tracer.eid(*name)));
                }
                PropKind::ByValue(k) => {
                    let key_r = val_reg(func_id, *k, alloc, codes)?;
                    codes.push(Bytecode::Ldsuperbyvalue(ic.two(), key_r));
                }
                PropKind::ByIndex(_) => {
                    // No direct bytecode; approximate with ByValue
                }
            }
            store_result(result_slot, codes);
        }
        InstData::StoreSuperProperty { key, value } => match key {
            PropKind::ByName(name) => {
                let val_r = val_reg(func_id, *value, alloc, codes)?;
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
            store_result(result_slot, codes);
        }
        InstData::StoreGlobalVar { name, value } => {
            ensure_acc(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Stglobalvar(ic.one(), tracer.eid(*name)));
        }
        InstData::TryLoadGlobalByName { name } => {
            codes.push(Bytecode::Tryldglobalbyname(ic.one(), tracer.eid(*name)));
            store_result(result_slot, codes);
        }
        InstData::TryStoreGlobalByName { name, value } => {
            ensure_acc(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Trystglobalbyname(ic.one(), tracer.eid(*name)));
        }

        // ── Lexical variables ────────────────────────────────────────
        InstData::LoadLexVar { level, slot } => {
            codes.push(Bytecode::Ldlexvar(Imm(*level as i64), Imm(*slot as i64)));
            store_result(result_slot, codes);
        }
        InstData::StoreLexVar { level, slot, value } => {
            ensure_acc(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Stlexvar(Imm(*level as i64), Imm(*slot as i64)));
        }
        InstData::NewLexEnv { num_vars } => {
            codes.push(Bytecode::Newlexenv(Imm(*num_vars as i64)));
            store_result(result_slot, codes);
        }
        InstData::NewLexEnvWithName {
            num_vars,
            scope_literal_array,
        } => {
            codes.push(Bytecode::Newlexenvwithname(
                Imm(*num_vars as i64),
                EntityId(*scope_literal_array),
            ));
            store_result(result_slot, codes);
        }
        InstData::PopLexEnv => {
            codes.push(Bytecode::Poplexenv);
        }

        // ── Module variables ─────────────────────────────────────────
        InstData::LoadLocalModuleVar { index } => {
            codes.push(Bytecode::Ldlocalmodulevar(Imm(*index as i64)));
            store_result(result_slot, codes);
        }
        InstData::LoadExternalModuleVar { index } => {
            codes.push(Bytecode::Ldexternalmodulevar(Imm(*index as i64)));
            store_result(result_slot, codes);
        }
        InstData::StoreModuleVar { index, value } => {
            ensure_acc(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Stmodulevar(Imm(*index as i64)));
        }
        InstData::GetModuleNamespace { index } => {
            codes.push(Bytecode::Getmodulenamespace(Imm(*index as i64)));
            store_result(result_slot, codes);
        }
        InstData::DynamicImport { specifier } => {
            ensure_acc(func_id, *specifier, alloc, codes)?;
            codes.push(Bytecode::Dynamicimport);
            store_result(result_slot, codes);
        }

        // ── Function / Class definition ──────────────────────────────
        InstData::DefineFunc { method_id, length } => {
            codes.push(Bytecode::Definefunc(
                ic.one(),
                tracer.eid(*method_id),
                Imm(*length as i64),
            ));
            store_result(result_slot, codes);
        }
        InstData::DefineMethod {
            method_id,
            length,
            home_object,
        } => {
            ensure_acc(func_id, *home_object, alloc, codes)?;
            codes.push(Bytecode::Definemethod(
                ic.one(),
                tracer.eid(*method_id),
                Imm(*length as i64),
            ));
            store_result(result_slot, codes);
        }
        InstData::DefineClassWithBuffer {
            method_id,
            literal_array,
            base,
        } => {
            let base_r = val_reg(func_id, *base, alloc, codes)?;
            codes.push(Bytecode::Defineclasswithbuffer(
                ic.one(),
                tracer.eid(*method_id),
                EntityId(*literal_array),
                Imm(0),
                base_r,
            ));
            store_result(result_slot, codes);
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
            store_result(result_slot, codes);
        }

        // ── Calls ────────────────────────────────────────────────────
        InstData::Call { kind, callee, args } => {
            select_call(*kind, *callee, args, func_id, alloc, codes, ic)?;
            store_result(result_slot, codes);
        }

        // ── Special value loaders ────────────────────────────────────
        InstData::LoadThis => {
            codes.push(Bytecode::Ldthis);
            store_result(result_slot, codes);
        }
        InstData::LoadNewTarget => {
            codes.push(Bytecode::Ldnewtarget);
            store_result(result_slot, codes);
        }
        InstData::LoadGlobalObject => {
            codes.push(Bytecode::Ldglobal);
            store_result(result_slot, codes);
        }
        InstData::LoadFunction => {
            codes.push(Bytecode::Ldfunction);
            store_result(result_slot, codes);
        }
        InstData::GetUnmappedArgs => {
            codes.push(Bytecode::Getunmappedargs);
            store_result(result_slot, codes);
        }
        InstData::CopyRestArgs { start_index } => {
            codes.push(Bytecode::Copyrestargs(Imm(*start_index as i64)));
            store_result(result_slot, codes);
        }

        // ── Iterators ────────────────────────────────────────────────
        InstData::GetIterator { obj } => {
            ensure_acc(func_id, *obj, alloc, codes)?;
            codes.push(Bytecode::Getiterator(ic.two()));
            store_result(result_slot, codes);
        }
        InstData::GetAsyncIterator { obj } => {
            ensure_acc(func_id, *obj, alloc, codes)?;
            codes.push(Bytecode::Getasynciterator(ic.two()));
            store_result(result_slot, codes);
        }
        InstData::GetPropIterator { obj } => {
            ensure_acc(func_id, *obj, alloc, codes)?;
            codes.push(Bytecode::Getpropiterator);
            store_result(result_slot, codes);
        }
        InstData::CloseIterator { iterator } => {
            let iter_r = val_reg(func_id, *iterator, alloc, codes)?;
            codes.push(Bytecode::Closeiterator(ic.two(), iter_r));
            store_result(result_slot, codes);
        }

        // ── Generator / Async ────────────────────────────────────────
        InstData::CreateGeneratorObj { func } => {
            let func_r = val_reg(func_id, *func, alloc, codes)?;
            codes.push(Bytecode::Creategeneratorobj(func_r));
            store_result(result_slot, codes);
        }
        InstData::SuspendGenerator { value } => {
            let val_r = val_reg(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Suspendgenerator(val_r));
            store_result(result_slot, codes);
        }
        InstData::ResumeGenerator => {
            codes.push(Bytecode::Resumegenerator);
            store_result(result_slot, codes);
        }
        InstData::AsyncFunctionEnter => {
            codes.push(Bytecode::Asyncfunctionenter);
            store_result(result_slot, codes);
        }
        InstData::AsyncFunctionAwaitUncaught { value } => {
            let val_r = val_reg(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Asyncfunctionawaituncaught(val_r));
            store_result(result_slot, codes);
        }
        InstData::AsyncFunctionResolve { value } => {
            let val_r = val_reg(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Asyncfunctionresolve(val_r));
            store_result(result_slot, codes);
        }
        InstData::AsyncFunctionReject { value } => {
            let val_r = val_reg(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Asyncfunctionreject(val_r));
            store_result(result_slot, codes);
        }
        InstData::CreateIterResultObj { value, done } => {
            let regs = materialize_operands(func_id, &[*value, *done], None, alloc, codes)?;
            codes.push(Bytecode::Createiterresultobj(regs[0], regs[1]));
            store_result(result_slot, codes);
        }

        // ── Exception handling ───────────────────────────────────────
        InstData::Throw { value } => {
            ensure_acc(func_id, *value, alloc, codes)?;
            codes.push(Bytecode::Throw);
        }
        InstData::ThrowIfNotObject { value } => {
            let val_r = val_reg(func_id, *value, alloc, codes)?;
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
            if let Some(fused) =
                try_fuse_cmp_branch(*cond, *true_dest, func_id, module, alloc, codes)?
            {
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
            n => {
                // Range calls pass only the first register; the rest are
                // assumed to occupy consecutive registers (approximate,
                // pre-existing).
                let regs = materialize_operands(func_id, &args[..1], Some(callee), alloc, codes)?;
                codes.push(Bytecode::Callrange(ic.two(), Imm(n as i64), regs[0]));
            }
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
                n => {
                    let regs =
                        materialize_operands(func_id, &args[..1], Some(callee), alloc, codes)?;
                    codes.push(Bytecode::Callthisrange(ic.two(), Imm(n as i64), regs[0]));
                }
            }
        }
        CallKind::SuperCall => {
            let regs = materialize_operands(
                func_id,
                &args[..1.min(args.len())],
                Some(callee),
                alloc,
                codes,
            )?;
            let start = if args.is_empty() { Reg(0) } else { regs[0] };
            codes.push(Bytecode::Supercallthisrange(
                ic.two(),
                Imm(args.len() as i64),
                start,
            ));
        }
        CallKind::SuperCallArrow => {
            let regs = materialize_operands(
                func_id,
                &args[..1.min(args.len())],
                Some(callee),
                alloc,
                codes,
            )?;
            let start = if args.is_empty() { Reg(0) } else { regs[0] };
            codes.push(Bytecode::Supercallarrowrange(
                ic.two(),
                Imm(args.len() as i64),
                start,
            ));
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
    }
    Ok(())
}

/// Try to fuse a compare + branch into a single bytecode.
///
/// Pattern: `CondBranch(cond: IsTrue(BinaryOp { op: Eq|StrictEq|..., left, right }), true_dest)`
/// → `Jeq(right_reg, true_dest)` with left in acc.
///
/// Returns `Ok(Some(fused_bytecode))` if fusion succeeded, `Ok(None)`
/// otherwise.
fn try_fuse_cmp_branch(
    cond: Value,
    true_dest: Block,
    func_id: FuncId,
    module: &Module,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Result<Option<Bytecode>, LowerError> {
    let cond_def = module.value(cond);
    let cond_inst = match cond_def.def {
        crate::module::ValueDef::Inst(i) => i,
        _ => return Ok(None),
    };

    // Check if cond is IsTrue { operand }
    let inner_val = match &module.inst(cond_inst).data {
        InstData::IsTrue { operand } => *operand,
        // If cond is directly a comparison (without IsTrue wrapper), also fuse.
        InstData::BinaryOp { op, left, right } => {
            return fuse_binop_branch(*op, *left, *right, true_dest, func_id, alloc, codes);
        }
        _ => return Ok(None),
    };

    // Check if inner_val is BinaryOp { op: comparison, left, right }
    let inner_def = module.value(inner_val);
    let inner_inst = match inner_def.def {
        crate::module::ValueDef::Inst(i) => i,
        _ => return Ok(None),
    };

    match &module.inst(inner_inst).data {
        InstData::BinaryOp { op, left, right } => {
            fuse_binop_branch(*op, *left, *right, true_dest, func_id, alloc, codes)
        }
        _ => Ok(None),
    }
}

/// Emit a fused compare-branch for a BinOp comparison.
///
/// The comparison's operands follow the same spill-before-load ordering as
/// any two-operand instruction: spill the register operand first, then load
/// the acc operand.
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
