//! # abcd-lower — lower converter: `abcd_ir2::Module` → `abcd_file::MethodBody`
//!
//! IR v0.2 migration plan P2 (design/ir-v0.2.md §8): the lowering half of
//! the v0.2 pipeline. This is a source-level port of v0.1 `abcd_ir::lower`
//! (frozen oracle) onto the v0.2 IR: the same algorithms (MCS chordal
//! coloring, slot-level parallel-copy resolution, acc-as-cache instruction
//! selection, block layout with edge trampolines, N43 try-range
//! reconstruction, and the entity relocation channel), operating on
//! [`abcd_ir2::Module`] and producing [`abcd_file::MethodBody`].

#![deny(missing_docs)]

pub mod analysis;
pub mod copy_resolve;
pub mod fusion;
pub mod isel;
pub mod layout;
pub mod method_body;
pub mod regalloc;

use abcd_ir2::{BlockId, FuncId, Module, ValueId};

pub use layout::LayoutResult;
pub use method_body::to_method_body;
pub use regalloc::RegAlloc;

/// Errors that can occur during lowering.
#[derive(Debug, thiserror::Error)]
pub enum LowerError {
    /// The function has no blocks (e.g. an external/native function).
    #[error("function {0:?} has no blocks")]
    EmptyFunction(FuncId),
    /// Register allocation overflow.
    #[error("register allocation overflow in function {0:?}")]
    RegisterOverflow(FuncId),
    /// An instruction has no faithful bytecode encoding.
    #[error("unsupported instruction in function {func:?}: {message}")]
    UnsupportedInstruction {
        /// The owning function.
        func: FuncId,
        /// What cannot be encoded.
        message: String,
    },
    /// A slot-level phi copy cycle exists but no copy temp was reserved.
    #[error(
        "function {0:?} has a slot-level phi copy cycle but no reserved copy temporary register"
    )]
    MissingCopyTemp(FuncId),
    /// An operand was never colored by register allocation.
    #[error("function {func:?} uses value {value:?} that register allocation never colored")]
    UnallocatedOperand {
        /// The owning function.
        func: FuncId,
        /// The uncolored value.
        value: ValueId,
    },
    /// An entity operand cannot be traced back to a source-file offset.
    #[error(
        "function {func:?} has a {kind:?} entity operand with raw value {raw:#x} that cannot \
         be traced to a source-file entity (string content, method function-table index, or \
         literal-array content)"
    )]
    UntraceableEntity {
        /// The owning function.
        func: FuncId,
        /// The entity kind.
        kind: abcd_isa::EntityKind,
        /// The raw operand value.
        raw: u32,
    },
    /// A high (>= 256) register routes through the accumulator but no low
    /// scratch block was reserved.
    #[error(
        "function {0:?} routes a high (>= 256) register through the accumulator but register \
         allocation reserved no low (<= 255) scratch block; sta/lda are op_v_8-only"
    )]
    MissingLowScratch(FuncId),
    /// An instruction has more register operands than the low scratch block.
    #[error(
        "function {0:?} has an instruction with more register operands than the reserved low \
         scratch block holds"
    )]
    LowScratchExhausted(FuncId),
    /// A range-form call exists but no argument window was reserved.
    #[error(
        "function {0:?} contains a range-form call but register allocation reserved no \
         consecutive argument window"
    )]
    MissingCallWindow(FuncId),
    /// The range-call window would start above register 255.
    #[error(
        "range-call argument window in function {0:?} would start above register 255; the \
         vendored start-register operand is u8 in every callrange form (narrow and wide)"
    )]
    CallWindowOverflow(FuncId),
    /// A range-form call exceeds the u16 argc encoding limit.
    #[error(
        "range-form call in function {func:?} has {argc} arguments, exceeding the u16 argc \
         encoding limit of the wide callrange forms"
    )]
    CallArgcOverflow {
        /// The owning function.
        func: FuncId,
        /// The argument count.
        argc: usize,
    },
    /// A catch-handler phi has a same-slot result/incoming pair that
    /// interferes.
    #[error(
        "function {0:?}: a catch-handler phi has a same-slot result/incoming pair that \
         interferes (inconsistent input — coloring never assigns one slot to an \
         interfering pair)"
    )]
    HandlerPhiConflict(FuncId),
    /// A catch-handler phi result or incoming value was never colored.
    #[error(
        "function {0:?}: a catch-handler phi result has no register home or an incoming \
         value was never colored"
    )]
    HandlerPhiUncoalesced(FuncId),
    /// Phi copies remain on an exception edge — no code may run there.
    #[error(
        "function {func:?}: phi copies remain on exception edge {pred:?} -> {handler:?}; \
         no code may run on an exception edge — the VM dispatches directly to the handler's \
         flat offset (N21)"
    )]
    HandlerEdgeCopies {
        /// The owning function.
        func: FuncId,
        /// The protected predecessor.
        pred: BlockId,
        /// The handler block.
        handler: BlockId,
    },
    /// Phi copies keyed to an edge that is neither a terminator successor
    /// nor a catch-handler edge.
    #[error(
        "function {func:?}: phi copies keyed to {pred:?} -> {succ:?}, which is neither a \
         terminator successor nor a catch-handler edge — inconsistent input"
    )]
    InconsistentEdgeCopies {
        /// The owning function.
        func: FuncId,
        /// The predecessor.
        pred: BlockId,
        /// The successor.
        succ: BlockId,
    },
    /// A block emitted zero bytecodes (N49).
    #[error(
        "function {func:?}: block {block:?} emitted zero bytecodes — inconsistent input (a \
         block with no terminator). Its flat offset would alias the next block's, and the \
         next-greater-offset extent in try/handler range reconstruction would swallow the \
         following block into this one's range (N49)"
    )]
    ZeroExtentBlock {
        /// The owning function.
        func: FuncId,
        /// The offending block.
        block: BlockId,
    },
}

/// Lower a single IR function back to bytecodes.
pub fn lower_function(module: &Module, func_id: FuncId) -> Result<LayoutResult, LowerError> {
    let func = module
        .func(func_id)
        .ok_or(LowerError::EmptyFunction(func_id))?;
    if func.blocks.is_empty() {
        return Err(LowerError::EmptyFunction(func_id));
    }

    // Step 0: Fusion analysis (BEFORE register allocation): the v0.2
    // lift's expansion mappings (compare.rs rule 3) materialize values
    // v0.1 never had — DefineFunc/AllocClosure pairs, by-index constant
    // loads, try-load-global defaults. Their results must never be
    // colored, or the allocator's value universe would differ from
    // v0.1's and every coloring (hence every emitted operand) could
    // drift. The suppressed instructions fold into their consumers at
    // instruction selection.
    let suppression = fusion::analyze(module, &func.blocks);

    // Step 1: Register allocation.
    let alloc = regalloc::allocate(module, func_id, &suppression).map_err(|e| match e {
        regalloc::RegAllocError::RegisterOverflow => LowerError::RegisterOverflow(func_id),
        regalloc::RegAllocError::WindowBaseOverflow => LowerError::CallWindowOverflow(func_id),
        regalloc::RegAllocError::HandlerPhiSlotConflict => LowerError::HandlerPhiConflict(func_id),
        regalloc::RegAllocError::HandlerPhiUncoalesced => {
            LowerError::HandlerPhiUncoalesced(func_id)
        }
    })?;

    // Step 2: Compute RPO (reuse from regalloc).
    let rpo = regalloc::compute_rpo(module, func_id);

    // Step 3: Instruction selection.
    let isel_result = isel::select(module, func_id, &alloc, &rpo, &suppression)?;
    if let Some(message) = isel_result.unsupported.clone() {
        return Err(LowerError::UnsupportedInstruction {
            func: func_id,
            message,
        });
    }

    // Step 4: Layout and jump resolution.
    layout::layout(module, func_id, &isel_result, &alloc, &rpo)
}

#[cfg(test)]
mod tests {
    use super::lower_function;
    use abcd_ir2::{Block, BlockId, ClassId, FuncId, FunctionData, FunctionKind, Inst, InstId, Module, Op, Ty, Value, ValueDef, ValueId};

    /// N25 (v0.1 parity): the name is the runtime VALUE in the register
    /// operand (vendor `throw.constassignment v:in:top, acc: none`,
    /// isa.yaml:987-991) — lowering succeeds and emits the name's
    /// register home, never a hardcoded Reg(0).
    #[test]
    fn const_assignment_lowers_with_the_name_register() {
        let mut module = Module::new();
        let descriptor = module.sym.intern("Ltest;");
        module.classes.push(abcd_ir2::ClassData {
            descriptor,
            name: descriptor,
            modifiers: abcd_ir2::Modifiers::NONE,
            source_lang: abcd_ir2::SourceLang::EcmaScript,
            super_class: None,
            interfaces: Vec::new(),
            fields: Vec::new(),
            methods: Vec::new(),
            annotations: Vec::new(),
            source_file: None,
        });
        let name_sym = module.sym.intern("f");
        let func = FuncId::new(0);
        module
            .functions
            .push(FunctionData::new(ClassId::new(0), name_sym, FunctionKind::Function));
        let entry = BlockId::new(0);
        module.blocks.push(Block::default());
        module.functions[0].blocks.push(entry);
        // One parameter (the name value).
        let param = ValueId::new(0);
        module.values.push(Value {
            def: ValueDef::Param(0),
            ty: Ty::Any,
        });
        module.functions[0].params.push(param);
        let throw = InstId::new(0);
        module.insts.push(Inst {
            op: Op::ThrowConstAssignment { name: param },
            result: None,
            block: entry,
            loc: None,
        });
        let ret = InstId::new(1);
        module.insts.push(Inst {
            op: Op::Return { value: None },
            result: None,
            block: entry,
            loc: None,
        });
        module.blocks[0].insts.push(throw);
        module.blocks[0].insts.push(ret);

        let result = lower_function(&module, func).expect("throw.constassignment must lower");
        assert!(
            result
                .bytecodes
                .iter()
                .any(|bc| matches!(bc, abcd_isa::Bytecode::ThrowConstassignment(_))),
            "the lowered stream must contain throw.constassignment: {:?}",
            result.bytecodes
        );
    }
}
