//! IRBuilder: stateful API for constructing IR programmatically.

use abcd_file::{AccessFlags, FunctionKind, SourceLang};

use crate::entity::{Block, FuncId, Inst, StringId, Value};
use crate::inst::InstData;
use crate::module::{
    BasicBlockData, FunctionData, InstNode, IrAnnotations, Module, ValueData, ValueDef,
};
use crate::types::IrType;

/// Stateful builder for constructing IR within a [`Module`].
pub struct IRBuilder<'m> {
    pub module: &'m mut Module,
    current_func: FuncId,
    current_block: Block,
}

impl<'m> IRBuilder<'m> {
    pub fn new(module: &'m mut Module, func: FuncId) -> Self {
        let entry = module.func(func).entry_block;
        Self {
            module,
            current_func: func,
            current_block: entry,
        }
    }

    // ── Function creation ────────────────────────────────────────────

    /// Create a new function in the module and return its id.
    pub fn create_function(
        module: &mut Module,
        name: &str,
        kind: FunctionKind,
        param_count: u16,
    ) -> FuncId {
        let entry = Block::from_index(module.blocks.len());
        module.blocks.push(BasicBlockData::new());

        let name_id = module.strings.intern(name);
        let func_id = FuncId::from_index(module.functions.len());
        module.functions.push(FunctionData {
            name: name_id,
            kind,
            access_flags: AccessFlags::empty(),
            source_lang: SourceLang::EcmaScript,
            is_external: false,
            param_count,
            return_type: None,
            param_types: Vec::new(),
            entry_block: entry,
            blocks: vec![entry],
            annotations: IrAnnotations::default(),
            debug: None,
            try_regions: Vec::new(),
        });
        func_id
    }

    // ── Block management ─────────────────────────────────────────────

    /// Create a new basic block in the current function.
    pub fn create_block(&mut self) -> Block {
        let id = Block::from_index(self.module.blocks.len());
        self.module.blocks.push(BasicBlockData::new());
        self.module.func_mut(self.current_func).blocks.push(id);
        id
    }

    /// Set the insertion point to the end of the given block.
    pub fn set_insert_block(&mut self, block: Block) {
        self.current_block = block;
    }

    pub fn current_block(&self) -> Block {
        self.current_block
    }

    pub fn current_func(&self) -> FuncId {
        self.current_func
    }

    /// Add `pred` as a predecessor of `block`.
    pub fn add_predecessor(&mut self, block: Block, pred: Block) {
        self.module.block_mut(block).preds.push(pred);
    }

    // ── Value creation ───────────────────────────────────────────────

    fn alloc_value(&mut self, def: ValueDef, ty: IrType) -> Value {
        let id = Value::from_index(self.module.values.len());
        self.module.values.push(ValueData { def, ty });
        id
    }

    /// Create a function parameter value.
    pub fn create_func_param(&mut self, index: u16, ty: IrType) -> Value {
        self.alloc_value(ValueDef::FuncParam(index), ty)
    }

    // ── Instruction emission ─────────────────────────────────────────

    /// Emit an instruction at the current insertion point.
    /// Returns `(Inst, Option<Value>)` — the value is `Some` if the
    /// instruction produces a result.
    pub fn emit(&mut self, data: InstData, result_type: IrType) -> (Inst, Option<Value>) {
        let has_result = data.has_result();
        let is_phi = data.is_phi();

        let inst_id = Inst::from_index(self.module.insts.len());
        let result = if has_result {
            let val = self.alloc_value(ValueDef::Inst(inst_id), result_type.clone());
            Some(val)
        } else {
            None
        };

        self.module.insts.push(InstNode {
            data,
            result,
            result_type,
            block: self.current_block,
            loc: None,
        });

        let bb = self.module.block_mut(self.current_block);
        if is_phi {
            bb.phis.push(inst_id);
        } else {
            bb.insts.push(inst_id);
        }

        (inst_id, result)
    }

    /// Emit an instruction and return its result value.
    /// Panics if the instruction does not produce a result.
    pub fn emit_val(&mut self, data: InstData, result_type: IrType) -> Value {
        let (_, val) = self.emit(data, result_type);
        val.expect("instruction does not produce a value")
    }

    /// Emit an instruction that does not produce a value (stores, terminators).
    pub fn emit_void(&mut self, data: InstData) {
        self.emit(data, IrType::default());
    }

    // ── String interning shortcut ────────────────────────────────────

    pub fn intern(&mut self, s: &str) -> StringId {
        self.module.strings.intern(s)
    }
}
