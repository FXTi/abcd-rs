//! Lifting: bytecode → IR.
//!
//! Entry points:
//! - [`lift_file`]: lift an entire ABC file into a [`Module`]
//! - [`lift_method`]: lift a single method into an existing [`Module`]

pub mod cfg;
pub mod resolve;
pub mod ssa;
pub mod translate;

use abcd_file::{Class, File, Method};

use crate::entity::{Block, ClassId, FuncId, Inst, StringId, Value};
use crate::inst::InstData;
use crate::module::{
    BasicBlockData, CatchHandler, ClassData, FieldData, FuncDebugInfo, FunctionData, InstNode,
    IrAnnotation, IrAnnotations, Module, TryRegion, ValueData, ValueDef,
};
use crate::types::IrType;

use self::cfg::build_cfg;
use self::resolve::resolve_entity;
use self::ssa::{RegOrAcc, SsaBuilder};
use self::translate::translate_bytecode;

use std::collections::HashMap;

/// Map a file-level StringId to an IR-level StringId.
fn map_str(file: &File, module: &mut Module, id: abcd_file::StringId) -> StringId {
    let s = file.strings.resolve(id).expect("dangling file StringId");
    module.strings.intern(s)
}

/// Errors that can occur during lifting.
#[derive(Debug, thiserror::Error)]
pub enum LiftError {
    #[error("unresolved entity id {0}")]
    UnresolvedEntity(u32),
    #[error("method has no body")]
    NoBody,
    #[error("empty bytecode")]
    EmptyBytecode,
}

/// Lift an entire ABC file into a [`Module`].
pub fn lift_file(file: &File) -> Result<Module, LiftError> {
    let mut module = Module::new(file.version, file.file_type);
    module.literal_arrays = file.literal_arrays.clone();

    // Lift classes and their methods.
    for class in file.classes.values() {
        let class_id = lift_class(file, class, &mut module)?;
        let _ = class_id; // stored in module.classes
    }

    Ok(module)
}

/// Lift a single class into the module, including all its methods.
fn lift_class(file: &File, class: &Class, module: &mut Module) -> Result<ClassId, LiftError> {
    let descriptor = map_str(file, module, class.descriptor);
    let name = map_str(file, module, class.name);
    let source_file = class.source_file.map(|s| map_str(file, module, s));
    let super_class = class.super_class.map(|s| map_str(file, module, s));
    let interfaces: Vec<StringId> = class
        .interfaces
        .iter()
        .map(|&s| map_str(file, module, s))
        .collect();

    let fields: Vec<FieldData> = class
        .fields
        .iter()
        .map(|f| lift_field(file, f, module))
        .collect();

    let annotations = lift_annotations(file, &class.annotations, module);

    // Lift methods.
    let mut method_ids = Vec::new();
    for method in &class.methods {
        let func_id = lift_method(file, method, module)?;
        method_ids.push(func_id);
    }

    let class_id = ClassId::from_index(module.classes.len());
    module.classes.push(ClassData {
        descriptor,
        name,
        access_flags: class.access_flags,
        source_lang: class.source_lang,
        source_file,
        is_external: class.is_external,
        super_class,
        interfaces,
        fields,
        methods: method_ids,
        annotations,
    });
    Ok(class_id)
}

fn lift_field(file: &File, field: &abcd_file::Field, module: &mut Module) -> FieldData {
    let name = map_str(file, module, field.name);
    let field_type = IrType::Static(field.field_type);
    let annotations = lift_annotations(file, &field.annotations, module);
    FieldData {
        name,
        field_type,
        access_flags: field.access_flags,
        is_external: field.is_external,
        initial_value: field.initial_value.clone(),
        annotations,
    }
}

fn lift_annotations(
    file: &File,
    ann: &abcd_file::Annotations,
    module: &mut Module,
) -> IrAnnotations {
    let mut convert = |list: &[abcd_file::Annotation]| -> Vec<IrAnnotation> {
        list.iter()
            .map(|a| {
                let class_descriptor = map_str(file, module, a.class_descriptor);
                let elements = a
                    .elements
                    .iter()
                    .map(|e| {
                        let name = map_str(file, module, e.name);
                        (name, e.value.clone())
                    })
                    .collect();
                IrAnnotation {
                    class_descriptor,
                    elements,
                }
            })
            .collect()
    };
    IrAnnotations {
        compile_time: convert(&ann.compile_time),
        runtime: convert(&ann.runtime),
        compile_time_type: convert(&ann.compile_time_type),
        runtime_type: convert(&ann.runtime_type),
    }
}

fn lift_debug_info(
    file: &File,
    debug: &abcd_file::MethodDebugInfo,
    module: &mut Module,
) -> FuncDebugInfo {
    FuncDebugInfo {
        source_file: debug.source_file.map(|s| map_str(file, module, s)),
        source_code: debug.source_code.map(|s| map_str(file, module, s)),
        line_table: debug.line_table.clone(),
        column_table: debug.column_table.clone(),
        local_vars: debug.local_vars.clone(),
        params: debug.params.clone(),
    }
}

/// Lift a single method into the module.
pub fn lift_method(file: &File, method: &Method, module: &mut Module) -> Result<FuncId, LiftError> {
    let body = method.body.as_ref().ok_or(LiftError::NoBody)?;
    if body.bytecodes.is_empty() {
        return Err(LiftError::EmptyBytecode);
    }

    let raw_cfg = build_cfg(body).ok_or(LiftError::EmptyBytecode)?;

    // Create the function entry.
    let entry_block = Block::from_index(module.blocks.len());
    module.blocks.push(BasicBlockData::new());

    let func_id = FuncId::from_index(module.functions.len());
    let annotations = lift_annotations(file, &method.annotations, module);
    let debug = method
        .debug
        .as_ref()
        .map(|d| lift_debug_info(file, d, module));
    let name = map_str(file, module, method.name);

    module.functions.push(FunctionData {
        name,
        kind: method.function_kind,
        access_flags: method.access_flags,
        source_lang: method.source_lang,
        is_external: method.is_external,
        param_count: method.arg_types.len() as u16,
        return_type: None, // TODO: convert abcd_file::Type → IrType
        param_types: Vec::new(),
        entry_block,
        blocks: vec![entry_block],
        annotations,
        debug,
        try_regions: Vec::new(), // populated below after block_map is built
    });

    // Create IR blocks corresponding to raw CFG blocks.
    // raw_block_index → IR Block
    let mut block_map: HashMap<usize, Block> = HashMap::new();
    block_map.insert(0, entry_block); // first raw block = entry

    for bi in 1..raw_cfg.blocks.len() {
        let bb = Block::from_index(module.blocks.len());
        module.blocks.push(BasicBlockData::new());
        module.func_mut(func_id).blocks.push(bb);
        block_map.insert(bi, bb);
    }

    // Set predecessor edges.
    for (bi, raw_block) in raw_cfg.blocks.iter().enumerate() {
        let ir_block = block_map[&bi];
        for &succ_bi in &raw_block.succs {
            let succ_bb = block_map[&succ_bi];
            if !module.block(succ_bb).preds.contains(&ir_block) {
                module.block_mut(succ_bb).preds.push(ir_block);
            }
        }
        for &catch_bi in &raw_block.catch_succs {
            let catch_bb = block_map[&catch_bi];
            if !module.block(catch_bb).preds.contains(&ir_block) {
                module.block_mut(catch_bb).preds.push(ir_block);
            }
        }
    }

    // Build try_regions from the original try_blocks.
    let try_regions = build_try_regions(body, &raw_cfg, &block_map);
    module.func_mut(func_id).try_regions = try_regions;

    // SSA construction.
    let mut ssa = SsaBuilder::new();

    // Seal blocks that have all predecessors known (in RPO, all blocks are
    // sealable after we've set up edges — we process in order).
    // For simplicity, seal entry block immediately (no preds).
    ssa.seal_block(entry_block, module);

    // Translate bytecodes block by block.
    let bytecodes = &body.bytecodes;
    for (bi, raw_block) in raw_cfg.blocks.iter().enumerate() {
        let ir_block = block_map[&bi];

        for idx in raw_block.start..raw_block.end {
            let bc = &bytecodes[idx];
            translate_bytecode(
                bc, idx, ir_block, file, module, &mut ssa, &block_map, &raw_cfg,
            )?;
        }

        // Seal successor blocks if all their predecessors have been processed.
        // (Simple heuristic: seal after processing each block.)
        for &succ_bi in raw_block.succs.iter().chain(raw_block.catch_succs.iter()) {
            let succ_bb = block_map[&succ_bi];
            if !ssa.is_sealed(succ_bb) {
                // Check if all predecessors of succ_bb have been processed.
                let all_preds_done = module.block(succ_bb).preds.iter().all(|pred| {
                    // A predecessor is "done" if its raw block index <= bi.
                    block_map.iter().any(|(&rbi, &bb)| bb == *pred && rbi <= bi)
                });
                if all_preds_done {
                    ssa.seal_block(succ_bb, module);
                }
            }
        }
    }

    // Seal any remaining unsealed blocks.
    for bb in block_map.values() {
        if !ssa.is_sealed(*bb) {
            ssa.seal_block(*bb, module);
        }
    }

    Ok(func_id)
}

/// Build TryRegion entries from the original bytecode try_blocks.
///
/// For each try_block in the method body, find which IR blocks overlap the
/// try region and which IR blocks are catch handlers.
fn build_try_regions(
    body: &abcd_file::MethodBody,
    raw_cfg: &cfg::RawCfg,
    block_map: &HashMap<usize, Block>,
) -> Vec<TryRegion> {
    let mut regions = Vec::new();

    for try_block in &body.try_blocks {
        let try_start = try_block.start as usize;
        let try_end = (try_block.start + try_block.len) as usize;

        // Find all IR blocks that overlap the try region.
        let mut try_blocks = Vec::new();
        for (bi, raw_block) in raw_cfg.blocks.iter().enumerate() {
            // Block overlaps try region if [start..end) ∩ [try_start..try_end) ≠ ∅
            if raw_block.start < try_end && raw_block.end > try_start {
                if let Some(&ir_block) = block_map.get(&bi) {
                    try_blocks.push(ir_block);
                }
            }
        }

        // Map catch handlers to IR blocks.
        let catches = try_block
            .catches
            .iter()
            .filter_map(|c| {
                let handler_idx = c.handler as usize;
                let handler_bi = raw_cfg.leader_to_block.get(&handler_idx)?;
                let handler_block = block_map.get(handler_bi)?;
                Some(CatchHandler {
                    type_idx: c.type_idx,
                    handler_block: *handler_block,
                })
            })
            .collect();

        regions.push(TryRegion {
            try_blocks,
            catches,
        });
    }

    regions
}

// ─── Helpers ─────────────────────────────────────────────────────────────────

/// Emit an IR instruction in `block`, returning `(Inst, Option<Value>)`.
fn emit(
    module: &mut Module,
    block: Block,
    data: InstData,
    loc: Option<u32>,
) -> (Inst, Option<Value>) {
    let has_result = data.has_result();
    let is_phi = data.is_phi();
    let inst_id = Inst::from_index(module.insts.len());
    let result = if has_result {
        let val = Value::from_index(module.values.len());
        module.values.push(ValueData {
            def: ValueDef::Inst(inst_id),
            ty: IrType::default(),
        });
        Some(val)
    } else {
        None
    };
    module.insts.push(InstNode {
        data,
        result,
        result_type: IrType::default(),
        block,
        loc,
    });
    let bb = module.block_mut(block);
    if is_phi {
        bb.phis.push(inst_id);
    } else {
        bb.insts.push(inst_id);
    }
    (inst_id, result)
}

/// Emit and return the result value (panics if no result).
fn emit_val(module: &mut Module, block: Block, data: InstData, loc: Option<u32>) -> Value {
    emit(module, block, data, loc)
        .1
        .expect("instruction has no result")
}

/// Emit a void instruction (no result).
fn emit_void(module: &mut Module, block: Block, data: InstData, loc: Option<u32>) {
    emit(module, block, data, loc);
}

/// Read the accumulator SSA value.
fn read_acc(ssa: &mut SsaBuilder, block: Block, module: &mut Module) -> Value {
    ssa.read_variable(RegOrAcc::Acc, block, module)
}

/// Write the accumulator SSA value.
fn write_acc(ssa: &mut SsaBuilder, block: Block, val: Value) {
    ssa.write_variable(RegOrAcc::Acc, block, val);
}

/// Read a register SSA value.
fn read_reg(ssa: &mut SsaBuilder, reg: abcd_isa::Reg, block: Block, module: &mut Module) -> Value {
    ssa.read_variable(RegOrAcc::Reg(reg.0), block, module)
}

/// Write a register SSA value.
fn write_reg(ssa: &mut SsaBuilder, reg: abcd_isa::Reg, block: Block, val: Value) {
    ssa.write_variable(RegOrAcc::Reg(reg.0), block, val);
}

/// Resolve an EntityId to StringId, or return LiftError.
fn resolve(
    file: &File,
    module: &mut Module,
    id: abcd_isa::EntityId,
) -> Result<StringId, LiftError> {
    resolve_entity(file, module, id).ok_or(LiftError::UnresolvedEntity(id.0))
}

/// Look up the IR Block for a jump target label.
fn label_block(
    label: abcd_isa::Label,
    raw_cfg: &cfg::RawCfg,
    block_map: &HashMap<usize, Block>,
) -> Block {
    let target_idx = label.0 as usize;
    let raw_bi = raw_cfg.leader_to_block[&target_idx];
    block_map[&raw_bi]
}
