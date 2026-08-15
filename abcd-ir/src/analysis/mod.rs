//! Analysis infrastructure: CFG traversal, operand queries, and value replacement.

pub mod domtree;
pub mod usedef;

use std::collections::HashSet;

use crate::entity::{Block, FuncId, Inst, Value};
use crate::inst::{InstData, PropKind};
use crate::module::Module;

// ─── CFG traversal ───────────────────────────────────────────────────────────

/// Compute reverse post-order of blocks reachable from the entry.
/// Unreachable blocks (e.g. catch handlers) are appended at the end.
pub fn compute_rpo(module: &Module, func_id: FuncId) -> Vec<Block> {
    let func = module.func(func_id);
    let entry = func.entry_block;
    let mut visited = HashSet::new();
    let mut post_order = Vec::new();

    fn dfs(
        block: Block,
        module: &Module,
        visited: &mut HashSet<Block>,
        post_order: &mut Vec<Block>,
    ) {
        if !visited.insert(block) {
            return;
        }
        for succ in block_succs(module, block) {
            dfs(succ, module, visited, post_order);
        }
        post_order.push(block);
    }

    dfs(entry, module, &mut visited, &mut post_order);

    // Include unreachable blocks.
    for &bb in &func.blocks {
        if visited.insert(bb) {
            post_order.push(bb);
        }
    }

    post_order.reverse();
    post_order
}

/// Extract successor blocks from a block's terminator.
pub fn block_succs(module: &Module, block: Block) -> Vec<Block> {
    let bb = module.block(block);
    match bb.insts.last() {
        Some(&last) => inst_succs(&module.inst(last).data),
        None => vec![],
    }
}

/// Extract successor blocks from an instruction (terminators only).
pub fn inst_succs(data: &InstData) -> Vec<Block> {
    match data {
        InstData::Branch { dest } => vec![*dest],
        InstData::CondBranch {
            true_dest,
            false_dest,
            ..
        } => vec![*true_dest, *false_dest],
        _ => vec![],
    }
}

// ─── Operand queries ─────────────────────────────────────────────────────────

/// Extract all Value operands used by an instruction.
///
/// This is the single canonical implementation — both verification and
/// register allocation should call this instead of maintaining duplicates.
pub fn inst_operands(data: &InstData) -> Vec<Value> {
    use InstData::*;
    match data {
        LiteralUndefined
        | LiteralNull
        | LiteralBool(_)
        | LiteralNumber(_)
        | LiteralString(_)
        | LiteralNaN
        | LiteralInfinity
        | LiteralHole
        | CreateEmptyObject
        | CreateEmptyArray
        | CreateObjectWithBuffer { .. }
        | CreateArrayWithBuffer { .. }
        | CreateRegExp { .. }
        | LoadGlobalVar { .. }
        | TryLoadGlobalByName { .. }
        | LoadLexVar { .. }
        | LoadLocalModuleVar { .. }
        | LoadExternalModuleVar { .. }
        | GetModuleNamespace { .. }
        | NewLexEnv { .. }
        | NewLexEnvWithName { .. }
        | PopLexEnv
        | DefineFunc { .. }
        | LoadThis
        | LoadNewTarget
        | LoadGlobalObject
        | LoadFunction
        | GetUnmappedArgs
        | CopyRestArgs { .. }
        | ResumeGenerator
        | AsyncFunctionEnter
        | ThrowNotExists
        | ThrowPatternNonCoercible
        | ThrowDeleteSuperProperty
        | ThrowConstAssignment { .. }
        | Branch { .. }
        | Unreachable
        | Debugger => vec![],

        BinaryOp { left, right, .. } => vec![*left, *right],
        UnaryOp { operand, .. } | IsTrue { operand } | IsFalse { operand } => vec![*operand],

        CreateObjectWithExcludedKeys { obj, keys } => {
            let mut v = vec![*obj];
            v.extend(keys);
            v
        }

        LoadProperty { object, key } => {
            let mut v = vec![*object];
            if let PropKind::ByValue(k) = key {
                v.push(*k);
            }
            v
        }
        StoreProperty { object, key, value } | StoreOwnProperty { object, key, value } => {
            let mut v = vec![*object, *value];
            if let PropKind::ByValue(k) = key {
                v.push(*k);
            }
            v
        }
        DeleteProperty { object, key } => vec![*object, *key],
        LoadSuperProperty { key } => {
            if let PropKind::ByValue(k) = key {
                vec![*k]
            } else {
                vec![]
            }
        }
        StoreSuperProperty { key, value } => {
            let mut v = vec![*value];
            if let PropKind::ByValue(k) = key {
                v.push(*k);
            }
            v
        }

        StoreGlobalVar { value, .. }
        | TryStoreGlobalByName { value, .. }
        | StoreLexVar { value, .. }
        | StoreModuleVar { value, .. }
        | DynamicImport { specifier: value }
        | Throw { value }
        | ThrowIfNotObject { value }
        | ThrowIfSuperNotCorrectCall { value }
        | GetIterator { obj: value }
        | GetAsyncIterator { obj: value }
        | GetPropIterator { obj: value }
        | CloseIterator { iterator: value }
        | CreateGeneratorObj { func: value }
        | SuspendGenerator { value }
        | AsyncFunctionAwaitUncaught { value }
        | AsyncFunctionResolve { value }
        | AsyncFunctionReject { value } => vec![*value],

        ThrowUndefinedIfHole { value, .. } => vec![*value],
        CreateIterResultObj { value, done } => vec![*value, *done],

        DefineMethod { home_object, .. } => vec![*home_object],
        DefineClassWithBuffer { base, .. } => vec![*base],
        DefineGetterSetterByValue {
            obj,
            key,
            getter,
            setter,
        } => {
            vec![*obj, *key, *getter, *setter]
        }

        Call { callee, args, .. } => {
            let mut v = vec![*callee];
            v.extend(args);
            v
        }

        Phi { entries } => entries.iter().map(|(_, v)| *v).collect(),
        CondBranch { cond, .. } => vec![*cond],
        Return { value } => value.iter().copied().collect(),
    }
}

// ─── Value replacement ───────────────────────────────────────────────────────

/// Replace all uses of `old` with `new_val` across every instruction in `func`.
/// Returns the number of replacements made.
pub fn replace_uses_in_func(
    module: &mut Module,
    func_id: FuncId,
    old: Value,
    new_val: Value,
) -> usize {
    let blocks: Vec<Block> = module.func(func_id).blocks.clone();
    let mut count = 0;
    for bb in blocks {
        let block = module.block(bb);
        let all_insts: Vec<Inst> = block
            .phis
            .iter()
            .chain(block.insts.iter())
            .copied()
            .collect();
        for inst_id in all_insts {
            count += replace_uses_in_inst(&mut module.insts[inst_id.index()].data, old, new_val);
        }
    }
    count
}

/// Replace `old` → `new_val` inside a single instruction's operands.
/// Returns the number of replacements.
fn replace_uses_in_inst(data: &mut InstData, old: Value, new_val: Value) -> usize {
    let mut count = 0;
    for v in data.operands_mut() {
        if *v == old {
            *v = new_val;
            count += 1;
        }
    }
    count
}
