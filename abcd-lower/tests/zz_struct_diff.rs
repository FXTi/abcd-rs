//! TEMPORARY structural diff diagnostic (delete after gate diagnosis).

use std::collections::{HashMap, HashSet};

use abcd_file::File;
use abcd_ir2::{BlockId, FuncId, Module, ValueId};

fn dump(tag: &str, file: &File) {
    eprintln!("== {tag}");
    eprintln!(
        "  version {:?} strings={} literal_arrays={}",
        file.version,
        file.strings.len(),
        file.literal_arrays.len()
    );
    for (i, la) in file.literal_arrays.iter().enumerate() {
        eprintln!("  la[{i}] = {:?}", la.values);
    }
    let mut la_off: Vec<(u32, u32)> =
        file.literal_array_offsets.iter().map(|(&o, &i)| (o, i)).collect();
    la_off.sort();
    eprintln!("  la_offsets: {la_off:?}");
    for (desc, m) in file.all_methods() {
        let body = m.body.as_ref();
        eprintln!(
            "  method {}::{} off={:#x} vregs={} args={} code_len={} try={} ic_entity_offsets={}",
            file.strings.resolve(desc).unwrap_or("?"),
            file.strings.resolve(m.name).unwrap_or("?"),
            m.offset,
            body.map_or(0, |b| b.num_vregs),
            body.map_or(0, |b| b.num_args),
            body.map_or(0, |b| b.bytecodes.len()),
            body.map_or(0, |b| b.try_blocks.len()),
            body.map_or(0, |b| b.entity_offsets.len()),
        );
        if let Some(b) = body {
            for tb in &b.try_blocks {
                eprintln!("    try {} +{} catches={:?}", tb.start, tb.len, tb.catches);
            }
        }
    }
    let mut strs: Vec<(u32, String)> = file
        .entity_map
        .iter()
        .map(|(&o, &s)| (o, file.strings.resolve(s).unwrap_or("?").to_string()))
        .collect();
    strs.sort();
    eprintln!("  entity_map: {strs:?}");
}

// ─── Replica of abcd-lower's liveness + interference (for inspection) ───────

fn phi_entries(module: &Module, block: BlockId) -> Vec<(BlockId, ValueId, ValueId)> {
    let mut out = Vec::new();
    for &iid in &module.blocks[block.index()].insts {
        let inst = &module.insts[iid.index()];
        let abcd_ir2::Op::Phi { entries } = &inst.op else { break };
        let Some(result) = inst.result else { continue };
        for (edge, val) in entries {
            out.push((edge.from, *val, result));
        }
    }
    out
}

#[allow(clippy::type_complexity)]
fn v2_graph(module: &Module, func_id: FuncId) -> (HashMap<ValueId, HashSet<ValueId>>, HashMap<BlockId, Vec<u32>>) {
    let rpo = abcd_lower::analysis::compute_rpo(module, func_id);
    let func = &module.functions[func_id.index()];
    let suppression = abcd_lower::fusion::analyze(module, &func.blocks);
    let consts = abcd_lower::regalloc::frame_init_consts(module, func_id);

    let succs: HashMap<BlockId, Vec<BlockId>> = rpo
        .iter()
        .map(|&bb| (bb, abcd_lower::analysis::augmented_succs(module, func_id, bb)))
        .collect();

    let mut block_use: HashMap<BlockId, HashSet<ValueId>> = HashMap::new();
    let mut block_def: HashMap<BlockId, HashSet<ValueId>> = HashMap::new();
    for &bb in &rpo {
        let mut uses = HashSet::new();
        let mut defs = HashSet::new();
        let block = &module.blocks[bb.index()];
        for &iid in &block.insts {
            let node = &module.insts[iid.index()];
            if node.op.is_phi() {
                if let Some(r) = node.result {
                    defs.insert(r);
                }
                continue;
            }
            for val in node.op.operands() {
                if !defs.contains(&val) {
                    uses.insert(val);
                }
            }
            if let Some(r) = node.result {
                defs.insert(r);
            }
        }
        block_use.insert(bb, uses);
        block_def.insert(bb, defs);
    }
    if let Some(entry) = rpo.first() {
        for &c in &consts {
            block_def.entry(*entry).or_default().insert(c);
        }
    }
    for &bb in &rpo {
        for &(pred, val, _) in &phi_entries(module, bb) {
            let pred_def = block_def.get(&pred).cloned().unwrap_or_default();
            if !pred_def.contains(&val) {
                block_use.entry(pred).or_default().insert(val);
            }
        }
    }
    let mut live_in: HashMap<BlockId, HashSet<ValueId>> = HashMap::new();
    let mut live_out: HashMap<BlockId, HashSet<ValueId>> = HashMap::new();
    for &bb in &rpo {
        live_in.insert(bb, HashSet::new());
        live_out.insert(bb, HashSet::new());
    }
    let mut changed = true;
    while changed {
        changed = false;
        for &bb in rpo.iter().rev() {
            let empty: Vec<BlockId> = Vec::new();
            let bb_succs = succs.get(&bb).unwrap_or(&empty);
            let mut new_out = HashSet::new();
            for &succ in bb_succs {
                if let Some(succ_in) = live_in.get(&succ) {
                    new_out.extend(succ_in);
                }
            }
            for &succ in bb_succs {
                for &(pred, val, _) in &phi_entries(module, succ) {
                    if pred == bb {
                        new_out.insert(val);
                    }
                }
            }
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

    let mut graph: HashMap<ValueId, HashSet<ValueId>> = HashMap::new();
    for &bb in &rpo {
        let block = &module.blocks[bb.index()];
        let mut live: HashSet<ValueId> = live_out.get(&bb).cloned().unwrap_or_default();
        for &iid in block.insts.iter().rev() {
            let node = &module.insts[iid.index()];
            if let Some(result) = node.result {
                for &v in &live {
                    if v != result {
                        graph.entry(result).or_default().insert(v);
                        graph.entry(v).or_default().insert(result);
                    }
                }
                live.remove(&result);
            }
            if node.op.is_phi() {
                continue;
            }
            for val in node.op.operands() {
                live.insert(val);
            }
        }
        if Some(bb) == rpo.first().copied() {
            for &c in &consts {
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

    // N13
    let mut handler_exc: Vec<(BlockId, ValueId)> = Vec::new();
    for region in &func.try_regions {
        for catch in &region.catches {
            if !handler_exc.contains(&(catch.handler, catch.exception)) {
                handler_exc.push((catch.handler, catch.exception));
            }
        }
    }
    for &(handler, exc) in &handler_exc {
        if let Some(live) = live_in.get(&handler) {
            for &w in live {
                if w != exc {
                    graph.entry(exc).or_default().insert(w);
                    graph.entry(w).or_default().insert(exc);
                }
            }
        }
    }
    // N21
    let handler_blocks: HashSet<BlockId> = func
        .try_regions
        .iter()
        .flat_map(|r| r.catches.iter().map(|c| c.handler))
        .collect();
    let mut used: HashSet<ValueId> = HashSet::new();
    for &bb in &rpo {
        for &iid in &module.blocks[bb.index()].insts {
            used.extend(
                module.insts[iid.index()]
                    .op
                    .operands()
                    .into_iter()
                    .filter(|v| !suppression.values.contains(v)),
            );
        }
    }
    for &handler in &handler_blocks {
        for &(pred, _, result) in &phi_entries(module, handler) {
            if !used.contains(&result) {
                continue;
            }
            let mut forbid: HashSet<ValueId> = live_in.get(&pred).cloned().unwrap_or_default();
            for &iid in &module.blocks[pred.index()].insts {
                if let Some(r) = module.insts[iid.index()].result {
                    forbid.insert(r);
                }
            }
            for w in forbid {
                if w != result {
                    graph.entry(result).or_default().insert(w);
                    graph.entry(w).or_default().insert(result);
                }
            }
        }
    }

    let mut live_in_dump: HashMap<BlockId, Vec<u32>> = HashMap::new();
    for (bb, set) in &live_in {
        let mut v: Vec<u32> = set.iter().map(|v| v.0).collect();
        v.sort();
        live_in_dump.insert(*bb, v);
    }
    (graph, live_in_dump)
}

#[test]
#[ignore = "diagnostic"]
fn structural_diff() {
    let v1 = std::fs::read(std::env::var("ABCD_V1").unwrap()).unwrap();
    let v2 = std::fs::read(std::env::var("ABCD_V2").unwrap()).unwrap();
    dump("v1", &abcd_file::decode(&v1).unwrap());
    dump("v2", &abcd_file::decode(&v2).unwrap());

    let orig =
        abcd_file::decode(&std::fs::read(std::env::var("ABCD_ORIG").unwrap()).unwrap()).unwrap();
    let module = abcd_lift::lift_file(&orig).unwrap();
    let name_want = std::env::var("ABCD_FUNC").unwrap_or_default();
    for (fi, f) in module.functions.iter().enumerate() {
        if !name_want.is_empty()
            && module.sym.resolve(f.name).unwrap_or("?").contains(&name_want)
        {
            let fid = FuncId::new(fi as u32);
            let (graph, live_in) = v2_graph(&module, fid);
            for bb in [35u32, 38, 45] {
                eprintln!("live_in[{bb}] = {:?}", live_in[&BlockId::new(bb)]);
            }
            for v in [145u32, 146, 147, 163] {
                let mut n: Vec<u32> = graph
                    .get(&ValueId::new(v))
                    .map(|s| s.iter().map(|v| v.0).collect())
                    .unwrap_or_default();
                n.sort();
                eprintln!("neighbors[{v}] ({}): {n:?}", n.len());
            }
        }
    }
}
