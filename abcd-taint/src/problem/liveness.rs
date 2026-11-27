//! Per-function backward SSA local liveness (`LocalLiveness`), aliasing property-load
//! reachability (`FuncAliasLoads`), and OHOS JSBridge proxy seed discovery.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};

use abcd_analysis::dataflow::heap::AllocSiteSet;
use abcd_ir::{BlockId, CallKind, Const, FuncId, InstId, Module, Op, ValueDef, ValueId};

use crate::gap;
use crate::names::call_base_value;
use crate::oracle::Oracle;

use super::indexes::ctor_this_of_module;
use super::{JsBridgePropIndex, ParamBinding, param_binding};

const UNUSED_BLOCK: u32 = u32::MAX;
const MULTI_USE_BLOCK: u32 = u32::MAX - 1;

#[derive(Clone, Copy)]
pub(super) struct InstLivenessLoc {
    pub(super) block_local: u32,
    pub(super) pos: u32,
}

enum InstLocMap {
    Empty,
    Dense { base: u32, table: Box<[(u32, u32)]> },
    Sparse(Box<[(u32, u32, u32)]>),
}

impl InstLocMap {
    fn build(module: &Module, local_blocks: &[BlockId]) -> Self {
        let mut raw_entries: Vec<(u32, u32, u32)> = Vec::new();
        let mut min_raw = u32::MAX;
        let mut max_raw = 0u32;
        for (b_local, &b) in local_blocks.iter().enumerate() {
            let Some(bb) = module.block(b) else { continue };
            for (pos, &iid) in bb.insts.iter().enumerate() {
                let r = iid.raw();
                min_raw = min_raw.min(r);
                max_raw = max_raw.max(r);
                raw_entries.push((r, b_local as u32, pos as u32));
            }
        }
        if raw_entries.is_empty() {
            return Self::Empty;
        }
        let span = (max_raw - min_raw) as usize + 1;
        if span <= raw_entries.len().saturating_mul(2).max(16) {
            let mut table = vec![(UNUSED_BLOCK, 0u32); span];
            for &(r, bl, pos) in &raw_entries {
                let slot = &mut table[(r - min_raw) as usize];
                if slot.0 == UNUSED_BLOCK {
                    *slot = (bl, pos);
                }
            }
            Self::Dense {
                base: min_raw,
                table: table.into_boxed_slice(),
            }
        } else {
            raw_entries.sort_by_key(|&(r, _, _)| r);
            raw_entries.dedup_by_key(|e| e.0);
            Self::Sparse(raw_entries.into_boxed_slice())
        }
    }

    #[inline]
    fn get(&self, inst: InstId) -> Option<InstLivenessLoc> {
        match self {
            Self::Empty => None,
            Self::Dense { base, table } => {
                let off = inst.raw().checked_sub(*base)? as usize;
                let &(block_local, pos) = table.get(off)?;
                (block_local != UNUSED_BLOCK).then_some(InstLivenessLoc { block_local, pos })
            }
            Self::Sparse(entries) => {
                let idx = entries
                    .binary_search_by_key(&inst.raw(), |&(r, _, _)| r)
                    .ok()?;
                let &(_, block_local, pos) = &entries[idx];
                Some(InstLivenessLoc { block_local, pos })
            }
        }
    }
}

pub(super) struct FuncLiveness {
    loc_map: InstLocMap,
    words_per_block: usize,
    aug_live_out_words: Vec<u64>,
    val_to_lidx: HashMap<ValueId, u32>,
    single_block_last_use: Vec<(u32, u32)>,
    multi_block_last_use: HashMap<(u32, u32), u32>,
}

impl FuncLiveness {
    fn empty() -> Self {
        Self::empty_with_locs(InstLocMap::Empty)
    }

    fn empty_with_locs(loc_map: InstLocMap) -> Self {
        Self {
            loc_map,
            words_per_block: 0,
            aug_live_out_words: Vec::new(),
            val_to_lidx: HashMap::new(),
            single_block_last_use: Vec::new(),
            multi_block_last_use: HashMap::new(),
        }
    }

    fn build(module: &Module, fid: FuncId, await_resume: &HashMap<InstId, Vec<ValueId>>) -> Self {
        let Some(f) = module.func(fid) else {
            return Self::empty();
        };
        if f.blocks.is_empty() {
            return Self::empty();
        }

        let mut local_blocks: Vec<BlockId> = Vec::with_capacity(f.blocks.len());
        let mut block_to_local: HashMap<BlockId, usize> = HashMap::with_capacity(f.blocks.len());
        for &b in &f.blocks {
            if let std::collections::hash_map::Entry::Vacant(e) = block_to_local.entry(b) {
                e.insert(local_blocks.len());
                local_blocks.push(b);
            }
        }
        let loc_map = InstLocMap::build(module, &local_blocks);
        let num_blocks = local_blocks.len();
        let ctor_this = ctor_this_of_module(module, fid);

        let mut val_to_lidx: HashMap<ValueId, u32> = HashMap::new();
        let mut intern_val = |v: ValueId| {
            if v.index() >= module.values.len() {
                return;
            }
            let next_id = val_to_lidx.len() as u32;
            val_to_lidx.entry(v).or_insert(next_id);
        };

        for &p in &f.params {
            intern_val(p);
        }
        for region in &f.try_regions {
            for catch in &region.catches {
                intern_val(catch.exception);
            }
        }
        for &b in &local_blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if let Some(res) = inst.result {
                    intern_val(res);
                }
                inst.op.for_each_operand(&mut intern_val);
                if matches!(inst.op, Op::Call { .. })
                    && let Some(base_v) = call_base_value(module, inst)
                {
                    intern_val(base_v);
                }
                if matches!(inst.op, Op::ResumeGenerator { .. })
                    && let Some(aws) = await_resume.get(&iid)
                {
                    for &aw in aws {
                        intern_val(aw);
                    }
                }
                if matches!(inst.op, Op::Return { .. })
                    && let Some(ct) = ctor_this
                {
                    intern_val(ct);
                }
            }
        }

        let num_vals = val_to_lidx.len();
        let words = num_vals.div_ceil(64);
        if words == 0 {
            return Self::empty_with_locs(loc_map);
        }

        let mut single_block_last_use = vec![(UNUSED_BLOCK, 0u32); num_vals];
        let mut multi_block_last_use: HashMap<(u32, u32), u32> = HashMap::new();

        let mut norm_succs: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];
        let mut norm_preds: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];
        let mut exc_succs: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];
        let mut exc_preds: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];
        let mut entry_exc_kill = vec![0u64; num_blocks * words];

        for (b_local, &b) in local_blocks.iter().enumerate() {
            for s in abcd_analysis::control::block_succs(module, b) {
                if let Some(&sl) = block_to_local.get(&s)
                    && !norm_succs[b_local].contains(&sl)
                {
                    norm_succs[b_local].push(sl);
                    norm_preds[sl].push(b_local);
                }
            }
        }
        for region in &f.try_regions {
            let mut handlers = Vec::new();
            for catch in &region.catches {
                if let Some(&hl_usize) = block_to_local.get(&catch.handler) {
                    if !handlers.contains(&hl_usize) {
                        handlers.push(hl_usize);
                    }
                    if let Some(&lidx) = val_to_lidx.get(&catch.exception) {
                        let li = lidx as usize;
                        entry_exc_kill[hl_usize * words + li / 64] |= 1u64 << (li % 64);
                    }
                }
            }
            for &prot_b in &region.protected {
                if let Some(&pl_usize) = block_to_local.get(&prot_b) {
                    for &hl in &handlers {
                        if !exc_succs[pl_usize].contains(&hl) {
                            exc_succs[pl_usize].push(hl);
                            exc_preds[hl].push(pl_usize);
                        }
                    }
                }
            }
        }

        let mut gen_bits = vec![0u64; num_blocks * words];
        let mut kill_bits = vec![0u64; num_blocks * words];

        for (b_local, &b) in local_blocks.iter().enumerate() {
            let Some(bb) = module.block(b) else { continue };
            let b_u32 = b_local as u32;
            let base_w = b_local * words;

            let mut record_use =
                |v: ValueId, pos_u32: u32, gen_s: &mut [u64], kill_s: &mut [u64]| {
                    let Some(&lidx) = val_to_lidx.get(&v) else {
                        return;
                    };
                    let li = lidx as usize;
                    let w = li / 64;
                    let mask = 1u64 << (li % 64);
                    gen_s[w] |= mask;
                    kill_s[w] &= !mask;

                    let sb = &mut single_block_last_use[li];
                    if sb.0 == UNUSED_BLOCK {
                        *sb = (b_u32, pos_u32);
                    } else if sb.0 == b_u32 {
                        // Reverse iteration visits the maximum position first.
                    } else if sb.0 != MULTI_USE_BLOCK {
                        let (prev_b, prev_max) = *sb;
                        *sb = (MULTI_USE_BLOCK, 0);
                        multi_block_last_use.insert((prev_b, lidx), prev_max);
                        multi_block_last_use.insert((b_u32, lidx), pos_u32);
                    } else {
                        multi_block_last_use.entry((b_u32, lidx)).or_insert(pos_u32);
                    }
                };

            let gen_slice = &mut gen_bits[base_w..base_w + words];
            let kill_slice = &mut kill_bits[base_w..base_w + words];

            for (pos, &iid) in bb.insts.iter().enumerate().rev() {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if let Some(res) = inst.result
                    && let Some(&lidx) = val_to_lidx.get(&res)
                {
                    let li = lidx as usize;
                    let w = li / 64;
                    let mask = 1u64 << (li % 64);
                    gen_slice[w] &= !mask;
                    kill_slice[w] |= mask;
                }
                let pos_u32 = pos as u32;
                inst.op.for_each_operand(|u| {
                    record_use(u, pos_u32, gen_slice, kill_slice);
                });
                if matches!(inst.op, Op::Call { .. })
                    && let Some(base_v) = call_base_value(module, inst)
                {
                    record_use(base_v, pos_u32, gen_slice, kill_slice);
                }
                if matches!(inst.op, Op::ResumeGenerator { .. })
                    && let Some(aws) = await_resume.get(&iid)
                {
                    for &aw in aws {
                        record_use(aw, pos_u32, gen_slice, kill_slice);
                    }
                }
                if matches!(inst.op, Op::Return { .. })
                    && let Some(ct) = ctor_this
                {
                    record_use(ct, pos_u32, gen_slice, kill_slice);
                }
            }
        }

        let mut live_in = gen_bits.clone();
        let mut queue: VecDeque<usize> = (0..num_blocks).rev().collect();
        let mut in_queue = vec![true; num_blocks];

        while let Some(b_local) = queue.pop_front() {
            in_queue[b_local] = false;
            let base_w = b_local * words;
            let mut changed = false;
            for w in 0..words {
                let mut norm_out = 0u64;
                for &s in &norm_succs[b_local] {
                    norm_out |= live_in[s * words + w];
                }
                let mut exc_out = 0u64;
                for &h in &exc_succs[b_local] {
                    exc_out |= live_in[h * words + w] & !entry_exc_kill[h * words + w];
                }
                let new_in = (norm_out & !kill_bits[base_w + w]) | gen_bits[base_w + w] | exc_out;
                if new_in != live_in[base_w + w] {
                    live_in[base_w + w] = new_in;
                    changed = true;
                }
            }
            if changed {
                for &p in norm_preds[b_local].iter().chain(exc_preds[b_local].iter()) {
                    if !in_queue[p] {
                        in_queue[p] = true;
                        queue.push_back(p);
                    }
                }
            }
        }

        let mut aug_live_out_words = Vec::with_capacity(num_blocks * words);
        for b_local in 0..num_blocks {
            for w in 0..words {
                let mut aug_out = 0u64;
                for &s in &norm_succs[b_local] {
                    aug_out |= live_in[s * words + w];
                }
                for &h in &exc_succs[b_local] {
                    aug_out |= live_in[h * words + w] & !entry_exc_kill[h * words + w];
                }
                aug_live_out_words.push(aug_out);
            }
        }

        Self {
            loc_map,
            words_per_block: words,
            aug_live_out_words,
            val_to_lidx,
            single_block_last_use,
            multi_block_last_use,
        }
    }

    fn is_live_at_loc(&self, loc: InstLivenessLoc, v: ValueId) -> bool {
        if self.words_per_block == 0 {
            return false;
        }
        let Some(&lidx) = self.val_to_lidx.get(&v) else {
            return false;
        };
        let word_idx = (loc.block_local as usize) * self.words_per_block + (lidx as usize / 64);
        if self
            .aug_live_out_words
            .get(word_idx)
            .is_some_and(|&w| ((w >> (lidx % 64)) & 1) != 0)
        {
            return true;
        }
        let Some(&(ublk, max_pos)) = self.single_block_last_use.get(lidx as usize) else {
            return true;
        };
        if ublk == loc.block_local {
            max_pos >= loc.pos
        } else if ublk == MULTI_USE_BLOCK {
            self.multi_block_last_use
                .get(&(loc.block_local, lidx))
                .is_some_and(|&mp| mp >= loc.pos)
        } else {
            false
        }
    }
}

/// Compact lazy per-function backward SSA liveness index over [`Module`] (`#78`).
pub(super) struct LocalLiveness {
    #[cfg(test)]
    pub(super) funcs: RefCell<Vec<Option<Box<FuncLiveness>>>>,
    #[cfg(not(test))]
    funcs: RefCell<Vec<Option<Box<FuncLiveness>>>>,
}

impl LocalLiveness {
    pub(super) fn new(n_funcs: usize) -> Self {
        let mut funcs = Vec::with_capacity(n_funcs);
        funcs.resize_with(n_funcs, || None);
        Self {
            funcs: RefCell::new(funcs),
        }
    }

    pub(super) fn clear(&self) {
        *self.funcs.borrow_mut() = Vec::new();
    }

    #[cfg(test)]
    pub(super) fn is_live_at(
        &self,
        module: &Module,
        block_func: &[Option<FuncId>],
        await_resume: &HashMap<InstId, Vec<ValueId>>,
        at_inst: InstId,
        v: ValueId,
    ) -> bool {
        self.resolve_loc_and_live(module, block_func, await_resume, at_inst, v)
            .is_none_or(|(_, _, live)| live)
    }

    pub(super) fn resolve_loc_and_live(
        &self,
        module: &Module,
        block_func: &[Option<FuncId>],
        await_resume: &HashMap<InstId, Vec<ValueId>>,
        at_inst: InstId,
        v: ValueId,
    ) -> Option<(FuncId, InstLivenessLoc, bool)> {
        if v.index() >= module.values.len() {
            return None;
        }
        let block = module.inst(at_inst)?.block;
        let fid = block_func.get(block.index()).copied().flatten()?;
        let fidx = fid.index();
        let has_built = self.funcs.borrow().get(fidx).is_some_and(Option::is_some);
        if !has_built {
            let built = FuncLiveness::build(module, fid, await_resume);
            if let Some(slot) = self.funcs.borrow_mut().get_mut(fidx) {
                *slot = Some(Box::new(built));
            }
        }
        let funcs_borrow = self.funcs.borrow();
        let fl = funcs_borrow.get(fidx)?.as_ref()?;
        let loc = fl.loc_map.get(at_inst)?;
        let live = fl.is_live_at_loc(loc, v);
        Some((fid, loc, live))
    }
}

pub(super) struct ValueAliasLoads {
    pub(super) func: u32,
    pub(super) load_ids: Box<[u32]>,
}

struct AliasLoadSite {
    block_local: u32,
    pos: u32,
    object: ValueId,
}

/// Per-function reachability index over property loads whose `object` has
/// non-empty `site_info_at` allocation sites (built lazily at most once per
/// function when a dead local taint fact is tested for pruning).
pub(super) struct FuncAliasLoads {
    loads: Vec<AliasLoadSite>,
    words_per_block: usize,
    reach_out_words: Vec<u64>,
    site_to_loads: HashMap<InstId, Vec<u32>>,
}

impl FuncAliasLoads {
    pub(super) fn empty() -> Self {
        Self {
            loads: Vec::new(),
            words_per_block: 0,
            reach_out_words: Vec::new(),
            site_to_loads: HashMap::new(),
        }
    }

    pub(super) fn build(module: &Module, fid: FuncId, oracle: &Oracle) -> Self {
        let Some(f) = module.func(fid) else {
            return Self::empty();
        };
        if f.blocks.is_empty() {
            return Self::empty();
        }
        let mut local_blocks: Vec<BlockId> = Vec::with_capacity(f.blocks.len());
        let mut block_to_local: HashMap<BlockId, usize> = HashMap::with_capacity(f.blocks.len());
        for &b in &f.blocks {
            if let std::collections::hash_map::Entry::Vacant(e) = block_to_local.entry(b) {
                e.insert(local_blocks.len());
                local_blocks.push(b);
            }
        }

        let mut loads = Vec::new();
        let mut site_to_loads: HashMap<InstId, Vec<u32>> = HashMap::new();
        for (b_local, &b) in local_blocks.iter().enumerate() {
            let Some(bb) = module.block(b) else { continue };
            for (pos, &iid) in bb.insts.iter().enumerate() {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                let (Op::LoadProp { object, .. }
                | Op::LoadPropIdx { object, .. }
                | Op::LoadPropDyn { object, .. }
                | Op::LoadPrivate { obj: object, .. }) = &inst.op
                else {
                    continue;
                };
                let obj_sites = oracle.site_info_at(*object, iid).sites;
                if obj_sites.is_empty() {
                    continue;
                }
                let load_idx = loads.len() as u32;
                loads.push(AliasLoadSite {
                    block_local: b_local as u32,
                    pos: pos as u32,
                    object: *object,
                });
                for site in obj_sites.iter() {
                    site_to_loads.entry(site).or_default().push(load_idx);
                }
            }
        }

        if loads.is_empty() {
            return Self::empty();
        }

        let num_blocks = local_blocks.len();
        let words = loads.len().div_ceil(64);
        let mut succs: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); num_blocks];

        for (b_local, &b) in local_blocks.iter().enumerate() {
            for s in abcd_analysis::control::block_succs(module, b) {
                if let Some(&sl) = block_to_local.get(&s)
                    && !succs[b_local].contains(&sl)
                {
                    succs[b_local].push(sl);
                    preds[sl].push(b_local);
                }
            }
        }
        for region in &f.try_regions {
            let mut handlers = Vec::new();
            for catch in &region.catches {
                if let Some(&hl) = block_to_local.get(&catch.handler)
                    && !handlers.contains(&hl)
                {
                    handlers.push(hl);
                }
            }
            for &prot_b in &region.protected {
                if let Some(&pl) = block_to_local.get(&prot_b) {
                    for &hl in &handlers {
                        if !succs[pl].contains(&hl) {
                            succs[pl].push(hl);
                            preds[hl].push(pl);
                        }
                    }
                }
            }
        }

        let mut reach_in = vec![0u64; num_blocks * words];
        for (k, ld) in loads.iter().enumerate() {
            reach_in[(ld.block_local as usize) * words + k / 64] |= 1u64 << (k % 64);
        }
        let mut queue: VecDeque<usize> = (0..num_blocks).rev().collect();
        let mut in_queue = vec![true; num_blocks];
        while let Some(b_local) = queue.pop_front() {
            in_queue[b_local] = false;
            let base_w = b_local * words;
            let mut changed = false;
            for w in 0..words {
                let mut out_bits = reach_in[base_w + w];
                for &s in &succs[b_local] {
                    out_bits |= reach_in[s * words + w];
                }
                if out_bits != reach_in[base_w + w] {
                    reach_in[base_w + w] = out_bits;
                    changed = true;
                }
            }
            if changed {
                for &p in &preds[b_local] {
                    if !in_queue[p] {
                        in_queue[p] = true;
                        queue.push_back(p);
                    }
                }
            }
        }

        let mut reach_out_words = Vec::with_capacity(num_blocks * words);
        for succ_list in &succs {
            for w in 0..words {
                let mut out_bits = 0u64;
                for &s in succ_list {
                    out_bits |= reach_in[s * words + w];
                }
                reach_out_words.push(out_bits);
            }
        }

        Self {
            loads,
            words_per_block: words,
            reach_out_words,
            site_to_loads,
        }
    }

    pub(super) fn matching_loads_for(&self, v: ValueId, v_sites: &AllocSiteSet) -> Vec<u32> {
        if self.loads.is_empty() {
            return Vec::new();
        }
        let mut out = Vec::new();
        for site in v_sites.iter() {
            let Some(cands) = self.site_to_loads.get(&site) else {
                continue;
            };
            for &k in cands {
                if let Some(ld) = self.loads.get(k as usize)
                    && ld.object != v
                    && !out.contains(&k)
                {
                    out.push(k);
                }
            }
        }
        out
    }

    pub(super) fn any_reachable_at(&self, loc: InstLivenessLoc, load_ids: &[u32]) -> bool {
        if self.words_per_block == 0 {
            return false;
        }
        let b_base = (loc.block_local as usize) * self.words_per_block;
        for &k in load_ids {
            let ku = k as usize;
            let Some(ld) = self.loads.get(ku) else {
                continue;
            };
            if ld.block_local == loc.block_local && ld.pos >= loc.pos {
                return true;
            }
            if self
                .reach_out_words
                .get(b_base + ku / 64)
                .is_some_and(|&w| ((w >> (ku % 64)) & 1) != 0)
            {
                return true;
            }
        }
        false
    }
}

pub(super) fn build_jsbridge_prop_index(module: &Module) -> JsBridgePropIndex {
    let mut index: JsBridgePropIndex = HashMap::new();
    for inst in &module.insts {
        match &inst.op {
            Op::StoreProp {
                object,
                name,
                value,
            }
            | Op::StoreOwnPropName {
                object,
                name,
                value,
                ..
            } => {
                index.entry(*object).or_default().push((*name, *value));
            }
            Op::DefineMethod {
                object, name, func, ..
            } => {
                index.entry(*object).or_default().push((*name, *func));
            }
            _ => {}
        }
    }
    index
}

/// Discover methods exposed on `proxy_obj` via
/// `WebviewController.registerJavaScriptProxy(proxy_obj, name, methodList)`
/// and seed their formal parameters as untrusted JSBridge inputs.
pub(super) fn collect_jsbridge_seeds(
    module: &Module,
    oracle: &Oracle,
    prop_index: &JsBridgePropIndex,
    proxy_obj: ValueId,
    method_list: Option<ValueId>,
    at: InstId,
    param_seeds: &mut Vec<(FuncId, Vec<ValueId>)>,
) {
    let allowed_names: Option<HashSet<String>> = method_list.and_then(|ml| {
        let ValueDef::Inst(iid) = module.value(ml)?.def else {
            return None;
        };
        let Op::AllocArray {
            shape: Some(arr_cid),
        } = &module.inst(iid)?.op
        else {
            return None;
        };
        let Const::ArrayLiteral(items) = module.consts.get(*arr_cid)? else {
            return None;
        };
        let mut set = HashSet::new();
        for &it_cid in items {
            if let Some(Const::String(s)) = module.consts.get(it_cid)
                && let Some(txt) = module.sym.resolve(*s)
            {
                set.insert(txt.to_owned());
            }
        }
        (!set.is_empty()).then_some(set)
    });

    let name_allowed = |mname: &str| -> bool {
        !mname.is_empty()
            && mname != "constructor"
            && !mname.starts_with("#~@")
            && allowed_names.as_ref().is_none_or(|s| s.contains(mname))
    };

    let mut candidate_funcs: Vec<FuncId> = Vec::new();
    let mut sites: Vec<InstId> = oracle.may_sites_at(proxy_obj, at).iter().collect();
    if let Some(ValueDef::Inst(def_iid)) = module.value(proxy_obj).map(|v| v.def)
        && !sites.contains(&def_iid)
    {
        sites.push(def_iid);
    }

    for site in sites {
        let Some(site_inst) = module.inst(site) else {
            continue;
        };
        match &site_inst.op {
            Op::AllocObject { shape } => {
                if let Some(Const::ObjectLiteral { keys, values }) = module.consts.get(*shape) {
                    for (&k_cid, &v_cid) in keys.iter().zip(values.iter()) {
                        if let (Some(Const::String(ks)), Some(Const::MethodRef { func: mfid, .. })) =
                            (module.consts.get(k_cid), module.consts.get(v_cid))
                            && let Some(mname) = module.sym.resolve(*ks)
                            && name_allowed(mname)
                        {
                            candidate_funcs.push(*mfid);
                        }
                    }
                }
                if let Some(obj_val) = site_inst.result
                    && let Some(props) = prop_index.get(&obj_val)
                {
                    for &(name, fn_val) in props {
                        if let Some(mname) = module.sym.resolve(name)
                            && name_allowed(mname)
                        {
                            for f in gap::resolve_callback_funcs(module, oracle, fn_val, at) {
                                candidate_funcs.push(f);
                            }
                        }
                    }
                }
            }
            Op::Call {
                callee,
                kind: CallKind::New | CallKind::NewSpread,
                ..
            } => {
                if let Some(ValueDef::Inst(cls_iid)) = module.value(*callee).map(|v| v.def)
                    && let Some(Op::DefineClass(data) | Op::DefineSendableClass(data)) =
                        module.inst(cls_iid).map(|i| &i.op)
                    && let Some(Const::ArrayLiteral(items)) = module.consts.get(data.members)
                {
                    let mut pending: Option<&str> = None;
                    for &it_cid in items {
                        match module.consts.get(it_cid) {
                            Some(Const::String(s)) => pending = module.sym.resolve(*s),
                            Some(Const::MethodRef { func: mfid, .. }) => {
                                if let Some(mname) = pending.take()
                                    && name_allowed(mname)
                                {
                                    candidate_funcs.push(*mfid);
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            _ => {}
        }
    }

    candidate_funcs.sort();
    candidate_funcs.dedup();
    for mfid in candidate_funcs {
        let Some(fd) = module.func(mfid) else {
            continue;
        };
        let formals: Vec<ValueId> = match param_binding(module, mfid) {
            ParamBinding::Precise { formal_base, .. } => {
                fd.params.iter().skip(formal_base).copied().collect()
            }
            ParamBinding::OverApproxAll => fd.params.clone(),
        };
        if !formals.is_empty() {
            param_seeds.push((mfid, formals));
        }
    }
}
