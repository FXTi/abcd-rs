//! Static lexical-environment scope chains (`StaticLexEnvTable`) and synthetic
//! `#private` class-field slot indexing (`PrivateFieldIndex`).

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use abcd_analysis::module_link::ModuleLinkTable;
use abcd_ir::{
    BlockId, ClassId, Const, FuncId, InstId, LexEnvKind, Module, Op, Sym, ValueDef, ValueId,
};

pub(super) const PRIVATE_SYM_TAG: u32 = 0x8000_0000;
pub(super) const LEX_SYM_TAG: u32 = 0xC000_0000;

#[inline]
pub(super) fn is_synthetic_slot_sym(sym: Sym) -> bool {
    (sym.index() as u32) >= PRIVATE_SYM_TAG
}

#[inline]
pub(super) fn lex_slot_sym(slot: u16) -> Sym {
    Sym::new(LEX_SYM_TAG | u32::from(slot))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum StaticEnvKey {
    Inst(InstId),
    ImplicitFunc(FuncId),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct StaticEnvChain {
    frames: Vec<BTreeSet<InstId>>,
}

impl StaticEnvChain {
    const MAX_DEPTH: usize = 32;

    fn push_site(&mut self, site: InstId) {
        self.frames.push(BTreeSet::from([site]));
        if self.frames.len() > Self::MAX_DEPTH {
            let overflow = self.frames.len() - Self::MAX_DEPTH;
            self.frames.drain(0..overflow);
        }
    }

    fn pop_frame(&mut self) {
        let _ = self.frames.pop();
    }

    fn join_into(&mut self, other: &Self) -> bool {
        let max_len = self.frames.len().max(other.frames.len());
        if max_len == 0 {
            return false;
        }
        let mut merged = Vec::with_capacity(max_len);
        for from_top in (0..max_len).rev() {
            let mut set = BTreeSet::new();
            if from_top < self.frames.len() {
                set.extend(&self.frames[self.frames.len() - 1 - from_top]);
            }
            if from_top < other.frames.len() {
                set.extend(&other.frames[other.frames.len() - 1 - from_top]);
            }
            merged.push(set);
        }
        if self.frames != merged {
            self.frames = merged;
            true
        } else {
            false
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct StaticEnvState {
    plain: StaticEnvChain,
    sendable: StaticEnvChain,
}

impl StaticEnvState {
    fn chain(&self, kind: LexEnvKind) -> &StaticEnvChain {
        match kind {
            LexEnvKind::Sendable => &self.sendable,
            LexEnvKind::Plain | LexEnvKind::Patch => &self.plain,
        }
    }

    fn chain_mut(&mut self, kind: LexEnvKind) -> &mut StaticEnvChain {
        match kind {
            LexEnvKind::Sendable => &mut self.sendable,
            LexEnvKind::Plain | LexEnvKind::Patch => &mut self.plain,
        }
    }

    fn join_into(&mut self, other: &Self) -> bool {
        let c1 = self.plain.join_into(&other.plain);
        let c2 = self.sendable.join_into(&other.sendable);
        c1 || c2
    }
}

/// Static lexical-environment scope table (`R10`): maps each `GetLexVar`,
/// `PutLexVar`, and `*Private` instruction to canonical `u16` scope IDs and
/// explicit `NewLexEnv` sites so `StoreLexVar { level: 0, slot }` in an outer
/// function matches `LoadLexVar { level: 1, slot }` inside a nested closure
/// across Rung 0 and Rung 1 without raw `(level, slot)` mismatch.
pub(crate) struct StaticLexEnvTable {
    inst_env_ids: HashMap<InstId, Vec<u16>>,
    inst_explicit_sites: HashMap<InstId, Vec<InstId>>,
}

impl StaticLexEnvTable {
    pub(super) fn build(module: &Module, links: &ModuleLinkTable) -> Self {
        let n_funcs = module.functions.len();
        let mut val_funcs: Vec<BTreeSet<FuncId>> = vec![BTreeSet::new(); module.values.len()];
        let mut copy_edges: Vec<Vec<ValueId>> = vec![Vec::new(); module.values.len()];
        let mut val_queue: VecDeque<ValueId> = VecDeque::new();

        for (vi, val) in module.values.iter().enumerate() {
            if let ValueDef::Const(cid) = val.def
                && let Some(Const::MethodRef { func, .. }) = module.consts.get(cid)
            {
                let vid = ValueId::new(vi as u32);
                val_funcs[vi].insert(*func);
                val_queue.push_back(vid);
            }
        }
        for fd in &module.functions {
            for &b in &fd.blocks {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    match &inst.op {
                        Op::DefineFunc { body, .. } => {
                            if let Some(res) = inst.result
                                && let Some(set) = val_funcs.get_mut(res.index())
                                && set.insert(*body)
                            {
                                val_queue.push_back(res);
                            }
                        }
                        Op::LoadConst(cid) => {
                            if let Some(Const::MethodRef { func, .. }) = module.consts.get(*cid)
                                && let Some(res) = inst.result
                                && let Some(set) = val_funcs.get_mut(res.index())
                                && set.insert(*func)
                            {
                                val_queue.push_back(res);
                            }
                        }
                        Op::Mov { src }
                        | Op::AllocClosure { func: src }
                        | Op::CreateGenerator { func: src }
                        | Op::CreateAsyncGenerator { func: src }
                        | Op::DefineMethod { func: src, .. } => {
                            if let Some(res) = inst.result
                                && let Some(outs) = copy_edges.get_mut(src.index())
                            {
                                outs.push(res);
                            }
                        }
                        Op::Phi { entries } => {
                            if let Some(res) = inst.result {
                                for (_, incoming) in entries {
                                    if let Some(outs) = copy_edges.get_mut(incoming.index()) {
                                        outs.push(res);
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        while let Some(v) = val_queue.pop_front() {
            let cur = val_funcs.get(v.index()).cloned().unwrap_or_default();
            if cur.is_empty() {
                continue;
            }
            let outs = copy_edges.get(v.index()).cloned().unwrap_or_default();
            for dst in outs {
                if let Some(dst_set) = val_funcs.get_mut(dst.index()) {
                    let before = dst_set.len();
                    dst_set.extend(cur.iter().copied());
                    if dst_set.len() > before {
                        val_queue.push_back(dst);
                    }
                }
            }
        }

        let collect_const_funcs = |root: abcd_ir::ConstId, out: &mut Vec<FuncId>| {
            let mut visited = HashSet::new();
            let mut stack = vec![root];
            while let Some(cid) = stack.pop() {
                if !visited.insert(cid) {
                    continue;
                }
                match module.consts.get(cid) {
                    Some(Const::MethodRef { func, .. }) => out.push(*func),
                    Some(Const::ArrayLiteral(items) | Const::TypedArrayLiteral { items, .. }) => {
                        for &ch in items.iter().rev() {
                            stack.push(ch);
                        }
                    }
                    Some(Const::ObjectLiteral { keys, values }) => {
                        for &ch in keys.iter().chain(values.iter()).rev() {
                            stack.push(ch);
                        }
                    }
                    Some(Const::LiteralBufferRef(inner)) => stack.push(*inner),
                    _ => {}
                }
            }
        };

        let mut entry_env: Vec<StaticEnvState> = vec![StaticEnvState::default(); n_funcs];
        let mut enclosing_funcs: Vec<BTreeSet<FuncId>> = vec![BTreeSet::new(); n_funcs];
        let mut fn_queue: VecDeque<FuncId> = (0..n_funcs).map(|i| FuncId::new(i as u32)).collect();
        let mut in_fn_queue = vec![true; n_funcs];
        let mut fn_visits = vec![0u8; n_funcs];

        let mut captured_buf = Vec::new();
        while let Some(fid) = fn_queue.pop_front() {
            let fi = fid.index();
            in_fn_queue[fi] = false;
            if fn_visits[fi] >= 4 {
                continue;
            }
            fn_visits[fi] += 1;
            let Some(fd) = module.func(fid) else {
                continue;
            };
            if fd.blocks.is_empty() {
                continue;
            }
            let rpo = abcd_ir::cfg::compute_rpo(module, fid);
            let mut block_to_idx: HashMap<BlockId, usize> = HashMap::with_capacity(rpo.len());
            for (bi, &b) in rpo.iter().enumerate() {
                block_to_idx.insert(b, bi);
            }
            let mut block_in = vec![StaticEnvState::default(); rpo.len()];
            if let Some(first_in) = block_in.first_mut() {
                *first_in = entry_env[fi].clone();
            }
            let exc_map = abcd_ir::cfg::ExceptionHandlerMap::build(module, fid);

            for _pass in 0..2 {
                let mut any_block_changed = false;
                for (bi, &b) in rpo.iter().enumerate() {
                    let mut state = block_in[bi].clone();
                    if let Some(bb) = module.block(b) {
                        for &iid in &bb.insts {
                            let Some(inst) = module.inst(iid) else {
                                continue;
                            };
                            captured_buf.clear();
                            match &inst.op {
                                Op::NewLexEnv { kind, .. } => {
                                    state.chain_mut(*kind).push_site(iid);
                                }
                                Op::NewLexEnvWithName { .. } => {
                                    state.chain_mut(LexEnvKind::Plain).push_site(iid);
                                }
                                Op::PopLexEnv => {
                                    state.chain_mut(LexEnvKind::Plain).pop_frame();
                                }
                                Op::DefineFunc { body, .. } => {
                                    captured_buf.push(*body);
                                }
                                Op::AllocClosure { func }
                                | Op::CreateGenerator { func }
                                | Op::CreateAsyncGenerator { func }
                                | Op::DefineMethod { func, .. } => {
                                    if let Some(fset) = val_funcs.get(func.index()) {
                                        captured_buf.extend(fset.iter().copied());
                                    }
                                }
                                Op::DefineGetterSetterByValue { getter, setter, .. } => {
                                    if let Some(fset) = val_funcs.get(getter.index()) {
                                        captured_buf.extend(fset.iter().copied());
                                    }
                                    if let Some(fset) = val_funcs.get(setter.index()) {
                                        captured_buf.extend(fset.iter().copied());
                                    }
                                }
                                Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                                    captured_buf.push(cls.ctor);
                                    collect_const_funcs(cls.members, &mut captured_buf);
                                }
                                Op::AllocObject { shape } => {
                                    collect_const_funcs(*shape, &mut captured_buf);
                                }
                                Op::AllocArray { shape: Some(shape) } => {
                                    collect_const_funcs(*shape, &mut captured_buf);
                                }
                                _ => {}
                            }
                            for &child_fid in &captured_buf {
                                let ci = child_fid.index();
                                if ci < n_funcs && child_fid != fid {
                                    enclosing_funcs[ci].insert(fid);
                                    if entry_env[ci].join_into(&state) && !in_fn_queue[ci] {
                                        in_fn_queue[ci] = true;
                                        fn_queue.push_back(child_fid);
                                    }
                                }
                            }
                        }
                    }
                    let succs: Vec<BlockId> = match &exc_map {
                        Some(em) => abcd_ir::cfg::augmented_succs_with_map(module, em, b),
                        None => abcd_analysis::control::block_succs(module, b),
                    };
                    for sb in succs {
                        if let Some(&sbi) = block_to_idx.get(&sb)
                            && block_in[sbi].join_into(&state)
                        {
                            any_block_changed = true;
                        }
                    }
                }
                if !any_block_changed {
                    break;
                }
            }
        }

        let mut key_to_id: BTreeMap<StaticEnvKey, u16> = BTreeMap::new();
        let mut intern_env_key = |key: StaticEnvKey| -> u16 {
            if let Some(&id) = key_to_id.get(&key) {
                return id;
            }
            let next = (key_to_id.len() as u32).min(u32::from(u16::MAX - 1)) as u16;
            key_to_id.insert(key, next);
            next
        };

        let mut inst_env_ids: HashMap<InstId, Vec<u16>> = HashMap::new();
        let mut inst_explicit_sites: HashMap<InstId, Vec<InstId>> = HashMap::new();

        for (fi, fd) in module.functions.iter().enumerate() {
            if fd.blocks.is_empty() {
                continue;
            }
            let fid = FuncId::new(fi as u32);
            let rpo = abcd_ir::cfg::compute_rpo(module, fid);
            let mut block_to_idx: HashMap<BlockId, usize> = HashMap::with_capacity(rpo.len());
            for (bi, &b) in rpo.iter().enumerate() {
                block_to_idx.insert(b, bi);
            }
            let mut block_in = vec![StaticEnvState::default(); rpo.len()];
            if let Some(first_in) = block_in.first_mut() {
                *first_in = entry_env[fi].clone();
            }
            let exc_map = abcd_ir::cfg::ExceptionHandlerMap::build(module, fid);

            for pass in 0..2 {
                let mut any_changed = false;
                for (bi, &b) in rpo.iter().enumerate() {
                    let mut state = block_in[bi].clone();
                    if let Some(bb) = module.block(b) {
                        for &iid in &bb.insts {
                            let Some(inst) = module.inst(iid) else {
                                continue;
                            };
                            match &inst.op {
                                Op::NewLexEnv { kind, .. } => {
                                    state.chain_mut(*kind).push_site(iid);
                                }
                                Op::NewLexEnvWithName { .. } => {
                                    state.chain_mut(LexEnvKind::Plain).push_site(iid);
                                }
                                Op::PopLexEnv => {
                                    state.chain_mut(LexEnvKind::Plain).pop_frame();
                                }
                                Op::GetLexVar { level, kind, .. }
                                | Op::PutLexVar { level, kind, .. }
                                    if pass == 1 =>
                                {
                                    let chain = state.chain(*kind);
                                    let lvl = *level as usize;
                                    if lvl < chain.frames.len() {
                                        let sites = &chain.frames[chain.frames.len() - 1 - lvl];
                                        let mut ids = Vec::with_capacity(sites.len());
                                        let mut ex = Vec::with_capacity(sites.len());
                                        for &s in sites {
                                            ex.push(s);
                                            let eid = intern_env_key(StaticEnvKey::Inst(s));
                                            if !ids.contains(&eid) {
                                                ids.push(eid);
                                            }
                                        }
                                        inst_explicit_sites.insert(iid, ex);
                                        inst_env_ids.insert(iid, ids);
                                    } else {
                                        let rem_hops = lvl - chain.frames.len();
                                        let mut cur_fns = BTreeSet::from([fid]);
                                        for _ in 0..rem_hops {
                                            let mut next_fns = BTreeSet::new();
                                            for &cf in &cur_fns {
                                                if let Some(parents) =
                                                    enclosing_funcs.get(cf.index())
                                                {
                                                    next_fns.extend(parents.iter().copied());
                                                }
                                            }
                                            cur_fns = next_fns;
                                            if cur_fns.is_empty() {
                                                break;
                                            }
                                        }
                                        if !cur_fns.is_empty() {
                                            let mut ids = Vec::with_capacity(cur_fns.len());
                                            for af in cur_fns {
                                                let eid =
                                                    intern_env_key(StaticEnvKey::ImplicitFunc(af));
                                                if !ids.contains(&eid) {
                                                    ids.push(eid);
                                                }
                                            }
                                            inst_env_ids.insert(iid, ids);
                                        }
                                    }
                                }
                                Op::LoadPrivate { level, .. }
                                | Op::StorePrivate { level, .. }
                                | Op::DefinePrivate { level, .. }
                                    if pass == 1 =>
                                {
                                    let chain = state.chain(LexEnvKind::Plain);
                                    let lvl = *level as usize;
                                    if lvl < chain.frames.len() {
                                        let sites: Vec<InstId> = chain.frames
                                            [chain.frames.len() - 1 - lvl]
                                            .iter()
                                            .copied()
                                            .collect();
                                        if !sites.is_empty() {
                                            inst_explicit_sites.insert(iid, sites);
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    let succs: Vec<BlockId> = match &exc_map {
                        Some(em) => abcd_ir::cfg::augmented_succs_with_map(module, em, b),
                        None => abcd_analysis::control::block_succs(module, b),
                    };
                    for sb in succs {
                        if let Some(&sbi) = block_to_idx.get(&sb)
                            && block_in[sbi].join_into(&state)
                        {
                            any_changed = true;
                        }
                    }
                }
                if !any_changed && pass == 0 {
                    // Still execute pass == 1 to record per-instruction results.
                }
            }
        }
        let _ = links;
        Self {
            inst_env_ids,
            inst_explicit_sites,
        }
    }

    pub(super) fn empty() -> Self {
        Self {
            inst_env_ids: HashMap::new(),
            inst_explicit_sites: HashMap::new(),
        }
    }

    #[inline]
    pub(crate) fn env_ids_at(&self, inst: InstId) -> &[u16] {
        self.inst_env_ids.get(&inst).map_or(&[], Vec::as_slice)
    }

    #[inline]
    pub(crate) fn explicit_sites_at(&self, inst: InstId) -> &[InstId] {
        self.inst_explicit_sites
            .get(&inst)
            .map_or(&[], Vec::as_slice)
    }
}

/// Pre-indexed canonical synthetic [`Sym`]s for `#private` class fields
/// (`LoadPrivate`, `StorePrivate`, `DefinePrivate`), keyed by
/// `(Option<NewLexEnv InstId>, owning ClassId, slot)` so private fields never
/// collide with string property names or across distinct private slots.
pub(super) struct PrivateFieldIndex {
    by_inst: HashMap<InstId, Vec<Sym>>,
}

impl PrivateFieldIndex {
    pub(super) fn build(
        module: &Module,
        links: &ModuleLinkTable,
        lex_env: &StaticLexEnvTable,
    ) -> Self {
        let mut key_to_sym: BTreeMap<(Option<InstId>, ClassId, u16), Sym> = BTreeMap::new();
        let mut next_priv = 0u32;
        let mut intern_priv = |key: (Option<InstId>, ClassId, u16)| -> Sym {
            if let Some(&s) = key_to_sym.get(&key) {
                return s;
            }
            let sym = Sym::new(PRIVATE_SYM_TAG | (next_priv & 0x3FFF_FFFF));
            next_priv += 1;
            key_to_sym.insert(key, sym);
            sym
        };

        let mut by_inst: HashMap<InstId, Vec<Sym>> = HashMap::new();
        for (fi, fd) in module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            let cid = links.func_class(fid).unwrap_or(fd.class_id);
            for &b in &fd.blocks {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    let (Op::LoadPrivate { slot, .. }
                    | Op::StorePrivate { slot, .. }
                    | Op::DefinePrivate { slot, .. }) = &inst.op
                    else {
                        continue;
                    };
                    let sites = lex_env.explicit_sites_at(iid);
                    let mut syms = Vec::new();
                    if sites.is_empty() {
                        syms.push(intern_priv((None, cid, *slot)));
                    } else {
                        for &s in sites {
                            let sym = intern_priv((Some(s), cid, *slot));
                            if !syms.contains(&sym) {
                                syms.push(sym);
                            }
                        }
                    }
                    by_inst.insert(iid, syms);
                }
            }
        }
        Self { by_inst }
    }

    pub(super) fn empty() -> Self {
        Self {
            by_inst: HashMap::new(),
        }
    }

    #[inline]
    pub(super) fn syms_at(&self, inst: InstId) -> &[Sym] {
        self.by_inst.get(&inst).map_or(&[], Vec::as_slice)
    }
}
