//! Unit tests for Rung-0 allocation-site keying, compact site/field sets, and concrete-singleton gating.

use super::*;
use crate::testutil::*;
use abcd_ir::{EdgeKind, Op};

#[test]
fn straight_line_alloc_is_single_precise() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let obj = alloc_object(&mut m, entry);
    let alias = emit(&mut m, entry, Op::Mov { src: obj });
    emit_void(&mut m, entry, Op::Return { value: None });

    let info = resolve_alloc_sites(&m, alias);
    assert_eq!(info.sites.len(), 1);
    assert!(info.is_single_precise());
    assert_eq!(update_kind(&info), UpdateKind::Strong);

    // The oracle seam's must-alias/points-to delegates were deleted
    // as dead surface; the same answers come from `resolve`:
    // must-alias = both sides single-precise with equal sites,
    // points-to = the resolved site set.
    let oracle = Rung0AliasOracle::new(&m);
    let (a, b) = (oracle.resolve(obj), oracle.resolve(alias));
    assert!(a.is_single_precise() && b.is_single_precise() && a.sites == b.sites);
    assert_eq!(oracle.resolve(alias).sites.len(), 1);
}

#[test]
fn phi_merge_is_weak() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let join = add_block(&mut m, f);

    let cond = load_number(&mut m, entry, 1.0);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond,
            true_dest: t,
            false_dest: e,
        },
    );
    let a = alloc_object(&mut m, t);
    emit_void(&mut m, t, Op::Branch { dest: join });
    let b = alloc_object(&mut m, e);
    emit_void(&mut m, e, Op::Branch { dest: join });
    link(&mut m, entry, t);
    link(&mut m, entry, e);
    link(&mut m, t, join);
    link(&mut m, e, join);
    let phi = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    abcd_ir::Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    a,
                ),
                (
                    abcd_ir::Edge {
                        from: e,
                        kind: EdgeKind::Normal,
                    },
                    b,
                ),
            ],
        },
    );
    emit_void(&mut m, join, Op::Return { value: None });

    let info = resolve_alloc_sites(&m, phi);
    assert_eq!(info.sites.len(), 2, "phi merges sites");
    assert!(info.has_phi);
    assert_eq!(update_kind(&info), UpdateKind::Weak);

    let oracle = Rung0AliasOracle::new(&m);
    // Not must-alias: the phi side is not single-precise.
    let (pa, pb) = (oracle.resolve(phi), oracle.resolve(a));
    assert!(!(pa.is_single_precise() && pb.is_single_precise() && pa.sites == pb.sites));
    assert_eq!(oracle.resolve(phi).sites.len(), 2);
}

#[test]
fn array_alloc_site_and_consts() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let arr = alloc_array(&mut m, entry);
    let undef = const_undefined(&mut m);
    emit_void(&mut m, entry, Op::Return { value: None });

    // An array allocation is a keyed site (T7).
    let info = resolve_alloc_sites(&m, arr);
    assert!(info.is_single_precise());
    assert_eq!(update_kind(&info), UpdateKind::Strong);

    // Constants contribute no site and no unknown — they are not heap
    // objects at all.
    let info = resolve_alloc_sites(&m, undef);
    assert!(info.sites.is_empty());
    assert!(!info.has_unknown && !info.has_phi);

    // Different sites of different kinds do not alias.
    let obj = alloc_object(&mut m, entry);
    let oracle = Rung0AliasOracle::new(&m);
    let (a, b) = (oracle.resolve(arr), oracle.resolve(obj));
    assert!(!(a.is_single_precise() && b.is_single_precise() && a.sites == b.sites));
}

#[test]
fn unknown_sources_are_weak_and_never_must_alias() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let p = add_param(&mut m, f, 1);
    let name = intern(&mut m, "x");
    let loaded = emit(&mut m, entry, Op::LoadProp { object: p, name });
    emit_void(&mut m, entry, Op::Return { value: None });

    let info = resolve_alloc_sites(&m, loaded);
    assert!(info.sites.is_empty());
    assert!(info.has_unknown);
    assert_eq!(update_kind(&info), UpdateKind::Weak);

    let oracle = Rung0AliasOracle::new(&m);
    // Not must-alias: an unknown-source value is not single-precise.
    let (a, b) = (oracle.resolve(loaded), oracle.resolve(loaded));
    assert!(!(a.is_single_precise() && b.is_single_precise() && a.sites == b.sites));
}

#[test]
fn access_path_cutoff_at_k() {
    let cap = 3usize;
    let s = Sym::new(7);
    let mut chain = FieldChain::new();
    for _ in 0..5 {
        chain = chain.pushed(FieldKey::Named(s), cap);
    }
    assert_eq!(chain.len(), cap, "chain is capped at k");

    // Two chains that differ ONLY below the cutoff collapse to the
    // same key (k-limiting merges them).
    let other = Sym::new(8);
    let mut a = FieldChain::new();
    let mut b = FieldChain::new();
    for _ in 0..cap {
        a = a.pushed(FieldKey::Named(s), cap);
        b = b.pushed(FieldKey::Named(s), cap);
    }
    a = a.pushed(FieldKey::Named(s), cap);
    b = b.pushed(FieldKey::Named(other), cap);
    assert_eq!(a, b, "beyond-k extensions collapse onto the prefix");
}

#[test]
fn may_alias_tri_state() {
    let f1 = FieldChain::new().pushed(FieldKey::Named(Sym::new(1)), DEFAULT_MAX_FIELD_CHAIN);
    let f2 = FieldChain::new().pushed(FieldKey::Named(Sym::new(2)), DEFAULT_MAX_FIELD_CHAIN);
    let s1 = AllocSiteSet::one(InstId::new(1));
    let s2 = AllocSiteSet::one(InstId::new(2));

    // The oracle seam's may-alias delegate was deleted as dead
    // surface; it was a pure forward to `key_may_alias`.
    let same = HeapRef {
        sites: s1.clone(),
        fields: f1.clone(),
    };
    assert_eq!(key_may_alias(&same, &same.clone()), Tribool::True);
    // Different named fields: never the same location.
    let other_field = HeapRef {
        sites: s1.clone(),
        fields: f2,
    };
    assert_eq!(key_may_alias(&same, &other_field), Tribool::False);
    // Same field, disjoint sites: different objects.
    let other_obj = HeapRef {
        sites: s2,
        fields: f1.clone(),
    };
    assert_eq!(key_may_alias(&same, &other_obj), Tribool::False);
    // Same field, unknown sites on one side: undecidable.
    let unknown = HeapRef {
        sites: AllocSiteSet::new(),
        fields: f1,
    };
    assert_eq!(key_may_alias(&same, &unknown), Tribool::Unknown);
}

#[test]
fn concrete_singleton_classifier_gates_loops_multi_call_helpers_and_escaped_closures() {
    let mut m = mk_module();

    // 1. `single_helper`: called ONCE from `func_main_0` outside any loop -> singleton!
    let single_helper = add_func_named(&mut m, "single_helper");
    let b_sh = entry_of(&m, single_helper);
    let obj_single_helper = alloc_object(&mut m, b_sh);
    let site_single_helper = m.blocks[b_sh.index()].insts[0];
    emit_void(
        &mut m,
        b_sh,
        Op::Return {
            value: Some(obj_single_helper),
        },
    );

    // 2. `multi_helper`: called TWICE from `func_main_0` -> NOT singleton!
    let multi_helper = add_func_named(&mut m, "multi_helper");
    let b_mh = entry_of(&m, multi_helper);
    let obj_multi_helper = alloc_object(&mut m, b_mh);
    let site_multi_helper = m.blocks[b_mh.index()].insts[0];
    emit_void(
        &mut m,
        b_mh,
        Op::Return {
            value: Some(obj_multi_helper),
        },
    );

    // 3. `escaped_cb`: stored onto an object -> NOT singleton!
    let escaped_cb = add_func_named(&mut m, "escaped_cb");
    let b_cb = entry_of(&m, escaped_cb);
    let obj_escaped = alloc_object(&mut m, b_cb);
    let site_escaped = m.blocks[b_cb.index()].insts[0];
    emit_void(
        &mut m,
        b_cb,
        Op::Return {
            value: Some(obj_escaped),
        },
    );

    // 4. `func_main_0`: top-level alloc, natural `while` loop alloc, and
    //    irreducible 2-entry loop (`ir1 <-> ir2`) alloc.
    let main_fn = add_func_named(&mut m, "func_main_0");
    let b_entry = entry_of(&m, main_fn);
    let b_while_head = add_block(&mut m, main_fn);
    let b_while_body = add_block(&mut m, main_fn);
    let b_ir1 = add_block(&mut m, main_fn);
    let b_ir2 = add_block(&mut m, main_fn);
    let b_exit = add_block(&mut m, main_fn);

    let obj_top = alloc_object(&mut m, b_entry);
    let site_top = m.blocks[b_entry.index()].insts[0];

    let sh_ref = load_method_ref(&mut m, b_entry, single_helper);
    let _ = emit(
        &mut m,
        b_entry,
        Op::Call {
            callee: sh_ref,
            this: None,
            args: Vec::new(),
            kind: abcd_ir::CallKind::Direct,
        },
    );
    let mh_ref = load_method_ref(&mut m, b_entry, multi_helper);
    for _ in 0..2 {
        let _ = emit(
            &mut m,
            b_entry,
            Op::Call {
                callee: mh_ref,
                this: None,
                args: Vec::new(),
                kind: abcd_ir::CallKind::Direct,
            },
        );
    }
    let df_cb = emit(
        &mut m,
        b_entry,
        Op::DefineFunc {
            body: escaped_cb,
            captures: Vec::new(),
            length: 0,
        },
    );
    let cl_cb = emit(&mut m, b_entry, Op::AllocClosure { func: df_cb });
    let s_fn = intern(&mut m, "fn");
    emit_void(
        &mut m,
        b_entry,
        Op::StoreProp {
            object: obj_top,
            name: s_fn,
            value: cl_cb,
        },
    );
    emit_void(&mut m, b_entry, Op::Branch { dest: b_while_head });
    link(&mut m, b_entry, b_while_head);

    let cond = load_number(&mut m, b_while_head, 1.0);
    emit_void(
        &mut m,
        b_while_head,
        Op::CondBranch {
            cond,
            true_dest: b_while_body,
            false_dest: b_ir1,
        },
    );
    link(&mut m, b_while_head, b_while_body);
    link(&mut m, b_while_head, b_ir1);

    let obj_while = alloc_object(&mut m, b_while_body);
    let site_while = m.blocks[b_while_body.index()].insts[0];
    emit_void(
        &mut m,
        b_while_body,
        Op::CondBranch {
            cond,
            true_dest: b_while_head,
            false_dest: b_ir2,
        },
    );
    link(&mut m, b_while_body, b_while_head);
    link(&mut m, b_while_body, b_ir2);

    // Irreducible cycle `b_ir1 <-> b_ir2` entered from both `b_while_head` and `b_while_body`.
    let _ = alloc_object(&mut m, b_ir1);
    let site_ir1 = m.blocks[b_ir1.index()].insts[0];
    emit_void(
        &mut m,
        b_ir1,
        Op::CondBranch {
            cond,
            true_dest: b_ir2,
            false_dest: b_exit,
        },
    );
    link(&mut m, b_ir1, b_ir2);
    link(&mut m, b_ir1, b_exit);

    emit_void(&mut m, b_ir2, Op::Branch { dest: b_ir1 });
    link(&mut m, b_ir2, b_ir1);

    let ret_iid = emit_void(&mut m, b_exit, Op::Return { value: None });

    let cls = SingletonSiteClassifier::from_module(&m);
    assert!(cls.is_single_execution_func(main_fn));
    assert!(cls.is_single_execution_func(single_helper));
    assert!(!cls.is_single_execution_func(multi_helper));
    assert!(!cls.is_single_execution_func(escaped_cb));

    assert!(!cls.is_loop_block(b_entry));
    assert!(cls.is_loop_block(b_while_head));
    assert!(cls.is_loop_block(b_while_body));
    assert!(cls.is_loop_block(b_ir1));
    assert!(cls.is_loop_block(b_ir2));
    assert!(!cls.is_loop_block(b_exit));

    assert!(cls.is_concrete_singleton_site(site_top));
    assert!(cls.is_concrete_singleton_site(site_single_helper));
    assert!(!cls.is_concrete_singleton_site(site_while));
    assert!(!cls.is_concrete_singleton_site(site_ir1));
    assert!(!cls.is_concrete_singleton_site(site_multi_helper));
    assert!(!cls.is_concrete_singleton_site(site_escaped));
    assert!(is_concrete_singleton_site(&m, site_top));
    assert!(!is_concrete_singleton_site(&m, site_while));

    let r0 = Rung0AliasOracle::new(&m);
    assert_eq!(r0.update_kind_of(obj_top), UpdateKind::Strong);
    assert_eq!(r0.update_kind_of(obj_single_helper), UpdateKind::Strong);
    assert_eq!(r0.update_kind_of(obj_while), UpdateKind::Weak);
    assert_eq!(r0.update_kind_of(obj_multi_helper), UpdateKind::Weak);
    assert_eq!(r0.update_kind_of(obj_escaped), UpdateKind::Weak);
    assert!(!r0.site_info_at(obj_top, ret_iid).has_phi);
    assert!(r0.site_info_at(obj_while, ret_iid).has_phi);
    assert!(r0.site_info_at(obj_multi_helper, ret_iid).has_phi);
}

#[test]
fn alloc_site_set_and_field_chain_inline_spill_boundaries_and_traits() {
    use std::collections::hash_map::DefaultHasher;

    fn hash_of<T: Hash>(v: &T) -> u64 {
        let mut h = DefaultHasher::new();
        v.hash(&mut h);
        h.finish()
    }

    // 1. `AllocSiteSet` across cardinalities `0..=8` (inline <= 4, spill > 4).
    let mut set = AllocSiteSet::new();
    assert!(set.is_empty());
    assert_eq!(set.len(), 0);
    assert_eq!(set.as_slice(), &[]);
    assert!(!set.contains(InstId::new(0)));

    // Insert out of order (`70, 10, 50, 30, 60, 20, 80, 40`) and verify sorted
    // `as_slice()`, `contains`, `iter`, `Clone`, `Ord`, and `Hash` at every step.
    let order = [70u32, 10, 50, 30, 60, 20, 80, 40];
    let mut reference: BTreeSet<InstId> = BTreeSet::new();
    for (step, &raw) in order.iter().enumerate() {
        let site = InstId::new(raw);
        assert!(set.insert(site));
        assert!(!set.insert(site), "duplicate insert must return false");
        reference.insert(site);

        let expected: Vec<InstId> = reference.iter().copied().collect();
        assert_eq!(set.len(), step + 1);
        assert_eq!(set.as_slice(), expected.as_slice());
        assert_eq!(set.iter().collect::<Vec<_>>(), expected);
        for &present in &expected {
            assert!(set.contains(present));
        }
        assert!(!set.contains(InstId::new(999)));

        let rebuilt: AllocSiteSet = expected.iter().copied().collect();
        assert_eq!(set, rebuilt);
        assert_eq!(hash_of(&set), hash_of(&rebuilt));
        assert_eq!(set.cmp(&rebuilt), Ordering::Equal);
    }

    // Verify `union_with` and `intersects` across inline + inline -> inline,
    // inline + inline -> spill, and spill + spill.
    let inline_a: AllocSiteSet = [InstId::new(2), InstId::new(6)].into_iter().collect();
    let inline_b: AllocSiteSet = [InstId::new(4), InstId::new(6)].into_iter().collect();
    assert!(inline_a.intersects(&inline_b));
    let mut u_small = inline_a.clone();
    u_small.union_with(&inline_b);
    assert_eq!(
        u_small.as_slice(),
        &[InstId::new(2), InstId::new(4), InstId::new(6)]
    );

    let inline_c: AllocSiteSet = [InstId::new(1), InstId::new(3), InstId::new(5)]
        .into_iter()
        .collect();
    let mut u_spill = inline_a.clone();
    u_spill.union_with(&inline_c);
    assert_eq!(
        u_spill.as_slice(),
        &[
            InstId::new(1),
            InstId::new(2),
            InstId::new(3),
            InstId::new(5),
            InstId::new(6)
        ]
    );
    assert!(!inline_a.intersects(&inline_c));

    // 2. `FieldChain` across lengths `0..=8` (inline <= 5, spill > 5 when cap = 8).
    let mut chain = FieldChain::new();
    assert!(chain.is_empty());
    let mut expected_keys = Vec::new();
    for i in 1..=8u32 {
        let k = FieldKey::Named(Sym::new(i));
        chain = chain.pushed(k, 8);
        expected_keys.push(k);
        assert_eq!(chain.len(), i as usize);
        assert_eq!(chain.elements(), expected_keys.as_slice());
        let cloned = chain.clone();
        assert_eq!(chain, cloned);
        assert_eq!(hash_of(&chain), hash_of(&cloned));
    }
    // Capped push at `cap = 8` leaves length at 8.
    let capped = chain.pushed(FieldKey::AnyIndex, 8);
    assert_eq!(capped, chain);
}

#[test]
fn decoy_user_harness_name_is_not_treated_as_singleton_root() {
    let mut m = mk_module();
    let main_fn = add_func_named(&mut m, "func_main_0");
    let b_main = entry_of(&m, main_fn);
    emit_void(&mut m, b_main, Op::Return { value: None });

    // Uncalled user function literally named `"__abcd_ohos_harness__"`:
    // with `harness_func == None`, it MUST NOT be treated as a single-exec root!
    let decoy = add_func_named(&mut m, crate::ohos_lifecycle::OHOS_HARNESS_FUNC);
    let b_decoy = entry_of(&m, decoy);
    let decoy_obj = alloc_object(&mut m, b_decoy);
    let decoy_site = m.blocks[b_decoy.index()].insts[0];
    emit_void(
        &mut m,
        b_decoy,
        Op::Return {
            value: Some(decoy_obj),
        },
    );

    let cls = SingletonSiteClassifier::from_module(&m);
    assert!(cls.is_single_execution_func(main_fn));
    assert!(
        !cls.is_single_execution_func(decoy),
        "decoy user function named __abcd_ohos_harness__ must not spoof single_exec_funcs"
    );
    assert!(!cls.is_concrete_singleton_site(decoy_site));
}
