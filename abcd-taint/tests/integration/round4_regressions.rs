//! Round 4 Sub-batch 2B regression suite (`R4-C1`, `R4-C2`, `R4-P2a`, `R4-H1`,
//! `R4-H3`, `R4-H4`, `R4-H5`, and `256 KiB` stack-size scaling).

use crate::common::*;
use abcd_ir::op::SuperKey;
use abcd_ir::{CallKind, Edge, EdgeKind, Modifiers, Module, Op, ValueId};
use abcd_taint::{Endpoint, SinkSpec, SourceSpec, Summary, TaintConfig, run_taint};

fn base_config() -> TaintConfig {
    TaintConfig {
        sources: vec![SourceSpec::FunctionParams {
            name: "func_main_0".to_owned(),
            params: Some(vec![1]),
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        builtin_summaries: true,
        ohos_lifecycle: false,
        ..TaintConfig::default()
    }
}

fn sink_call(m: &mut Module, b: abcd_ir::BlockId, arg: ValueId) -> abcd_ir::InstId {
    let print = try_get_global(m, b, "print");
    push_inst(
        m,
        b,
        Op::Call {
            callee: print,
            this: None,
            args: vec![arg],
            kind: CallKind::Dynamic,
        },
    )
}

fn add_static_func(
    m: &mut Module,
    name: &str,
    num_formals: usize,
) -> (abcd_ir::FuncId, Vec<ValueId>) {
    let fid = add_func_named(m, name);
    m.func_mut(fid).unwrap().modifiers = Modifiers::STATIC;
    let mut formals = Vec::with_capacity(num_formals);
    add_param(m, fid, 0);
    add_param(m, fid, 1);
    add_param(m, fid, 2);
    for i in 0..num_formals {
        formals.push(add_param(m, fid, (3 + i) as u16));
    }
    (fid, formals)
}

/// `R4-C1`: simultaneous multi-`Op::Phi` block entry mapping on a 3-phi header
/// (taint enters on the 3rd phi while phis 0 and 1 stay clean) and on a
/// phi-headed `catch` handler block.
#[test]
fn r4_c1_multi_phi_header_and_phi_headed_catch() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let secret = add_param(&mut m, f, 1);

    let left = add_block(&mut m, f);
    let right = add_block(&mut m, f);
    let header = add_block(&mut m, f);

    let cond = try_get_global(&mut m, entry, "COND");
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond,
            true_dest: left,
            false_dest: right,
        },
    );
    link(&mut m, entry, left);
    link(&mut m, entry, right);

    let l0 = load_string(&mut m, left, "c0");
    let l1 = load_string(&mut m, left, "c1");
    let l2 = secret;
    emit_void(&mut m, left, Op::Branch { dest: header });
    link(&mut m, left, header);

    let r0 = load_string(&mut m, right, "d0");
    let r1 = load_string(&mut m, right, "d1");
    let r2 = load_string(&mut m, right, "d2");
    emit_void(&mut m, right, Op::Branch { dest: header });
    link(&mut m, right, header);

    let e_left = Edge {
        from: left,
        kind: EdgeKind::Normal,
    };
    let e_right = Edge {
        from: right,
        kind: EdgeKind::Normal,
    };
    let phi0 = emit(
        &mut m,
        header,
        Op::Phi {
            entries: vec![(e_left, l0), (e_right, r0)],
        },
    );
    let phi1 = emit(
        &mut m,
        header,
        Op::Phi {
            entries: vec![(e_left, l1), (e_right, r1)],
        },
    );
    let phi2 = emit(
        &mut m,
        header,
        Op::Phi {
            entries: vec![(e_left, l2), (e_right, r2)],
        },
    );
    let call_p0 = sink_call(&mut m, header, phi0);
    let call_p1 = sink_call(&mut m, header, phi1);
    let call_p2 = sink_call(&mut m, header, phi2);

    // Phi-headed catch handler entered via exceptional edge from two protected blocks.
    let try_a = add_block(&mut m, f);
    let try_b = add_block(&mut m, f);
    let catch_hdr = add_block(&mut m, f);
    let exc = add_exception_param(&mut m, catch_hdr);

    emit_void(
        &mut m,
        header,
        Op::CondBranch {
            cond,
            true_dest: try_a,
            false_dest: try_b,
        },
    );
    link(&mut m, header, try_a);
    link(&mut m, header, try_b);

    let ca0 = load_string(&mut m, try_a, "clean_a");
    let benign_err = load_string(&mut m, try_a, "err");
    emit_void(&mut m, try_a, Op::Throw { value: benign_err });

    let cb0 = load_string(&mut m, try_b, "clean_b");
    let may_throw_fn = try_get_global(&mut m, try_b, "mayThrowExternal");
    push_inst(
        &mut m,
        try_b,
        Op::Call {
            callee: may_throw_fn,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
    );
    emit_void(&mut m, try_b, Op::Return { value: None });

    add_try(&mut m, f, vec![try_a, try_b], catch_hdr, exc);
    let ex_a = Edge {
        from: try_a,
        kind: EdgeKind::Exceptional,
    };
    let ex_b = Edge {
        from: try_b,
        kind: EdgeKind::Exceptional,
    };
    let catch_phi0 = emit(
        &mut m,
        catch_hdr,
        Op::Phi {
            entries: vec![(ex_a, ca0), (ex_b, cb0)],
        },
    );
    let catch_phi1 = emit(
        &mut m,
        catch_hdr,
        Op::Phi {
            entries: vec![(ex_a, cb0), (ex_b, secret)],
        },
    );
    let call_cp0 = sink_call(&mut m, catch_hdr, catch_phi0);
    let call_cp1 = sink_call(&mut m, catch_hdr, catch_phi1);
    emit_void(&mut m, catch_hdr, Op::Return { value: None });

    let report = run_taint(&m, &base_config());
    assert!(!report.hits.iter().any(|h| h.call == call_p0));
    assert!(!report.hits.iter().any(|h| h.call == call_p1));
    assert!(
        report.hits.iter().any(|h| h.call == call_p2),
        "3rd phi in header must receive taint: {:?}",
        report.hits
    );
    assert!(!report.hits.iter().any(|h| h.call == call_cp0));
    assert!(
        report.hits.iter().any(|h| h.call == call_cp1),
        "2nd phi in catch header must receive taint across call-to-return exceptional edge: {:?}",
        report.hits
    );
}

/// `R4-C2` & `R4-P2a`: zero `> 512`-function cliffs (exact hit parity between
/// `4`-function and `513`-function modules with `pta_root_sliced == true`),
/// `pta_step_budget: Some(1)` fallback cone, and `cond ? {} : ext` on Rung 0/1.
#[test]
fn r4_c2_and_p2a_zero_512_cliffs_budget_fallback_and_has_unknown_floor() {
    let build_bundle = |pad_to_513: bool| -> (Module, [abcd_ir::InstId; 4]) {
        let mut m = mk_module();

        // Dummy body for `http.request` so `call_has_body_callee` is true on a
        // resolved wrapper while `SinkSpec::Call` still matches `.request`.
        let (mock_req, _) = add_static_func(&mut m, "request", 2);
        {
            let b = entry_of(&m, mock_req);
            emit_void(&mut m, b, Op::Return { value: None });
        }

        // `sendReq(opts) { http.request(url, opts); }`
        let (send_req, sr_params) = add_static_func(&mut m, "sendReq", 1);
        let sink_req_call;
        {
            let b = entry_of(&m, send_req);
            let url = load_string(&mut m, b, "https://example.com");
            let req_fn = load_method_ref(&mut m, b, mock_req);
            sink_req_call = push_inst(
                &mut m,
                b,
                Op::Call {
                    callee: req_fn,
                    this: None,
                    args: vec![url, sr_params[0]],
                    kind: CallKind::Direct,
                },
            );
            emit_void(&mut m, b, Op::Return { value: None });
        }

        let f = add_func_named(&mut m, "func_main_0");
        let b = entry_of(&m, f);
        add_param(&mut m, f, 0);
        let secret = add_param(&mut m, f, 1);

        // (1) Multi-field chain (`cap = 5`, not clamped to 1 on >512 functions):
        // `o1.a.b` tainted, `o1.a.other` clean!
        let sym_a = intern(&mut m, "a");
        let sym_b = intern(&mut m, "b");
        let sym_other = intern(&mut m, "other");
        let inner = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: inner,
                name: sym_b,
                value: secret,
            },
        );
        let outer = alloc_object(&mut m, b);
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: outer,
                name: sym_a,
                value: inner,
            },
        );
        let ld_a = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: outer,
                name: sym_a,
            },
        );
        let ld_ab = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: ld_a,
                name: sym_b,
            },
        );
        let ld_a_other = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: ld_a,
                name: sym_other,
            },
        );
        let sink_ab = sink_call(&mut m, b, ld_ab);
        let sink_a_other = sink_call(&mut m, b, ld_a_other);

        // (2) `ext.k = secret; print(ext);` matches via `Local(ext).k` alongside `Heap(EMPTY).k`.
        let ext = try_get_global(&mut m, b, "EXT_OBJ");
        let sym_k = intern(&mut m, "k");
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: ext,
                name: sym_k,
                value: secret,
            },
        );
        let sink_ext = sink_call(&mut m, b, ext);

        // (3) `opts = {}; opts.extraData = secret; sendReq(opts);`
        let opts = alloc_object(&mut m, b);
        let sym_extra = intern(&mut m, "extraData");
        emit_void(
            &mut m,
            b,
            Op::StoreProp {
                object: opts,
                name: sym_extra,
                value: secret,
            },
        );
        let sr_fn = load_method_ref(&mut m, b, send_req);
        push_inst(
            &mut m,
            b,
            Op::Call {
                callee: sr_fn,
                this: None,
                args: vec![opts],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });

        if pad_to_513 {
            while m.functions.len() < 513 {
                let idx = m.functions.len();
                let df = add_func_named(&mut m, &format!("pad_fn_{idx}"));
                let db = entry_of(&m, df);
                emit_void(&mut m, db, Op::Return { value: None });
            }
        }
        (m, [sink_ab, sink_a_other, sink_ext, sink_req_call])
    };

    let mut cfg = base_config();
    cfg.sinks.push(SinkSpec::Call {
        name: "request".to_owned(),
    });

    let (m_small, [s_ab_1, s_other_1, s_ext_1, s_req_1]) = build_bundle(false);
    let (m_large, [s_ab_2, s_other_2, s_ext_2, s_req_2]) = build_bundle(true);
    assert_eq!(m_large.functions.len(), 513);

    let rep_small = run_taint(&m_small, &cfg);
    let rep_large = run_taint(&m_large, &cfg);
    assert!(!rep_small.pta_root_sliced);
    assert!(rep_large.pta_root_sliced);
    assert_eq!(
        rep_small.hits.len(),
        rep_large.hits.len(),
        "zero 512-function cliff: small={:?} vs large={:?}",
        rep_small.hits,
        rep_large.hits
    );
    for (s_ab, s_other, s_ext, s_req, rep) in [
        (s_ab_1, s_other_1, s_ext_1, s_req_1, &rep_small),
        (s_ab_2, s_other_2, s_ext_2, s_req_2, &rep_large),
    ] {
        assert!(rep.hits.iter().any(|h| h.call == s_ab));
        assert!(!rep.hits.iter().any(|h| h.call == s_other));
        assert!(rep.hits.iter().any(|h| h.call == s_ext));
        assert!(rep.hits.iter().any(|h| h.call == s_req));
    }

    // `pta_step_budget: Some(1)` degrades to Rung 1 and `unknown_deref_cone` keeps
    // interprocedural heap-property reads sound on 513-function bundles.
    let mut m_deg = mk_module();
    let (reader, r_params) = add_static_func(&mut m_deg, "reader", 1);
    let deg_sink;
    {
        let rb = entry_of(&m_deg, reader);
        let sym_k = intern(&mut m_deg, "k");
        let v = emit(
            &mut m_deg,
            rb,
            Op::LoadProp {
                object: r_params[0],
                name: sym_k,
            },
        );
        deg_sink = sink_call(&mut m_deg, rb, v);
        emit_void(&mut m_deg, rb, Op::Return { value: None });
    }
    let main_deg = add_func_named(&mut m_deg, "func_main_0");
    {
        let mb = entry_of(&m_deg, main_deg);
        add_param(&mut m_deg, main_deg, 0);
        let secret = add_param(&mut m_deg, main_deg, 1);
        let obj = alloc_object(&mut m_deg, mb);
        let sym_k = intern(&mut m_deg, "k");
        emit_void(
            &mut m_deg,
            mb,
            Op::StoreProp {
                object: obj,
                name: sym_k,
                value: secret,
            },
        );
        let r_fn = load_method_ref(&mut m_deg, mb, reader);
        push_inst(
            &mut m_deg,
            mb,
            Op::Call {
                callee: r_fn,
                this: None,
                args: vec![obj],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m_deg, mb, Op::Return { value: None });
    }
    while m_deg.functions.len() < 513 {
        let idx = m_deg.functions.len();
        let df = add_func_named(&mut m_deg, &format!("deg_pad_{idx}"));
        let db = entry_of(&m_deg, df);
        emit_void(&mut m_deg, db, Op::Return { value: None });
    }
    let cfg_budget = TaintConfig {
        pta_step_budget: Some(1),
        ..base_config()
    };
    let rep_deg = run_taint(&m_deg, &cfg_budget);
    assert_eq!(rep_deg.alias_rung_used, 1);
    assert!(!rep_deg.pta_root_sliced);
    assert!(rep_deg.hits.iter().any(|h| h.call == deg_sink));

    // `R4-P2a`: `cond ? {} : ext` on Rung 0 and Rung 1 (`sites` non-empty AND `has_unknown == true`).
    let mut m_phi = mk_module();
    let f_phi = add_func_named(&mut m_phi, "func_main_0");
    let b0 = entry_of(&m_phi, f_phi);
    add_param(&mut m_phi, f_phi, 0);
    let secret = add_param(&mut m_phi, f_phi, 1);
    let b_true = add_block(&mut m_phi, f_phi);
    let b_false = add_block(&mut m_phi, f_phi);
    let b_join = add_block(&mut m_phi, f_phi);

    let tainted_obj = alloc_object(&mut m_phi, b0);
    let sym_k = intern(&mut m_phi, "k");
    emit_void(
        &mut m_phi,
        b0,
        Op::StoreProp {
            object: tainted_obj,
            name: sym_k,
            value: secret,
        },
    );
    let cond = try_get_global(&mut m_phi, b0, "COND");
    emit_void(
        &mut m_phi,
        b0,
        Op::CondBranch {
            cond,
            true_dest: b_true,
            false_dest: b_false,
        },
    );
    link(&mut m_phi, b0, b_true);
    link(&mut m_phi, b0, b_false);

    let clean_obj = alloc_object(&mut m_phi, b_true);
    emit_void(&mut m_phi, b_true, Op::Branch { dest: b_join });
    link(&mut m_phi, b_true, b_join);

    let ext_alias = try_get_global(&mut m_phi, b_false, "MAY_HOLD_TAINTED_OBJ");
    emit_void(&mut m_phi, b_false, Op::Branch { dest: b_join });
    link(&mut m_phi, b_false, b_join);

    let merged = emit(
        &mut m_phi,
        b_join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b_true,
                        kind: EdgeKind::Normal,
                    },
                    clean_obj,
                ),
                (
                    Edge {
                        from: b_false,
                        kind: EdgeKind::Normal,
                    },
                    ext_alias,
                ),
            ],
        },
    );
    let val = emit(
        &mut m_phi,
        b_join,
        Op::LoadProp {
            object: merged,
            name: sym_k,
        },
    );
    let phi_sink = sink_call(&mut m_phi, b_join, val);
    emit_void(&mut m_phi, b_join, Op::Return { value: None });

    for rung in [0u8, 1u8] {
        let rep = run_taint(
            &m_phi,
            &TaintConfig {
                alias_rung: rung,
                ..base_config()
            },
        );
        assert!(
            rep.hits.iter().any(|h| h.call == phi_sink),
            "Rung {rung} must honor has_unknown floor on `cond ? {{}} : ext`: {:?}",
            rep.hits
        );
    }
}

/// `R4-H1`: `a[0] = SECRET; a[1] = clean; print(a[0]);` — `AnyIndex` stores
/// never strong-kill prior element taints.
#[test]
fn r4_h1_indexed_store_does_not_strong_kill_sibling_element() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let secret = add_param(&mut m, f, 1);

    let arr = alloc_array(&mut m, b);
    let idx0 = load_number(&mut m, b, 0.0);
    let idx1 = load_number(&mut m, b, 1.0);
    let clean = load_string(&mut m, b, "clean");
    emit_void(
        &mut m,
        b,
        Op::StorePropIdx {
            object: arr,
            index: idx0,
            value: secret,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::StorePropIdx {
            object: arr,
            index: idx1,
            value: clean,
        },
    );
    let elem0 = emit(
        &mut m,
        b,
        Op::LoadPropIdx {
            object: arr,
            index: idx0,
        },
    );
    let hit_call = sink_call(&mut m, b, elem0);
    emit_void(&mut m, b, Op::Return { value: None });

    for rung in [0u8, 1u8, 2u8] {
        let rep = run_taint(
            &m,
            &TaintConfig {
                alias_rung: rung,
                ..base_config()
            },
        );
        assert!(
            rep.hits.iter().any(|h| h.call == hit_call),
            "a[1] = clean must not kill a[0] on rung {rung}: {:?}",
            rep.hits
        );
    }
}

/// `R4-H3`:
/// 1. `Number(secret); print(secret);` retains scalar `secret` across `exclusive` builtin;
/// 2. `noop(ext); print(ext); print(ext.k);` preserves `Local(ext).[k]` across resolved body calls;
/// 3. `!resolution_complete` on a `BodyStep` call retains caller facts and runs `native_identity`;
/// 4. user `function Number(x)` overrides builtin `Number` summary, while user `extra_summaries`
///    overrides `BodyStep`.
#[test]
fn r4_h3_exclusive_scalar_body_field_writeback_incomplete_edge_and_user_number() {
    // (1) + (2) + (3)
    let mut m = mk_module();
    let (noop, _) = add_static_func(&mut m, "noop", 1);
    {
        let b = entry_of(&m, noop);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let secret = add_param(&mut m, f, 1);

    // (1) `Number(secret); print(secret);`
    let num_fn = try_get_global(&mut m, entry, "Number");
    let _coerced = emit(
        &mut m,
        entry,
        Op::Call {
            callee: num_fn,
            this: None,
            args: vec![secret],
            kind: CallKind::Dynamic,
        },
    );
    let sink_after_number = sink_call(&mut m, entry, secret);

    // (2) `ext.k = secret; noop(ext); print(ext); print(ext.k);`
    let ext = try_get_global(&mut m, entry, "ext");
    let sym_k = intern(&mut m, "k");
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: ext,
            name: sym_k,
            value: secret,
        },
    );
    let noop_ref = load_method_ref(&mut m, entry, noop);
    push_inst(
        &mut m,
        entry,
        Op::Call {
            callee: noop_ref,
            this: None,
            args: vec![ext],
            kind: CallKind::Direct,
        },
    );
    let sink_ext_whole = sink_call(&mut m, entry, ext);
    let ext_k = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: ext,
            name: sym_k,
        },
    );
    let sink_ext_field = sink_call(&mut m, entry, ext_k);

    // (3) `!resolution_complete`: `cond ? noop : unknownExternal`
    let b_left = add_block(&mut m, f);
    let b_right = add_block(&mut m, f);
    let b_merge = add_block(&mut m, f);
    let cond = try_get_global(&mut m, entry, "COND");
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond,
            true_dest: b_left,
            false_dest: b_right,
        },
    );
    link(&mut m, entry, b_left);
    link(&mut m, entry, b_right);

    let known_callee = load_method_ref(&mut m, b_left, noop);
    emit_void(&mut m, b_left, Op::Branch { dest: b_merge });
    link(&mut m, b_left, b_merge);

    let unknown_callee = try_get_global(&mut m, b_right, "unknownNative");
    emit_void(&mut m, b_right, Op::Branch { dest: b_merge });
    link(&mut m, b_right, b_merge);

    let dyn_callee = emit(
        &mut m,
        b_merge,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b_left,
                        kind: EdgeKind::Normal,
                    },
                    known_callee,
                ),
                (
                    Edge {
                        from: b_right,
                        kind: EdgeKind::Normal,
                    },
                    unknown_callee,
                ),
            ],
        },
    );
    let incomp_res = emit(
        &mut m,
        b_merge,
        Op::Call {
            callee: dyn_callee,
            this: None,
            args: vec![secret],
            kind: CallKind::Dynamic,
        },
    );
    let sink_incomp = sink_call(&mut m, b_merge, incomp_res);
    emit_void(&mut m, b_merge, Op::Return { value: None });

    let rep = run_taint(&m, &base_config());
    assert!(rep.hits.iter().any(|h| h.call == sink_after_number));
    assert!(rep.hits.iter().any(|h| h.call == sink_ext_whole));
    assert!(rep.hits.iter().any(|h| h.call == sink_ext_field));
    assert!(rep.hits.iter().any(|h| h.call == sink_incomp));

    // (4) User `function Number(x) { return "clean"; }` beats builtin `Number` summary,
    // while user `extra_summaries` for `"Number"` still overrides `BodyStep`.
    let mut m_num = mk_module();
    let (user_num, _) = add_static_func(&mut m_num, "Number", 1);
    {
        let b = entry_of(&m_num, user_num);
        let clean = load_string(&mut m_num, b, "sanitized");
        emit_void(&mut m_num, b, Op::Return { value: Some(clean) });
    }
    let main_num = add_func_named(&mut m_num, "func_main_0");
    let sink_num;
    {
        let b = entry_of(&m_num, main_num);
        add_param(&mut m_num, main_num, 0);
        let secret = add_param(&mut m_num, main_num, 1);
        let callee = load_method_ref(&mut m_num, b, user_num);
        let res = emit(
            &mut m_num,
            b,
            Op::Call {
                callee,
                this: None,
                args: vec![secret],
                kind: CallKind::Direct,
            },
        );
        sink_num = sink_call(&mut m_num, b, res);
        emit_void(&mut m_num, b, Op::Return { value: None });
    }
    let rep_builtin = run_taint(&m_num, &base_config());
    assert!(
        rep_builtin.hits.is_empty(),
        "user `function Number(x)` body must beat preloaded builtin summary: {:?}",
        rep_builtin.hits
    );
    assert_eq!(rep_builtin.stats.sites_body_step, 1);
    assert!(!rep_builtin.summary_misses.contains_key("Number"));

    let mut cfg_override = base_config();
    cfg_override.extra_summaries.push((
        "Number".to_owned(),
        Some(1),
        Summary::new("user override: param0 -> return")
            .flow(Endpoint::Param(0), Endpoint::Return)
            .exclusive(),
    ));
    let rep_user_sum = run_taint(&m_num, &cfg_override);
    assert!(rep_user_sum.hits.iter().any(|h| h.call == sink_num));
    assert_eq!(rep_user_sum.stats.sites_body_step, 0);
}

/// `R4-H4`:
/// 1. normal and summary calls inside a `catch` block propagate return values;
/// 2. 3-frame uncaught `throw` propagates via `call_uncaught_exit_flow` into caller `catch`;
/// 3. locally catch-all-caught `throw` inside a callee does NOT leak to caller `catch`.
#[test]
fn r4_h4_catch_block_calls_and_multiframe_uncaught_throw() {
    let mut m = mk_module();

    let (id_fn, id_params) = add_static_func(&mut m, "idFn", 1);
    {
        let b = entry_of(&m, id_fn);
        emit_void(
            &mut m,
            b,
            Op::Return {
                value: Some(id_params[0]),
            },
        );
    }

    // 3-frame uncaught throw: `leaf` -> `mid1` -> `mid2`.
    let (leaf, leaf_params) = add_static_func(&mut m, "leafThrow", 1);
    {
        let b = entry_of(&m, leaf);
        emit_void(
            &mut m,
            b,
            Op::Throw {
                value: leaf_params[0],
            },
        );
    }
    let (mid1, mid1_params) = add_static_func(&mut m, "mid1", 1);
    {
        let b = entry_of(&m, mid1);
        let lv = load_method_ref(&mut m, b, leaf);
        push_inst(
            &mut m,
            b,
            Op::Call {
                callee: lv,
                this: None,
                args: vec![mid1_params[0]],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let (mid2, mid2_params) = add_static_func(&mut m, "mid2", 1);
    {
        let b = entry_of(&m, mid2);
        let m1v = load_method_ref(&mut m, b, mid1);
        push_inst(
            &mut m,
            b,
            Op::Call {
                callee: m1v,
                this: None,
                args: vec![mid2_params[0]],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Locally caught throw inside `swallow(x)`: must NOT escape to caller catch!
    let (swallow, sw_params) = add_static_func(&mut m, "swallow", 1);
    {
        let b_try = entry_of(&m, swallow);
        let b_catch = add_block(&mut m, swallow);
        let inner_exc = add_exception_param(&mut m, b_catch);
        emit_void(
            &mut m,
            b_try,
            Op::Throw {
                value: sw_params[0],
            },
        );
        add_try(&mut m, swallow, vec![b_try], b_catch, inner_exc);
        emit_void(&mut m, b_catch, Op::Return { value: None });
    }

    let f = add_func_named(&mut m, "func_main_0");
    let b_try1 = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let secret = add_param(&mut m, f, 1);

    let b_catch1 = add_block(&mut m, f);
    let exc1 = add_exception_param(&mut m, b_catch1);
    let b_try2 = add_block(&mut m, f);
    let b_catch2 = add_block(&mut m, f);
    let exc2 = add_exception_param(&mut m, b_catch2);

    // Try 1: 3-frame uncaught throw lands on `exc1`, AND calls inside `b_catch1` return taint!
    let m2v = load_method_ref(&mut m, b_try1, mid2);
    push_inst(
        &mut m,
        b_try1,
        Op::Call {
            callee: m2v,
            this: None,
            args: vec![secret],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, b_try1, Op::Branch { dest: b_try2 });
    link(&mut m, b_try1, b_try2);
    add_try(&mut m, f, vec![b_try1], b_catch1, exc1);

    let sink_multiframe_exc = sink_call(&mut m, b_catch1, exc1);
    let id_v = load_method_ref(&mut m, b_catch1, id_fn);
    let body_ret = emit(
        &mut m,
        b_catch1,
        Op::Call {
            callee: id_v,
            this: None,
            args: vec![secret],
            kind: CallKind::Direct,
        },
    );
    let sink_catch_body_call = sink_call(&mut m, b_catch1, body_ret);
    let str_fn = try_get_global(&mut m, b_catch1, "String");
    let sum_ret = emit(
        &mut m,
        b_catch1,
        Op::Call {
            callee: str_fn,
            this: None,
            args: vec![secret],
            kind: CallKind::Dynamic,
        },
    );
    let sink_catch_sum_call = sink_call(&mut m, b_catch1, sum_ret);
    emit_void(&mut m, b_catch1, Op::Branch { dest: b_try2 });
    link(&mut m, b_catch1, b_try2);

    // Try 2: `swallow(secret)` catches its own throw; `exc2` must stay clean!
    let sw_v = load_method_ref(&mut m, b_try2, swallow);
    push_inst(
        &mut m,
        b_try2,
        Op::Call {
            callee: sw_v,
            this: None,
            args: vec![secret],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, b_try2, Op::Return { value: None });
    add_try(&mut m, f, vec![b_try2], b_catch2, exc2);

    let sink_swallowed = sink_call(&mut m, b_catch2, exc2);
    emit_void(&mut m, b_catch2, Op::Return { value: None });

    let rep = run_taint(&m, &base_config());
    assert!(rep.hits.iter().any(|h| h.call == sink_multiframe_exc));
    assert!(rep.hits.iter().any(|h| h.call == sink_catch_body_call));
    assert!(rep.hits.iter().any(|h| h.call == sink_catch_sum_call));
    assert!(
        !rep.hits.iter().any(|h| h.call == sink_swallowed),
        "locally caught throw must not leak to outer catch: {:?}",
        rep.hits
    );
}

/// `R4-H5`: `ArraySpread`, `CopyDataProps`, `CreateObjectWithExcludedKeys` (across
/// Rungs 0/1/2), `CallKind::Apply`, `CallKind::SuperForwardAllArgs`,
/// `CopyRestArgs` (including excess caller args) & `GetUnmappedArgs`,
/// `StoreSuper`/`LoadSuper`, and `LoadGlobalObject`.
#[test]
fn r4_h5_missing_ops_and_call_kinds() {
    let mut m = mk_module();

    // `applyTarget(a) { print(a); }`
    let (apply_target, at_params) = add_static_func(&mut m, "applyTarget", 1);
    let sink_apply;
    {
        let b = entry_of(&m, apply_target);
        sink_apply = sink_call(&mut m, b, at_params[0]);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // `variadic(first, ...rest)` — `fd.params` only declares `first` (`len = 4`, `formal_base = 3`),
    // while caller passes 2 args (`args[1]` is an excess argument at index 1 >= `start_index: 1`)!
    let (variadic_fn, _var_params) = add_static_func(&mut m, "variadic", 1);
    let sink_rest;
    {
        let b = entry_of(&m, variadic_fn);
        let rest_arr = emit(&mut m, b, Op::CopyRestArgs { start_index: 1 });
        let idx0 = load_number(&mut m, b, 0.0);
        let r0 = emit(
            &mut m,
            b,
            Op::LoadPropIdx {
                object: rest_arr,
                index: idx0,
            },
        );
        sink_rest = sink_call(&mut m, b, r0);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // `unmappedFn()` — 0 declared formals (`fd.params.len() == 3`), reads `GetUnmappedArgs`!
    let (unmapped_fn, _) = add_static_func(&mut m, "unmappedFn", 0);
    let sink_unmapped;
    {
        let b = entry_of(&m, unmapped_fn);
        let args_obj = emit(&mut m, b, Op::GetUnmappedArgs);
        let idx0 = load_number(&mut m, b, 0.0);
        let a0 = emit(
            &mut m,
            b,
            Op::LoadPropIdx {
                object: args_obj,
                index: idx0,
            },
        );
        sink_unmapped = sink_call(&mut m, b, a0);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // `baseCtor` + `derivedCtor` forwarding via `SuperForwardAllArgs`.
    let (base_ctor, base_params) = add_static_func(&mut m, "baseCtor", 1);
    let sink_super_fwd;
    {
        let b = entry_of(&m, base_ctor);
        sink_super_fwd = sink_call(&mut m, b, base_params[0]);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let derived_ctor = add_func_named(&mut m, "derivedCtor");
    m.func_mut(derived_ctor).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, derived_ctor);
        add_param(&mut m, derived_ctor, 0);
        add_param(&mut m, derived_ctor, 1);
        let d_this = add_param(&mut m, derived_ctor, 2);
        add_param(&mut m, derived_ctor, 3);
        let bc = load_method_ref(&mut m, b, base_ctor);
        push_inst(
            &mut m,
            b,
            Op::Call {
                callee: bc,
                this: None,
                args: vec![d_this],
                kind: CallKind::SuperForwardAllArgs,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    // Helper reading `LoadGlobalObject` source (`compute_zero_needed` + `Fact::Zero`).
    let (glob_reader, _) = add_static_func(&mut m, "globReader", 0);
    let sink_glob_src;
    {
        let b = entry_of(&m, glob_reader);
        let gobj = emit(&mut m, b, Op::LoadGlobalObject);
        let gobj_mov = emit(&mut m, b, Op::Mov { src: gobj });
        let sym_hs = intern(&mut m, "HOST_SECRET");
        let hs = emit(
            &mut m,
            b,
            Op::LoadProp {
                object: gobj_mov,
                name: sym_hs,
            },
        );
        sink_glob_src = sink_call(&mut m, b, hs);
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let f = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, f);
    let this_param = add_param(&mut m, f, 0);
    let secret = add_param(&mut m, f, 1);
    let clean = load_string(&mut m, b, "clean");
    let idx0 = load_number(&mut m, b, 0.0);

    // (1) `ArraySpread`: taints `dst[0]`, NOT `inst.result`!
    let src_arr = alloc_array(&mut m, b);
    emit_void(
        &mut m,
        b,
        Op::StorePropIdx {
            object: src_arr,
            index: idx0,
            value: secret,
        },
    );
    let dst_arr = alloc_array(&mut m, b);
    let new_idx = emit(
        &mut m,
        b,
        Op::ArraySpread {
            dst: dst_arr,
            index: idx0,
            src: src_arr,
        },
    );
    let spread_elem = emit(
        &mut m,
        b,
        Op::LoadPropIdx {
            object: dst_arr,
            index: idx0,
        },
    );
    let sink_spread_elem = sink_call(&mut m, b, spread_elem);
    let sink_spread_idx = sink_call(&mut m, b, new_idx);

    // (2) `CopyDataProps` from heap-tainted `src_obj`.
    let sym_k = intern(&mut m, "k");
    let sym_keep = intern(&mut m, "keep");
    let src_obj = alloc_object(&mut m, b);
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: src_obj,
            name: sym_k,
            value: secret,
        },
    );
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: src_obj,
            name: sym_keep,
            value: secret,
        },
    );
    let copy_dst = alloc_object(&mut m, b);
    emit_void(
        &mut m,
        b,
        Op::CopyDataProps {
            dst: copy_dst,
            src: src_obj,
        },
    );
    let copied_k = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: copy_dst,
            name: sym_k,
        },
    );
    let sink_copied_k = sink_call(&mut m, b, copied_k);

    // (3) `CreateObjectWithExcludedKeys`: `rest.k` excluded (clean on Rungs 0/1/2), `rest.keep` tainted!
    let key_k_str = load_string(&mut m, b, "k");
    let rest_obj = emit(
        &mut m,
        b,
        Op::CreateObjectWithExcludedKeys {
            obj: src_obj,
            keys: vec![key_k_str],
        },
    );
    let rest_excluded = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: rest_obj,
            name: sym_k,
        },
    );
    let rest_kept = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: rest_obj,
            name: sym_keep,
        },
    );
    let sink_rest_excluded = sink_call(&mut m, b, rest_excluded);
    let sink_rest_kept = sink_call(&mut m, b, rest_kept);

    // (4) `CallKind::Apply` over heap-tainted `src_arr`.
    let at_ref = load_method_ref(&mut m, b, apply_target);
    push_inst(
        &mut m,
        b,
        Op::Call {
            callee: at_ref,
            this: None,
            args: vec![src_arr],
            kind: CallKind::Apply,
        },
    );

    // (5) `SuperForwardAllArgs` via `derivedCtor(secret)`.
    let dc_ref = load_method_ref(&mut m, b, derived_ctor);
    push_inst(
        &mut m,
        b,
        Op::Call {
            callee: dc_ref,
            this: Some(this_param),
            args: vec![secret],
            kind: CallKind::Direct,
        },
    );

    // (6) `CopyRestArgs` excess arg + `GetUnmappedArgs` excess arg.
    let var_ref = load_method_ref(&mut m, b, variadic_fn);
    push_inst(
        &mut m,
        b,
        Op::Call {
            callee: var_ref,
            this: None,
            args: vec![clean, secret],
            kind: CallKind::Direct,
        },
    );
    let unm_ref = load_method_ref(&mut m, b, unmapped_fn);
    push_inst(
        &mut m,
        b,
        Op::Call {
            callee: unm_ref,
            this: None,
            args: vec![secret],
            kind: CallKind::Direct,
        },
    );

    // (7) `StoreSuper` / `LoadSuper`.
    let super_recv = alloc_object(&mut m, b);
    let sym_sup = intern(&mut m, "supProp");
    let sym_sup_clean = intern(&mut m, "supClean");
    emit_void(
        &mut m,
        b,
        Op::StoreSuper {
            key: SuperKey::Name(sym_sup),
            this_value: super_recv,
            value: secret,
        },
    );
    let sup_hit_val = emit(
        &mut m,
        b,
        Op::LoadSuper {
            key: SuperKey::Name(sym_sup),
            this_value: super_recv,
        },
    );
    let sup_clean_val = emit(
        &mut m,
        b,
        Op::LoadSuper {
            key: SuperKey::Name(sym_sup_clean),
            this_value: super_recv,
        },
    );
    let sink_super_prop = sink_call(&mut m, b, sup_hit_val);
    let sink_super_clean = sink_call(&mut m, b, sup_clean_val);

    // (8) `LoadGlobalObject` <-> `TryGetGlobal` / `StoreGlobal`.
    let gobj = emit(&mut m, b, Op::LoadGlobalObject);
    let sym_g1 = intern(&mut m, "G_FROM_OBJ");
    let sym_g2 = intern(&mut m, "G_FROM_STORE");
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: gobj,
            name: sym_g1,
            value: secret,
        },
    );
    let g1_val = try_get_global(&mut m, b, "G_FROM_OBJ");
    let sink_g1 = sink_call(&mut m, b, g1_val);

    emit_void(
        &mut m,
        b,
        Op::StoreGlobal {
            name: sym_g2,
            value: secret,
        },
    );
    let g2_val = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: gobj,
            name: sym_g2,
        },
    );
    let sink_g2 = sink_call(&mut m, b, g2_val);

    let gr_ref = load_method_ref(&mut m, b, glob_reader);
    push_inst(
        &mut m,
        b,
        Op::Call {
            callee: gr_ref,
            this: None,
            args: vec![],
            kind: CallKind::Direct,
        },
    );
    emit_void(&mut m, b, Op::Return { value: None });

    let mut cfg = base_config();
    cfg.sources.push(SourceSpec::GlobalLoad {
        name: "HOST_SECRET".to_owned(),
    });

    for rung in [0u8, 1u8, 2u8] {
        let rep = run_taint(
            &m,
            &TaintConfig {
                alias_rung: rung,
                ..cfg.clone()
            },
        );
        assert!(
            rep.hits.iter().any(|h| h.call == sink_spread_elem),
            "rung {rung}"
        );
        assert!(
            !rep.hits.iter().any(|h| h.call == sink_spread_idx),
            "rung {rung}"
        );
        assert!(
            rep.hits.iter().any(|h| h.call == sink_copied_k),
            "rung {rung}"
        );
        assert!(
            !rep.hits.iter().any(|h| h.call == sink_rest_excluded),
            "excluded rest key must not fire on rung {rung}: {:?}",
            rep.hits
        );
        assert!(
            rep.hits.iter().any(|h| h.call == sink_rest_kept),
            "rung {rung}"
        );
        assert!(rep.hits.iter().any(|h| h.call == sink_apply), "rung {rung}");
        assert!(
            rep.hits.iter().any(|h| h.call == sink_super_fwd),
            "rung {rung}"
        );
        assert!(rep.hits.iter().any(|h| h.call == sink_rest), "rung {rung}");
        assert!(
            rep.hits.iter().any(|h| h.call == sink_unmapped),
            "rung {rung}"
        );
        assert!(
            rep.hits.iter().any(|h| h.call == sink_super_prop),
            "rung {rung}"
        );
        assert!(
            !rep.hits.iter().any(|h| h.call == sink_super_clean),
            "rung {rung}"
        );
        assert!(rep.hits.iter().any(|h| h.call == sink_g1), "rung {rung}");
        assert!(rep.hits.iter().any(|h| h.call == sink_g2), "rung {rung}");
        assert!(
            rep.hits.iter().any(|h| h.call == sink_glob_src),
            "rung {rung}"
        );
    }
}

/// Mandatory `256 KiB` call-stack budget regression: deep CFG/Phi chains,
/// long `Mov` def chains, and multi-frame uncaught-exception call chains run
/// without stack overflow inside a `256 KiB`-stack worker thread.
#[test]
fn round4_256kib_stack_scaling() {
    let handle = std::thread::Builder::new()
        .name("taint-256kib".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut m = mk_module();

            // 64-frame uncaught-throw chain (`frame_0` throws -> ... -> `frame_63`).
            let mut prev_fn = None;
            for depth in 0..64 {
                let (fid, params) = add_static_func(&mut m, &format!("frame_{depth}"), 1);
                let b = entry_of(&m, fid);
                if let Some(callee_fid) = prev_fn {
                    let cv = load_method_ref(&mut m, b, callee_fid);
                    push_inst(
                        &mut m,
                        b,
                        Op::Call {
                            callee: cv,
                            this: None,
                            args: vec![params[0]],
                            kind: CallKind::Direct,
                        },
                    );
                    emit_void(&mut m, b, Op::Return { value: None });
                } else {
                    emit_void(&mut m, b, Op::Throw { value: params[0] });
                }
                prev_fn = Some(fid);
            }
            let top_thrower = prev_fn.unwrap();

            let f = add_func_named(&mut m, "func_main_0");
            let entry = entry_of(&m, f);
            add_param(&mut m, f, 0);
            let mut cur = add_param(&mut m, f, 1);

            // 300-hop `Mov` chain + 200-block `Phi` chain.
            for _ in 0..300 {
                cur = emit(&mut m, entry, Op::Mov { src: cur });
            }
            let mut prev_b = entry;
            for _ in 0..200 {
                let next_b = add_block(&mut m, f);
                emit_void(&mut m, prev_b, Op::Branch { dest: next_b });
                link(&mut m, prev_b, next_b);
                cur = emit(
                    &mut m,
                    next_b,
                    Op::Phi {
                        entries: vec![(
                            Edge {
                                from: prev_b,
                                kind: EdgeKind::Normal,
                            },
                            cur,
                        )],
                    },
                );
                prev_b = next_b;
            }

            let catch_b = add_block(&mut m, f);
            let exc = add_exception_param(&mut m, catch_b);
            let tv = load_method_ref(&mut m, prev_b, top_thrower);
            push_inst(
                &mut m,
                prev_b,
                Op::Call {
                    callee: tv,
                    this: None,
                    args: vec![cur],
                    kind: CallKind::Direct,
                },
            );
            emit_void(&mut m, prev_b, Op::Return { value: None });
            add_try(&mut m, f, vec![prev_b], catch_b, exc);

            let hit = sink_call(&mut m, catch_b, exc);
            emit_void(&mut m, catch_b, Op::Return { value: None });

            let rep = run_taint(&m, &base_config());
            assert_eq!(rep.hits.len(), 1);
            assert_eq!(rep.hits[0].call, hit);
        })
        .expect("spawn 256 KiB thread");
    handle
        .join()
        .expect("256 KiB thread completed without stack overflow");
}
