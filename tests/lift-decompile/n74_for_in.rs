//! N74-W1: the for-in iterator-stall regression (test262 dream-gate
//! class `decompile-bug-for-in-iterator-stalls`, 85 rows).
//!
//! The bug: es2abc merges the for-in ITERATOR register through the loop
//! body's branch joins, so out-of-SSA recovery leaves a redundant copy
//! phi inside the body (`v335 = phi(v325, v325)` — every incoming value
//! is the iterator temp). The for-in fold's internal-temp use check
//! (`rebuild_loop_body`) conservatively rejected those loops; the
//! fallback emission rendered `NextPropName` as a no-op plumbing
//! expression and the loop back-edge as a self-assign (`v325 = v325`),
//! so the decompiled loop never advanced the iterator → infinite loop
//! (VM timeout). The fold now eliminates iterator-copy phis before the
//! use check: the iterator is a stateful, loop-invariant object, so any
//! phi whose EVERY incoming value is the iterator temp (transitively)
//! is an identity copy — substituted away, its plumbing stripped.
//!
//! These rows are corpus-fixture tests (`#[ignore]`d like
//! `golden_yield_star.rs`); run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-decompile --release -- --ignored --nocapture n74_for_in
//! ```

use crate::common;

use abcd_decompile::emit::{decompile_module, EmitOptions};

/// Decompile one corpus fixture (twice — determinism is part of the
/// contract) and return the text.
fn decompile(abc: &str) -> String {
    let root = common::corpus_root();
    let data = std::fs::read(root.join(abc)).expect("read fixture");
    let file = abcd_file::decode(&data).expect("decode fixture");
    let module = abcd_lift::lift_file(&file).expect("lift fixture");
    let opts = EmitOptions {
        call_entry: true,
        ..EmitOptions::default()
    };
    let d1 = decompile_module(&module, &opts);
    let d2 = decompile_module(&module, &opts);
    assert_eq!(d1.text, d2.text, "non-deterministic output in {abc}");
    d1.text
}

/// A line of the form `<ident> = <same-ident>;` (the stalling
/// self-assign back-edge).
fn has_self_assign(text: &str) -> Option<String> {
    for line in text.lines() {
        let line = line.trim();
        let Some(assign) = line.strip_suffix(';') else {
            continue;
        };
        let Some((lhs, rhs)) = assign.split_once(" = ") else {
            continue;
        };
        if !lhs.is_empty()
            && lhs == rhs
            && lhs
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$')
        {
            return Some(line.to_string());
        }
    }
    None
}

/// The stall-class shape: the loop must fold to `for (const k in obj)`,
/// with no iterator plumbing comments and no self-assigning back-edge.
fn assert_for_in_folded(abc: &str) -> String {
    let text = decompile(abc);
    assert!(
        text.contains("for ("),
        "{abc}: the for-in loop did not fold (fallback while(true) shape):\n{text}"
    );
    assert!(
        !text.contains("GetPropIterator plumbing"),
        "{abc}: GetPropIterator plumbing leaked into the output"
    );
    assert!(
        !text.contains("NextPropName plumbing"),
        "{abc}: NextPropName plumbing leaked into the output"
    );
    // NOTE: no `while (true)` absence check — an unrelated irreducible
    // CFG in the same fixture legitimately keeps a dispatch loop.
    if let Some(line) = has_self_assign(&text) {
        panic!("{abc}: self-assigning back-edge survived: `{line}`");
    }
    text
}

/// The smallest ledger row (Object.defineProperty): the loop body is a
/// `switch` whose arms each feed the redundant iterator copy phi.
#[test]
#[ignore = "requires exported corpus"]
fn n74_for_in_define_property() {
    let text = assert_for_in_folded(
        "24.0.0.0/test262/built-ins/Object/defineProperty/15.2.3.6-3-22/baseline/input.abc",
    );
    // The folded loop keeps the body (the switch on the key) and binds
    // the user variable from the for-in binding.
    assert!(text.contains("switch ("), "{text}");
}

/// Array.prototype.map row: the copy phi is fed through a NESTED
/// if/else + switch join (the elimination must recurse into nested
/// bodies, not just top-level runs).
#[test]
#[ignore = "requires exported corpus"]
fn n74_for_in_nested_branch_join() {
    assert_for_in_folded(
        "24.0.0.0/test262/built-ins/Array/prototype/map/15.4.4.19-8-c-iii-4/baseline/input.abc",
    );
}

/// Object.keys row.
#[test]
#[ignore = "requires exported corpus"]
fn n74_for_in_object_keys() {
    assert_for_in_folded(
        "24.0.0.0/test262/built-ins/Object/keys/15.2.3.14-5-12/baseline/input.abc",
    );
}

/// arguments-object row (a `language/` ledger row, not a built-ins one).
#[test]
#[ignore = "requires exported corpus"]
fn n74_for_in_arguments_object() {
    assert_for_in_folded(
        "24.0.0.0/test262/language/arguments-object/10.6-14-c-1-s/baseline/input.abc",
    );
}

/// arguments-object S10.6 rows: the body's early-continue arm carries
/// the self-assign back-edge (`if (!(k === "length")) { v = v;
/// continue; } else { return ...; }`) — no copy phi exists, so the
/// no-op self-assign strip must fire at ANY body position, not just the
/// loop tail. Each fixture carries TWO such loops.
#[test]
#[ignore = "requires exported corpus"]
fn n74_for_in_early_continue_back_edge() {
    for abc in [
        "24.0.0.0/test262/language/arguments-object/S10.6_A5_T2/baseline/input.abc",
        "24.0.0.0/test262/language/arguments-object/S10.6_A3_T2/baseline/input.abc",
    ] {
        let text = assert_for_in_folded(abc);
        assert!(
            !text.contains("while (true)"),
            "{abc}: a for-in loop kept the unfused while(true) shape:\n{text}"
        );
    }
}

/// Nested for-in (compound-assignment row): the OUTER iterator register
/// is live across the inner loop, so the inner header carries a second,
/// pass-through phi (`var v372; /* phi */` + back-edge `v372 = v372`)
/// — the fold must hoist that loop-invariant wiring above the inner
/// `for…in` (LICM) and fold BOTH loops.
#[test]
#[ignore = "requires exported corpus"]
fn n74_for_in_nested_loops() {
    let text = assert_for_in_folded(
        "24.0.0.0/test262/language/expressions/assignment/8.12.5-3-b_1/baseline/input.abc",
    );
    assert!(
        !text.contains("while (true)"),
        "a nested for-in loop kept the unfused while(true) shape:\n{text}"
    );
    assert_eq!(text.matches("for (").count(), 2, "{text}");
}

/// Positive control: the project-corpus for-in row that ALWAYS folded
/// (its straight-line body carries no iterator copy phi) must keep its
/// exact folded shape — the elimination is a no-op when no copy phi
/// exists, so the corpus `for_in` fold counter must not move.
#[test]
#[ignore = "requires exported corpus"]
fn n74_for_in_project_control() {
    let text = decompile("9.0.0.0/local/for-in/baseline/input.abc");
    assert!(text.contains("for ("), "{text}");
    assert!(!text.contains("GetPropIterator plumbing"), "{text}");
    if let Some(line) = has_self_assign(&text) {
        panic!("control row gained a self-assign: `{line}`");
    }
}
