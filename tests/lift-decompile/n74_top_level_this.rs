//! N74-W3 red-first: the `call_entry` wrapper must receive the
//! SCRIPT-level `this` (the global object), not `undefined`.
//!
//! Root cause (verified against the pinned image
//! `ghcr.io/fxti/arkcompiler-test@sha256:45f4daf6…`): the VM invokes a
//! script's `func_main_0` with `this` = the global object (ark sloppy
//! script semantics — `this.x = 1` at script top level works). The
//! decompiler wraps the module body in `function func_main_0() {…}`
//! and used to emit a PLAIN call `func_main_0();` — es2abc compiles
//! the function strict, so the wrapper's receiver became `undefined`
//! and every script-level `this` read/store diverged (TypeError on
//! store). Node's sloppy mode masked it; ark's runtime does not.
//!
//! Fix: emit `func_main_0.call(this);` — the emitted file's own
//! top-level `this` is exactly the receiver the VM would have bound
//! (script → globalThis; module → undefined, matching module
//! semantics, where the plain call already behaved correctly).
//!
//! Ledger class: `scripts/test262-dream-divergences.json`
//! `decompile-bug-top-level-this-undefined` (9 rows).
//!
//! NOT registered in `main.rs` (N74 worker protocol: parallel workers
//! must not contend on the shared module list); run standalone by
//! temporarily adding `mod n74_top_level_this;`.

use abcd_decompile::emit::{decompile_module, EmitOptions};
use abcd_ir::Op;

use crate::common::decompile_scaffold::*;

/// A script main that stores through `this` (the shape of every
/// ledgered row, e.g. test262 S7.7_A1's `this.nan = NaN`): with
/// `call_entry`, the emitted entry call must bind the surrounding
/// script's `this` so the store lands on the global object.
#[test]
fn n74_script_entry_call_binds_top_level_this() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, f);
    let this = add_param(&mut m, f); // the hidden slot prints as `this`
    let forty_two = load_number(&mut m, b, 42.0);
    let answer = intern(&mut m, "answer");
    emit_void(
        &mut m,
        b,
        Op::StoreProp {
            object: this,
            name: answer,
            value: forty_two,
        },
    );
    emit_void(&mut m, b, Op::Return { value: None });

    let d = decompile_module(
        &m,
        &EmitOptions {
            call_entry: true,
            ..EmitOptions::default()
        },
    );
    assert!(
        d.text.contains("this.answer"),
        "the body must keep the `this` store:\n{}",
        d.text
    );
    assert!(
        d.text.ends_with("func_main_0.call(this);\n"),
        "the entry call must pass the script's top-level `this` as the \
         receiver (ark binds globalThis at script entry; a plain call \
         yields undefined under es2abc's strict functions):\n{}",
        d.text
    );
}

/// Without `call_entry` the output stays clean (human-facing default):
/// no entry call at all.
#[test]
fn n74_no_call_entry_no_entry_call() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, f);
    emit_void(&mut m, b, Op::Return { value: None });

    let d = decompile_module(&m, &EmitOptions::default());
    assert!(
        !d.text.contains("func_main_0.call(this)"),
        "default output must not call the entry:\n{}",
        d.text
    );
    assert!(
        !d.text.contains("func_main_0();"),
        "default output must not call the entry:\n{}",
        d.text
    );
}
