# Phase 5 decision briefing (maintainer)

Date: 2026-09-20. Author: orchestrator (evidence: orchestrator-verified, see
`design/agent-roadmap.md` 全量发现对账表 for the per-item register).

## Where the project stands

- **VM oracle: 1119→1149 fixtures, 100% on BOTH variants** (lift-only and
  lift+optimize), on the pinned corpus image (sha256:5e7627bdcb78…), with
  deterministic output (three consecutive full rewrites byte-identical) and
  a per-instruction pandasm cross-check: 2,787 fixtures / 12,996 methods /
  2,691,470 instructions match upstream's own `reference.pa` exactly, on
  every version × profile (the v24 superset decode is instruction-exact for
  9.0.0.0/11.0.2.0 — the real 9/11 read verification).
- Rewrite pipeline: 1149/1149 fixtures lower+encode with zero skips, empty
  error histograms. Every registered finding N1-N52 either fixed, moot, or
  deliberately deferred (see the reconciliation table).
- Test infra: cargo runs on dabai (Ubuntu, ~33s full workspace), docker VM
  oracle local, container hygiene fixed (N24).

## Decisions that need YOU

### D1. IR v0.2 — start implementation now?

`design/ir.md` carries the agreed v0.2 proposal (format-independent IR;
`abcd-lift`/`abcd-lower` split; FormatProfile absorbs version differences).
What v0.2 fixes that v0.1 cannot: N46 (file-bound reference type payloads),
N52 (typed ARRAY_* literals keep raw file offsets), the four-bucket
annotation fold becoming a profile decision, `opt::inline` rewritten on the
new boundary (or dropped), num_vregs/num_args leaving the IR.

Options: (a) start now (big refactor, weeks of agent-time, existing v0.1
stays green meanwhile); (b) defer until a concrete consumer needs it
(e.g. a module-only encoder); (c) never (v0.1 is proven by the oracle).
Orchestrator's recommendation: (a) only if a v0.2 consumer is planned;
otherwise (b). The current design is verified end-to-end; v0.2 buys
cleanliness, not correctness.

### D2. opt::inline fate

Quarantined as a hard-gated no-op (cab3ab8): it produces module-invalid IR
(N44, red-probed). Options: rewrite under v0.2 (1-2 days agent-time) /
delete outright / leave quarantined indefinitely. Recommendation: decide
with D1 — rewrite only makes sense on the v0.2 IR.
**RULED (2026-09-20, maintainer): revisited AFTER v2-P3** — the inline
discussion needs the pass framework as its base; not scheduled before then.

### D3. Dead FFI surface policy

108/324 bridge exports are unused by in-repo callers (Phase 0.5 register).
The crates are publish-shaped (the surface is the product). Options:
keep-as-published (status quo) / prune to the used set / feature-gate.
Recommendation: keep (the crates' value proposition is the wrapped surface;
pruning saves nothing but docs). If you want a prune, it's a mechanical
task with CI guards.
**RULED (2026-09-20, maintainer): KEEP.** Reconciliation-table row closed.

### D4. FormatProfile evaluation

Currently: version handling is the v24 superset ISA table (zero
renumbering, instruction-exact per Task A evidence) + #A7 (no proto
signatures on 12+) + version-selected output policy at encode. The
v0.2 design moves all of this into a FormatProfile layer. Evaluate whether
that layer is worth building standalone (without the rest of v0.2).
Recommendation: bundle with D1; standalone it buys little.

## Open latent notes (none blocking)

N8 (typeSummaryOffset — verify or dismiss, P5-T2 in flight), N15/N16
(byte-level divergences, P5-T2), N51 (stthisbyvalue unemittable by es2abc —
nothing to fix), N52 (v0.2 material), F-new-1/F-new-2/N7 (format layer,
P5-T2 in flight). CI #22 (duplicate vendor files): you chose "leave as is";
drift-watch only.
