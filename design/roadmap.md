# Roadmap and Working Agreements

## Two phases

### Phase 1 (current) — bytecode ⇄ IR

Complete, solid bidirectional conversion between ABC bytecode and the SSA IR. This is the foundation of the whole project.

### Phase 2 (future) — IR ⇄ source

Decompilation (IR → source) and compilation (source → IR), built on top of the Phase-1 IR.

## IR positioning: "Hermes-like in form, different in purpose"

The IR borrows Hermes' *shape and engineering*: SSA basic blocks, phis, arena index model, textual printing, verifier, and a peephole/SCCP/ADCE-style optimization pipeline. The *purpose* is different:

- Hermes generates IR on the way from AST to bytecode and may discard information.
- Our IR is lifted **from bytecode** and must preserve **semantics**: all four annotation categories, debug info, try regions, function kind, access flags. The only things deliberately dropped are pure performance metadata (IC slots, JIT name hints), documented in design/ir.md.

One IR serves three downstream consumers:

1. **Analysis** — dominators, use-def chains, and whatever future passes need;
2. **Optimization** — the opt/ pipeline;
3. **Decompilation** — the Phase-2 source direction.

Therefore Phase 1 is not "make it run"; every node must hold up to all three uses.

## Why vendor code for isa and file

The ground truth of the ISA lives in `isa.yaml`; the ground truth of the container format lives in libpandafile. Rewriting either means permanently maintaining a mirror that chases upstream. The chosen trade-off:

- **vendor zero-diff + daily auto-sync**; all local adaptation is confined to shims, build flags, and the C bridge.
- The cost is upstream API drift hitting the bridge first (the API-24 adaptation of 2026-08 is the canonical example). That cost is acceptable — it trades "format/ISA semantics maintenance" for "upstream API chasing".

## design/ directory policy

`design/` is the **knowledge deposit**: everything the project has decided, discovered, or still owes lives here in Markdown, so it survives context compaction and is easy for the maintainer to read and check.

- Content is English (the repository is public).
- These are **working documents**, not user docs. When the project reaches v0.1 they will be deleted and rewritten from the stabilized state.
- Review findings, accepted decisions, and open questions all belong here — if it is not in design/, it did not happen.

## Phase-1 acceptance criteria

1. **Semantic round-trip**: decode → lift → optimize → lower → encode → decode on a real `.abc` file is field-level equivalent; `encode_roundtrip` is un-`#[ignore]`d and green in CI.
2. **Opt safety**: every pass is covered by tests proving semantics before == semantics after.
3. **Quality review**: the isa/file review findings are triaged, fixed, and the report's status column is updated as work lands.
4. **No known P0/P1** in the layers below IR at the time of the v0.1 cut.

## Quality review process

1. Formal review report first (per layer: isa, file, then ir), with per-file findings, severity triage, evidence, and proposed fixes — **the maintainer reads and aligns before any code changes**.
2. Fixes land one commit at a time, each with a regression test that would have caught the issue.
3. The report's status column tracks each finding to completion.
