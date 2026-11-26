# Decompiler Architecture (`abcd-decompile`)

`abcd-decompile` translates [`abcd-ir::Module`](ir.md) into readable, syntactically valid JavaScript / TypeScript (and optional OpenHarmony ArkUI `@Component struct` source), verified end-to-end by recompiling emitted source with `es2abc` and comparing runtime behavior on `ark_js_vm`.

---

## 1. Architectural Rules

- **Pure IR + Analysis Consumer**: Depends **only** on `abcd-ir` and `abcd-analysis` in `[dependencies]`.
- **Pipeline Ordering Rule**: Never run `abcd_opt::inline::inline_module` before `abcd-decompile`—inlining erases function boundaries.
- **Fallback Honesty**: Silent miscompilation is forbidden. Any IR operation or state-machine shape that cannot be proven equivalent to surface syntax emits an explicit `Expr::Fallback` / `Stmt::Fallback` node, increments `DecompileStats`, and is enforced by two-way self-cleaning corpus ledgers.
- **Zero Recursion & Bit-Exact Determinism**: Every region walk, AST fold, scope pass, and expression/statement printer uses explicit heap workstacks (`256 KiB` stack-safe) and produces deterministic output (`N20`).

---

## 2. Three-Stage Pipeline

### Stage A — Expression & Name Recovery (`src/recover.rs`, `src/names.rs`, `src/consts.rs`)
1. **SSA Def-Use Inlining & Coercion-Order Monotonicity**: Single-use expressions inline into their same-block consumer across [`UseDefChains`](analysis.md) only when intervening instructions are absorbed or pure under [`Op::effects_in(module)`](ir.md) and effectful/mutable-reading operands preserve left-to-right JS evaluation order (`N36`). Unconditional runtime throw ops (`ThrowConstAssignment`, `ThrowNotExists`, `ThrowPatternNonCoercible`, and provably-hole TDZ guards) materialize as executable `throw new TypeError/ReferenceError(...)` statements rather than elided comments.
2. **Out-of-SSA Phi Wiring & Pre-Throw Flushing**: Parallel `Op::Phi` assignments on CFG edges are scheduled in `O(k)` via reader-count worklists so inlined expressions read pre-edge values before clobbering target slots, breaking permutation cycles with `PhiDecl` temporaries and flushing exception-edge phis prior to each block's first potentially throwing statement (`ADR-04`).
3. **Vendor Operand, Frame-Slot & Constant Fidelity**: Swaps `left`/`right` operands to match ArkCompiler's `vreg OP acc` evaluation order (`N36`), derives parameter roles via [`abcd_ir::frame::FrameSlots`](ir.md) (`ADR-05`, honoring `L_ESCallTypeAnnotation;` and `Dialect::StaticArkTS` `H = 0/1`), formats `f64` bit-exactly (`-0.0` preserved, negative literals parenthesized in primary/exponentiation positions), escapes NUL before digits as `\x00` and unpaired MUTF-8 surrogates as `\uXXXX` (`N75`), bounds shared-literal DAG expansion, and recovers raw/cooked template quasi arrays.
4. **Evidence-Only Name Resolution (`src/names.rs`, `src/legalize.rs`)**:
   - Propagates `NewLexEnvWithName` / `ClassData::scope_names` / debug local names transitively across `Arc`-shared parent closure frames and reserves globals/lexical bindings before minting `O(1)`-suffixed synthetic temporaries.
   - Isolates per-record `EsModule` external, namespace, and local export slot spaces in both single-file and `--split-modules` emission (including side-effect-only `import "./dep";` requests).
   - Legalizes identifiers against JS keywords and read-only globals (`NaN`, `Infinity`, `undefined`).

### Stage B — Control-Flow Structuring & Desugaring Folds (`src/structure/`, `src/folds/`, `src/classfold.rs`)
1. **Pattern-Independent Structuring (`src/structure/mod.rs`)**: Walks `abcd_analysis::control::regions` (`Seq`, `If`, `Loop`, `Switch`), emitting clean `while` / `do...while` / labeled `break` & `continue` constructs (with bounded tail duplication and a state-dispatch escape hatch for irreducible subgraphs).
2. **Laminar `TryRegion` Projection (`src/structure/try_project.rs`)**: Projects PC-range `TryRegion`s onto structured AST nodes while keeping catch handlers outside the Normal region tree—supporting cut-try join hoisting (`emit_cut_try`), loop-cut `do...while` tries, and continuation tower de-absorption (`emit_deabsorb_tower`).
3. **Idiomatic JS/TS Desugaring (`src/folds/`)**:
   - **State Machines (`folds/machines/`)**: Folds `es2abc` `function*` (`yield`), `async function` (`await`, including `effective_kind` recovery on API 9 metadata-less methods), `async function*`, `yield*` delegation, and `for await (const x of ...)` loops back into native syntax whenever the function's entry/dispatch protocol matches upstream `functionBuilder.cpp` shapes.
   - **Scopes, Control & Literals**: Reconstructs block-scoped `let` declarations (`scope_fold`, TDZ-honest `late_decl_fold`), `...rest` parameters and object rest destructuring, `for...of` / `for...in` loops, `switch` chains, alpha-equivalent duplicated `finally` blocks, object/array literal builders, and ES/TS classes (`classfold.rs`, including static/instance placement from `MemberAttrs`, field initializers, accessors, and `#private` fields).

### Stage C — Emission, `--split-modules`, and `--arkui` (`src/emit/`, `src/split.rs`, `src/arkui.rs`)
- **Precedence-Exact Printer (`src/emit/`)**: Emits single-file JS or TypeScript-annotated output (`EmitOptions::ts`, rendering surviving `Signature` metadata without fabricating missing types).
- **Multi-Module Bundle Recovery (`--split-modules`, `src/split.rs`)**: Splits `--merge-abc` bundles into safe relative directory trees per `ClassData` record, isolating per-record `EsModule` import/export index spaces, emitting `jsonFileContent` `.json` assets, and rewriting `@bundle:` / `@package:` / `@normalized:` OHMUrls to POSIX relative imports.
- **OpenHarmony ArkUI Sugar (`--arkui`, `src/arkui.rs`)**: Opt-in presentation pass reconstructing `@Entry` / `@CustomDialog` / `@Component struct`, reactive state decorators (`@State`, `@Prop`, `@Link`, `@ObjectLink`, `@Provide`, `@Consume`, `@LocalStorage*`, `@Storage*`), `@Builder` methods, and `build() { ... }` component trees (`observeComponentCreation2`, `If`, `ForEach`, `LazyForEach`, child `$link` bindings) from `ViewPU`/`View` classes.

---

## 3. Verification Gates

| Gate (`tests/lift-decompile/`) | Coverage & Contract |
| :--- | :--- |
| **`dream_gate`** | **`1,149 / 1,149`** runtime-passed corpus fixtures: `decompile → es2abc → ark_js_vm` stdout/stderr/exit-code equivalence (`0` divergences) |
| **`dream_gate_t262`** | **`2,676 / 2,685`** `test262` fixtures pass `decompile → es2abc → ark_js_vm` (`0` decompile bugs; `9` documented generator-plumbing fallbacks in `scripts/test262-dream-divergences.json`) |
| **`wild_gate`** | **`64 / 64`** `.abc` modules across the core-25 wild OpenHarmony `.hap` set recompile cleanly under `es2abc`, exercise `--split-modules` + `--arkui`, and match `scripts/wild-dream-divergences.json` (`< 1%` global fallback ceiling) |
| **`merge-abc`** | Multi-file `--merge-abc` bundles across `12.0.6.0`–`24.0.0.0` decompiled with `--split-modules`, re-bundled by `es2abc --merge-abc`, and verified on `ark_js_vm` |
