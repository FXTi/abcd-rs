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
1. **SSA Def-Use Inlining & Effect Barriers**: Single-use pure/movable expressions inline into their consumer across [`UseDefChains`](analysis.md) as long as no intervening instruction's [`Op::effects()`](ir.md) conflicts with the expression's read/throw dependencies.
2. **Out-of-SSA Phi Wiring**: Parallel `Op::Phi` assignments on CFG edges are topologically ordered so inlined expressions read pre-edge values before clobbering target slots, breaking permutation cycles with `PhiDecl` temporaries and flushing exception-edge phis prior to terminal `throw`s (`ADR-04`).
3. **Vendor Operand & Constant Fidelity**: Swaps `left`/`right` operands to match ArkCompiler's `vreg OP acc` evaluation order (`N36`), formats `f64` bit-exactly (`-0.0` preserved), escapes unpaired MUTF-8 surrogates as `\uXXXX` (`N75`), and recovers both raw and cooked quasi arrays for template and tagged-template literals.
4. **Evidence-Only Name Resolution (`src/names.rs`, `src/legalize.rs`)**:
   - Propagates `NewLexEnvWithName` / `ClassData::scope_names` / debug local names transitively across parent closure chains (keying unnamed fallback slots by absolute chain depth `v{abs}_{slot}` so owners and nested closures agree).
   - Resolves module-local export names from `throw.undefinedifholewithname` TDZ guards and `StoreModuleVar` definitions (demangling `12.0.6+` `#*#name` / `#~@0=#Class` tags and poisoning conflicting claims).
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
