# abcd-hap: HAP/HSP/APP container parsing — upstream research + design proposal

Status: phase 1 IMPLEMENTED (a8aa214, crate `abcd-hap/`; 39 tests green,
real-hap byte-exact cross-check passed). This document remains the design reference.
Upstream evidence base: `developtools_packing_tool` @ commit `b2aa3f6` ("!1568 merge master into master"),
read-only at `developtools_packing_tool/`. All file:line citations below refer to that checkout.

## 1. Executive summary

- OpenHarmony ships **two** packing toolchains in one repo:
  - a **Java toolchain** (`adapter/ohos/`) that produces four JARs (`app_packing_tool.jar`,
    `app_unpacking_tool.jar`, `app_check_tool.jar`, `haptobin_tool.jar`), and
  - a **C++ toolchain** (`packing_tool/frameworks/`) that builds a single executable
    `ohos_packing_tool` — **pack only**. The repo's own `AGENTS.md` states the C++ side has
    no unpack/scan/haptobin tool; its `unzip_wrapper` is an internal helper used by
    pack/normalize flows only.
  - For unpacking, the **Java `app_unpacking_tool.jar` (entry `ohos.UncompressEntrance`,
    `META-INF/unpacking_tool/MANIFEST.MF`) is the current and only mainline**.
- Every container in scope — **.hap, .hsp, .app, .har, .hqf, .appqf** — is a plain
  ZIP archive with HarmonyOS-mandated entry names (`README_zh.md:5` lists exactly this set
  for unpack; `.qf`/`.hqf` = quick-fix, `.appqf` = aggregated quick-fix).
- The Ark bytecode entry is **exactly one file at the fixed path `ets/modules.abc`**
  (`adapter/ohos/Uncompress.java:82`). It is STORED by the packer by default but is
  **not guaranteed 4K-aligned** (verified on a real-world hap below), so mmap-from-zip
  is not a safe assumption; we must be able to read/inflate entry data.
- Signed haps carry a signing block between the last entry and the central directory;
  a central-directory-first ZIP reader is unaffected (no code in the packing tool even
  looks at signatures — verification lives in the separate `hapsigner` repo).
- Proposal: **`abcd-hap` = pure-Rust, in-memory, unpack-only container reader** with a
  hand-written ZIP central-directory parser (STORED + DEFLATE via `miniz_oxide`),
  outputting `.abc` byte slices + provenance metadata straight into `abcd-file`.
  Tests **synthesize** ZIP bytes in code (no binary fixtures in-repo); real fixtures go
  to the `ghcr.io/fxti/arkcompiler-test` corpus image later.

---

## 2. Upstream research: `developtools_packing_tool`

### 2.1 Languages, build systems, module split

| | Java toolchain | C++ toolchain |
|---|---|---|
| Sources | `adapter/ohos/*.java` (~90 classes) + `adapter/scanner/` | `packing_tool/frameworks/{include,src}` |
| Build | root `BUILD.gn` → `packingtool.gni` → `build.py` + `packingTool.sh` / `unpackingTool.sh` / `haptobin.sh` (javac 1.8 + `jar -cvfm` with `META-INF/<tool>/MANIFEST.MF`) | root `BUILD.gn` `ohos_group("ohos_packing_tool")` → `packing_tool/frameworks/BUILD.gn` (GN/Ninja, OpenHarmony `hb build`) |
| Products | `app_packing_tool.jar`, `app_unpacking_tool.jar`, `app_check_tool.jar`, `haptobin_tool.jar` | `ohos_packing_tool` executable |
| Scope | pack + **unpack** + scan + haptobin | **pack only** (modes in `packing_tool/frameworks/include/constants.h:29-41`: hap/hsp/app/hqf/appqf/multiApp/versionNormalize/packageNormalize/generalNormalize/fastApp/res) |

The repo's own `AGENTS.md` (§2 "Code map") confirms: *"C++ 工具链只包含打包工具
`ohos_packing_tool`，不包含拆包工具、扫描工具或 haptobin 工具"* — unpack/scan/haptobin
are Java-only capabilities. So for our purposes the Java side is normative; the C++ side is
still worth reading for its ZIP layer and pack-side format decisions (what ends up in the
container is decided by whoever packs).

### 2.2 Unpack call chain (Java)

CLI entry and dispatch:

```
UncompressEntrance.main()                        adapter/ohos/UncompressEntrance.java:514
 ├─ CommandParser.commandParser(utility, args)   (fills ohos.Utility: mode, paths, flags)
 ├─ UncompressVerify.commandVerify(utility)      adapter/ohos/UncompressVerify.java
 └─ Uncompress.unpackageProcess(utility)         adapter/ohos/Uncompress.java:93
     switch (utility.getMode())                  Uncompress.java:119
     ├─ MODE_HAP → unpackageHapMode()            Uncompress.java:155
     │    ├─ --libs  → unpackageLibsMode()       (selective libs/<abi>/ extraction)
     │    ├─ --rpcid → getRpcidFromHap()
     │    ├─ --unpack-apk → unzip(..., ".apk") + repackHap()   (embedded shell APKs)
     │    └─ default → dataTransferAllFiles()    Uncompress.java:175
     ├─ MODE_HAR → dataTransferAllFiles()        Uncompress.java:123-124  (.har = plain unzip)
     ├─ MODE_APP → dataTransferFilesByApp()      Uncompress.java:127  (nested .hap/.hsp entries)
     ├─ MODE_HSP → unpackageHspMode()            Uncompress.java:188 → dataTransferAllFiles()
     └─ MODE_APPQF → uncompressAPPQFFile()       (nested .hqf entries)
```

Actual extraction primitives:

- `unzip()` / `unzipFromFile()` — `Uncompress.java:537/565`: iterates `java.util.zip.ZipFile`
  entries filtered by suffix, then `dataTransfer()` (`Uncompress.java:639`) streams each entry
  to disk. **Zip Slip guard**: destination path must pass `FileUtils.matchPattern()`
  (`Uncompress.java:643-645`, regex `PATTERN` in `FileUtils.java:659-665`) — a denylist
  regex, not a canonical-path containment proof.
- `dataTransferAllFiles()` — `Uncompress.java:673`: whole-archive extraction (hap/hsp/har).

Library (non-CLI) parse APIs on `UncompressEntrance` — these are the published surface used
by other tools (`parseHap`, `parseHapList`, `parseAPPQF`, `parseResource`, …, modes
`PARSE_MODE_HAPLIST` / `PARSE_MODE_HAPINFO` / `PARSE_MODE_ALL` at
`UncompressEntrance.java:36-46`):

- FA model (old, `config.json`): `unZipHapFileFromInputStream()` — `Uncompress.java:849` —
  streams entries, captures `pack.info`, `config.json`, `resources.index`, and records
  whether `ets/modules.abc` is STORED (`Uncompress.java:874-877`).
- Stage model (current, `module.json`): `unZipModuleHapFileFromInputStream()` —
  `Uncompress.java:1502` — captures `module.json` (`:1521`), `resources/base/profile/*`
  (`:1525`), `resources.index`, plus the same `modules.abc` STORED check (`:1532-1535`).
- Model discrimination: presence of `module.json` entry ⇒ Stage model —
  `isModuleHap()` `Uncompress.java:1555-1578`.
- `.app` parse: opens the outer ZIP, reads root `pack.info` for the module list and
  re-parses each nested `*.hap`/`*.hsp` entry as a stream —
  `uncompressAllAppByPath()` `Uncompress.java:278-299`,
  `uncompressHapAndHspFromAppPath()` `Uncompress.java:239-276`.

**Key observation:** upstream's parse APIs return *metadata* (profile info, pack.info, abc
compression flag) — they never hand you the abc bytes. Byte extraction only happens through
the dump-everything-to-disk CLI path. Our crate's "give me the abc bytes" API is therefore a
strict improvement, not a port.

### 2.3 C++ pack side (what decides the on-disk format)

Entry: `main.cpp:26` → `ShellCommand::ExecCommand()` → `getPackager()` mode dispatch
(`src/shell_command.cpp:137-164`) → `Packager::MakePackage()` phase pipeline
`InitAllowedParam → PreProcess → Process → PostProcess` (`src/packager.cpp:72-109`).

ZIP layer: `zip_wrapper.{h,cpp}` / `unzip_wrapper.{h,cpp}` / `zip_utils.cpp`, built on
**minizip** (zlib contrib). Default write method is **STORED** —
`include/zip_wrapper.h:96` (`ZipMethod zipMethod_ = ZipMethod::ZIP_METHOD_STORED;`).
The C++ unzip wrapper has a real Zip Slip check (`IsSafeZipEntryName`,
`src/unzip_wrapper.cpp:102`) and only exists to serve pack/normalize internals.

### 2.4 Container formats

All containers are ZIP. Differences are **entry-name contracts and nesting**:

| Container | Role | Distinguishing entries |
|---|---|---|
| `.hap` | one ability module (entry/feature) | `module.json` (Stage) or `config.json` (FA), `ets/modules.abc`, `resources.index`, `pack.info`, `libs/<abi>/*.so`, `rpcid.sc` (opt) — names from `adapter/ohos/Uncompress.java:57-82` and `Constants.java:182-207` |
| `.hsp` | dynamic shared package | same layout as hap; `module.json` says `"type": "shared"`; unpack mode `hsp` (`Utility.java:40`) |
| `.har` | static shared package | plain ZIP of build artifacts; unpack = `dataTransferAllFiles` (`Uncompress.java:123-124`); **contains compiled artifacts, no `ets/modules.abc` contract** (it ships `ets/modules.abc` in some builds — treat as best-effort) |
| `.app` | application package | root `pack.info` + nested `*.hap` / `*.hsp` entries, one per module (`Uncompress.java:289-298`; pack side `app_packager.cpp:700-729`) |
| `.hqf` | quick-fix (hot patch) for one module | `patch.json` + replacement `ets/` / `libs/` trees (`hqf_packager.cpp:72`, `Uncompress.java:78-79`) |
| `.appqf` | aggregated quick-fix | nested `*.hqf` entries, each carrying `patch.json` (`appqf_packager.cpp:42-64`) |

ZIP dialect constraints (pack-side facts):

- **STORED is the default.** C++: `zip_wrapper.h:96`. Java: `Compressor.compressFile()`
  picks STORED unless compression is explicitly requested
  (`adapter/ohos/Compressor.java:2946-2975`); several JSON entries are force-STORED.
- **Nested haps inside `.app` are DEFLATED** — `app_packager.cpp:716` sets
  `ZIP_METHOD_DEFLATED` before adding each hap (debug packages even force level 0 at `:713-715`).
  ⇒ an unpacker that only handles STORED **cannot** recurse into `.app`.
- **No 4K-alignment logic exists in this repo** — there is no extra-field padding writer
  anywhere in the ZIP layer (the only `align` hit in the whole tree is an unrelated test
  name). Device-side mmap alignment (the runtime/compiler know offsets like
  `"abcOffset":"0x1000"` — see `arkcompiler_ets_runtime-master/compiler_service/test/...`)
  must be arranged by a different pipeline stage, and is **not a container invariant**.
- **Signing block**: produced by the separate `hapsigner` tool, absent from this repo's
  code paths entirely. It sits between the last entry's data and the central directory
  (APK-signing-block style). Any reader that locates the EOCD by scanning backwards and
  then follows absolute central-directory offsets is unaffected. The packing tool itself
  never verifies signatures on unpack.

### 2.5 Locating and validating the abc entry

- Fixed path constant: `MODULE_ABC = "ets/modules.abc"` — `Uncompress.java:82`.
- Detection + STORED flag: `Uncompress.java:874-877`, `:1364`, `:1532-1535`
  (`isCompressed = entry.getMethod() != ZipEntry.STORED`, recorded into
  `HapZipInfo.isModuleAbcCompressed`). Upstream only *records* the compression flag; it
  does not reject compressed abc.
- Exactly **one** abc per hap: a hap is one module, and the module's whole compiled
  program is the single `ets/modules.abc` (Stage). Multi-module apps are multi-hap
  (`.app` nesting), not multi-abc. Sibling artifacts: `ets/sourceMaps.map`, `ets/*.abc`
  overlays do not exist in the packer contract; `--an-path`/`--ap-path` add annotation /
  profile files under `ets/` but only `modules.abc` is bytecode.
- Model check for validation: `module.json` presence = Stage (`Uncompress.java:1555`).

### 2.6 Third-party dependencies on the unpack path

- Java unpack: **`java.util.zip` only** (`Uncompress.java:41-46`). JSON parsing for the
  parse APIs uses **fastjson/fastjson2** (imports at `Compressor.java:59-63`; prebuilt JARs
  wired in root `BUILD.gn:62-74`). The Java *pack* side additionally uses Apache
  commons-compress `ParallelScatterZipCreator` (`Compressor.java:64-67`) — not needed for unpack.
- C++: **minizip (zlib)** + **cJSON** (`packing_tool/frameworks/BUILD.gn:101,105,119`) —
  irrelevant for us beyond format confirmation.
- Pack/unpack coupling to shed: everything hangs off the shared `ohos.Utility` bag and
  `CommandParser`; `Uncompress` also drags in `JsonUtil`/`ProfileInfo`/`restool` for the
  metadata APIs. The raw byte-extraction core (`ZipFile` iteration + `dataTransfer`) is
  small and self-contained — that is the part worth mirroring.

### 2.7 Upstream tests

- **No Java tests at all** in the repo (`find -name '*Test*.java'` → empty). Verification
  for the JARs is "compile with Java 8 + CLI smoke tests" per `AGENTS.md`.
- C++ GTest/HWTEST suites under `packing_tool/frameworks/test/unittest/` — ~20 dirs
  (`zip_wrapper_test`, `unzip_wrapper_test`, `hap_packager_test`, `app_packager_test`,
  `json/*`, `dedup`, …).
- **No committed binary container fixtures**: fixture dirs hold text inputs only
  (63 `.json`, 20 `.png`, 8 `.ets`, …; zero `.hap`/`.hsp`/`.app`). Tests *generate*
  packages from JSON/text inputs at runtime, then assert on re-read structure.
- Worth borrowing: the generate-then-verify pattern (no binary blobs in VCS), the
  negative-path cases in `zip_wrapper_test` / `unzip_wrapper_test` (unsafe entry names,
  partial writes, CRC errors), and the per-mode packager fixture layout.

### 2.8 Local cross-validation (not committed)

- Real hap `/Users/fxti/Downloads/ClashNEXT-1.3.3.hap` (unsigned debug build,
  `compileSdkVersion 5.0.4.150`): 69 entries, **all STORED**, exactly one
  `ets/modules.abc` (3.5 MB) at local-header offset `0x44fa54e`, data offset
  `0x44fa57b` — **not 4K-aligned**. No signing block present; EOCD at EOF-22.
  `module.json` (Stage) and `pack.info` parse as plain JSON.
- Official `app_unpacking_tool.jar --mode hap` output is a straight tree dump:
  `ets/  libs/  module.json  pack.info  pkgContextInfo.json  resources/  resources.index`
  — consistent with `dataTransferAllFiles`.

---

## 3. `abcd-hap` design proposal

### 3.1 Position

```
.hap/.hsp/.app ──▶ abcd-hap (ZIP CD parse, entry slice/inflate, provenance)
                        │  Vec<u8> / &[u8] + AbcProvenance{entry_name, container, module_name}
                        ▼
                   abcd-file (existing) ──▶ rest of pipeline
```

- **Unpack-only, in-memory only.** We never write extracted trees to disk, so the entire
  Zip Slip / canonical-path machinery that dominates upstream's unpack code is unnecessary;
  entry names are just lookup keys.
- Input is `&[u8]` (caller decides file vs mmap; `memmap2` is already a workspace dep).
- Output: borrowed slices for STORED entries, owned `Vec<u8>` for DEFLATE, plus metadata
  (entry name, compression method, offset/alignment facts, `module.json`/`pack.info` raw
  JSON for the caller to interpret).

### 3.2 ZIP strategy: hand-written central-directory reader

A hap is a *restricted ZIP dialect*: no spanned archives, no encryption, no data
descriptors we must honor (CD is authoritative), methods {STORED, DEFLATE}. The reader is:

1. Scan backwards ≤ 64 KiB + EOCD-comment for `PK\x05\x06`; read CD offset/count.
2. Walk central headers `PK\x01\x02`: name, method, CRC, sizes, local-header offset.
3. Per entry: seek to local header `PK\x03\x04`, skip name+extra, data = `size` bytes.
4. STORED → slice; DEFLATE → `miniz_oxide::inflate`.

That is ~300–400 lines with full bounds checking. Compared to the `zip` crate:

| | hand-written | `zip` crate |
|---|---|---|
| deps | `miniz_oxide` only (pure Rust, already transitive via `flate2` ecosystems) | `zip` + several backend deps, large API we don't need |
| borrowing STORED slices | trivial (`&[u8]` into input) | possible but awkward through its `Read` API |
| restricted-dialect assumptions | explicit, auditable | hidden behind general-purpose code |
| risk | we own ZIP edge cases (must get EOCD scan + u32 bounds right) | battle-tested general ZIP |

**Recommendation: hand-written reader + `miniz_oxide`.** It matches the workspace's
existing posture (thin, auditable layers; `thiserror` errors; no heavy deps — current
workspace deps are clap/thiserror/serde/memmap2/log/bitflags/string-interner only).
Signing blocks need no code: EOCD scan + absolute CD offsets tolerate them by construction.

### 3.3 API sketch

```rust
pub struct ZipArchive<'a> { /* cd index over &'a [u8] */ }
impl<'a> ZipArchive<'a> {
    pub fn open(bytes: &'a [u8]) -> Result<Self, Error>;
    pub fn entries(&self) -> impl Iterator<Item = &EntryMeta>; // name, method, sizes, offsets
    pub fn entry(&self, name: &str) -> Option<&EntryMeta>;
    pub fn read(&self, name: &str) -> Result<EntryData<'a>, Error>; // Borrowed(&[u8]) | Owned(Vec<u8>)
}

pub enum Container<'a> {            // sniffed by entry set, not file extension
    Module(ZipArchive<'a>),         // hap/hsp/hqf: has module.json|config.json, ets/modules.abc
    App { outer: ZipArchive<'a>, modules: Vec<String> },  // .app: pack.info + nested *.hap/*.hsp
}

pub struct AbcModule<'a> {
    pub data: EntryData<'a>,        // ready for abcd_file::File::open-style API
    pub entry_name: String,         // normally "ets/modules.abc"
    pub compression: Compression,   // Stored{data_offset} | Deflated
    pub module_json: Option<EntryData<'a>>,
    pub container_path: Vec<String>,// e.g. ["app", "entry.hap"] provenance
}

pub fn abc_modules(bytes: &[u8]) -> Result<Vec<AbcModule<'_>>, Error>; // top-level entry point
```

- `.app` recursion: read nested `*.hap` bytes (inflating as needed), re-run `ZipArchive::open`
  on them, flatten with provenance. Depth cap = 2 (app → hap), matching upstream semantics.
- `.hqf`: same Module path; expose `patch.json` alongside.
- No CRC check by default (abc has its own integrity story); offer `verify_crc` flag later.

### 3.4 Error handling

`#[derive(thiserror::Error)] pub enum Error` in the established workspace style
(see `abcd-file/src/error.rs`): `NotZip`, `Truncated{context}`, `BadCentralDirectory`,
`EntryTooLarge{name}`, `UnsupportedMethod{method}`, `Inflate(name)`, `NoAbcEntry`,
`AppWithoutPackInfo`-style soft notes as data, not errors. **No panics on data** — every
index arithmetic through checked slice getters; fuzzable `open()`/`read()` over arbitrary
bytes must be total.

### 3.5 Test strategy (no binary fixtures in-repo)

| Option | Verdict |
|---|---|
| **(a) Synthesize ZIP bytes in Rust test code** | **Recommended primary.** A ~100-line test helper writes local headers + CD + EOCD for STORED/DEFLATE entries (deflate via `miniz_oxide` in dev-deps). Covers: minimal hap (`module.json` + `ets/modules.abc`), deflated nested hap inside synthetic `.app`, signing-block junk inserted before CD, truncated EOCD/CD, u32-overflow sizes, unsafe entry names, hqf patch layout. Fully deterministic, no blobs in VCS. |
| (b) Borrow upstream test ideas, own data | Fold into (a): port `zip_wrapper_test`/`unzip_wrapper_test` negative cases (bad names, partial data, CRC mismatch) as synthesized inputs. Not a separate strategy. |
| (c) Real fixtures in `ghcr.io/fxti/arkcompiler-test` | **Recommended second phase**, integration-level: 2-3 real signed haps (incl. one with signing block, one `.app`, one `.hsp`), digest-pinned like the existing corpus (`MEMORY.md` pattern: opt-in corpus tests reading `exports/corpus/index.jsonl`). Validates against the wild; not required for L1. |

Additionally keep `/Users/fxti/Downloads/ClashNEXT-1.3.3.hap` + `app_unpacking_tool.jar`
as local-only manual cross-checks (already demonstrated above).

## 4. Open questions / later work

- Whether `.har` ever ships an `ets/modules.abc` worth exposing (best-effort lookup).
- CRC verification policy once we hand slices to abcd-file on hot paths.
- If we ever need mmap-zero-copy from STORED+aligned entries, add an alignment *hint* in
  `Compression::Stored{data_offset}` — the data offset is already exposed; do not require it.
