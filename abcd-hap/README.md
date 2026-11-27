# abcd-hap

Pure-Rust, in-memory, unpack-only reader for OpenHarmony and HarmonyOS application containers (`.hap`, `.hsp`, `.app`, `.hqf`).

## Purpose & Layering Contract

`abcd-hap` sits at the container ingress edge of the `abcd-rs` workspace, turning raw application package bytes (`&[u8]`) into extracted ArkCompiler `.abc` payloads and manifest summaries without touching the filesystem or invoking C/C++ code.

- **Zero-C, zero-`serde`, pure-Rust footprint**: runtime dependencies are strictly [`miniz_oxide`](https://crates.io/crates/miniz_oxide) (raw DEFLATE inflation) and [`thiserror`](https://crates.io/crates/thiserror), with `#![forbid(unsafe_code)]`, `#![deny(missing_docs)]`, and `clippy::unwrap_used` denied in library code.
- **Strict upward-free layering**: `abcd-hap` has zero runtime dependency on `abcd-isa`, `abcd-file`, `abcd-ir`, or any analysis crate (`abcd-file` appears only in `[dev-dependencies]` for end-to-end integration tests).
- **Unpack-only in-memory boundary**: callers pass `&[u8]` and receive `AbcModule<'_>` payloads (`EntryData::Borrowed(&[u8])` for top-level `STORED` entries, `EntryData::Owned(Arc<[u8]>)` for `DEFLATE` or nested `.app` entries, sharing container-level manifests in `O(1)` across multi-`.abc` modules).

## Architecture & Module Map

OpenHarmony packages are ZIP archives in the restricted dialect produced by `developtools_packing_tool` (single-disk, unencrypted, 32-bit classic ZIP, methods `STORED` = 0 and `DEFLATE` = 8, optional APK-style signing block immediately before the central directory):

1. **Central-directory ZIP reader (`src/zip.rs`)**: `ZipArchive::open` scans backwards across at most `64 KiB + 22 B` for `PK\x05\x06`, evaluating at most `64` position-consistent candidates, exposes both ordinal (`len`, `is_empty`, `entry_at`) and name (`entry`, `entries`) access, enforces configurable `Limits` (`512 MiB` entry / `2 GiB` total defaults) plus the RFC 1951 `1032×` DEFLATE ratio pre-check before allocation, and verifies IEEE 802.3 CRC-32 (`Error::CrcMismatch`) on every read.
2. **Container sniffing & iterative `.app` unpacking (`src/container.rs`)**: `Container::sniff` classifies by entry set. Within a module container, `abc_modules` extracts `ets/modules.abc` first when present, followed by remaining `*.abc` entries in central-directory order alongside shared `module.json` / `config.json` and `patch.json` buffers. Outer `.app` bundles unpack nested `*.hap` / `*.hsp` entries directly in central-directory ordinal order via an explicit heap workstack bounded by `MAX_CONTAINER_DEPTH = 2` (eliminating `O(K * E)` name re-scans and duplicate-name shadowing).
3. **Zero-`serde`, iterative manifest summary (`src/manifest.rs`)**: `parse_manifest_summary` and `AbcModule::manifest_summary` parse `ManifestSummary { module_name, module_type, is_stage_model }` using an explicit `Vec<Frame>` state machine (`O(1)` call stack), handling UTF-8 BOMs, RFC 8259 escapes + UTF-16 surrogate pairs, and FA (`module.distro.{moduleName,moduleType}`, `is_stage_model: false`) vs. Stage (`module.{name,type}`, `is_stage_model: true`) precedence.

## Key Invariants

- **Total on arbitrary `&[u8]` (zero panics, zero recursion)**: every offset, length, slice, and JSON token calculation uses checked arithmetic and explicit heap workstacks (`O(1)` call stack, verified on `256 KiB` stacks). Corrupt, CRC-mismatched, encrypted, multi-disk, or ZIP64 archives return `Err(abcd_hap::Error)`; malformed manifests return `None`.
- **Path-traversal immunity by construction**: archive entry names are treated strictly as in-memory lookup keys (`Cow<'a, str>`) and provenance labels, never resolved against host filesystem paths.
- **Zero-copy & `O(1)` shared manifests**: valid UTF-8 central-directory names borrow from the input (`Cow::Borrowed`), top-level `STORED` entries return `EntryData::Borrowed`, and owned `module.json` / `patch.json` payloads are coerced once into `EntryData::Owned(Arc<[u8]>)` and cloned in `O(1)` across all `.abc` modules in a container.
- **Specifications & workspace standards**: see [`../design/hap-container.md`](../design/hap-container.md), [`../design/standards.md`](../design/standards.md), and [`../design/decisions.md`](../design/decisions.md).

## Quick Start

```rust,no_run
use abcd_hap::{Container, Limits, ZipArchive, abc_modules, abc_modules_with_limits};

fn inspect_package(bytes: &[u8]) -> Result<(), abcd_hap::Error> {
    let modules = abc_modules(bytes)?;
    for module in &modules {
        let summary = module.manifest_summary();
        println!(
            "{} (via {:?}, {:?}, manifest={:?}): {} bytes",
            module.entry_name,
            module.container_path,
            module.compression,
            summary,
            module.data.as_slice().len(),
        );
    }

    let custom = abc_modules_with_limits(bytes, Limits::DEFAULT)?;
    assert_eq!(custom.len(), modules.len());
    if let Container::Module(archive) = Container::sniff(bytes)? {
        assert_eq!(archive.len(), ZipArchive::open(bytes)?.len());
    }
    Ok(())
}
```

## Verification

Run the crate unit, synthetic container, manifest, and adversarial fuzz-sweep gates:

```sh
./scripts/test-local.sh crate abcd-hap
cargo test -p abcd-hap
cargo clippy -p abcd-hap --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-hap --no-deps
```

To sweep a local directory of wild `.hap` packages end-to-end (`abcd-hap` unpack + `abcd-file` decode):

```sh
ABCD_HAP_WILD_DIR=/path/to/haps cargo test -p abcd-hap --release -- --ignored --nocapture
./scripts/test-local.sh corpus
```
