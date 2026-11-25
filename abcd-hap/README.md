# abcd-hap

Pure-Rust, in-memory, unpack-only reader for OpenHarmony and HarmonyOS application containers (`.hap`, `.hsp`, `.app`, `.hqf`).

## Purpose & Layering Contract

`abcd-hap` sits at the container ingress edge of the `abcd-rs` workspace, turning raw application package bytes (`&[u8]`) into extracted ArkCompiler `.abc` payloads and manifest slices without touching the filesystem or invoking C/C++ code.

- **Zero-C, pure-Rust dependency footprint**: runtime dependencies are strictly [`miniz_oxide`](https://crates.io/crates/miniz_oxide) (raw DEFLATE inflation) and [`thiserror`](https://crates.io/crates/thiserror), with `#![forbid(unsafe_code)]`.
- **Strict upward-free layering**: `abcd-hap` has zero runtime dependency on `abcd-isa`, `abcd-file`, `abcd-ir`, or any analysis crate (`abcd-file` appears only in `[dev-dependencies]` for end-to-end integration tests).
- **Unpack-only in-memory boundary**: callers pass `&[u8]` and receive `AbcModule<'_>` payloads (`EntryData::Borrowed(&[u8])` for top-level `STORED` entries, `EntryData::Owned(Vec<u8>)` for `DEFLATE` or nested `.app` entries) ready for `abcd-file` decoding.

## Container & Security Architecture

OpenHarmony packages are ZIP archives in the restricted dialect produced by `developtools_packing_tool` (single-disk, unencrypted, 32-bit classic ZIP, methods `STORED` = 0 and `DEFLATE` = 8, optional APK-style signing block immediately before the central directory):

1. **Bounded backward EOCD scan & central-directory consistency**: `ZipArchive::open` scans backwards across at most `64 KiB + 22 B` for `PK\x05\x06`, evaluating at most `64` position-consistent candidates. Non-empty candidates are `O(1)`-checked for a leading `PK\x01\x02` signature and bounded capacity before walking records, neutralizing fake EOCD comment floods and ignoring opaque signing blocks before the central directory.
2. **Resource `Limits`, bomb pre-checks & mandatory IEEE CRC-32**: `read_entry_with_limits` and `abc_modules_with_limits` enforce per-entry (`512 MiB` default) and cumulative container (`2 GiB` default) caps, reject spoofed `DEFLATE` headers exceeding the RFC 1951 `1032×` theoretical ratio *before* allocating, and verify a pure-Rust IEEE 802.3 CRC-32 (`Error::CrcMismatch`) on every `STORED` and `DEFLATE` read.
3. **Content-driven classification & `.abc` enumeration order**: `Container::sniff` classifies by entry set rather than file extension using allocation-free ASCII suffix matching. Within any module container (`.hap`, `.hsp`, `.hqf`), `abc_modules` extracts `ets/modules.abc` first when present, followed by all remaining `*.abc` entries in central-directory order — covering per-ability Stage (`ets/**/*.abc`) and legacy FA (`assets/js/**/*.abc`) layouts — alongside `module.json` (or `config.json`) and `patch.json`.
4. **Iterative depth-bounded `.app` unpacking**: outer `.app` bundles containing `*.hap` / `*.hsp` entries are unpacked via an explicit heap workstack up to `MAX_CONTAINER_DEPTH = 2` (zero call-stack recursion), recording provenance in `AbcModule::container_path` and skipping resource-only nested `.hsp` / `.hap` siblings while propagating archive corruption.

## Key Invariants

- **Total on arbitrary `&[u8]` (zero panics, zero recursion)**: every offset, length, and slice calculation uses checked arithmetic and bounded heap loops (`unwrap_used = "deny"` in non-test code). Truncated, corrupt, CRC-mismatched, encrypted, multi-disk, or ZIP64 inputs deterministically return `Err(abcd_hap::Error)`.
- **Path-traversal immunity by construction**: archive entry names are treated strictly as in-memory lookup keys (`Cow<'a, str>`) and provenance labels, never resolved against host filesystem paths.
- **Zero-copy fast path**: valid UTF-8 central-directory names borrow directly from the input slice (`EntryMeta::name` as `Cow::Borrowed`), and top-level `STORED` payloads return `EntryData::Borrowed` with `Compression::Stored { data_offset }`.
- **Specifications & workspace standards**: see [`../design/hap-container.md`](../design/hap-container.md) for the authoritative OpenHarmony container format specification, and [`../design/standards.md`](../design/standards.md) for workspace-wide safety, determinism, and verification rules.

## Quick Start

```rust,no_run
use abcd_hap::{Container, Limits, ZipArchive, abc_modules, abc_modules_with_limits};

fn inspect_package(bytes: &[u8]) -> Result<(), abcd_hap::Error> {
    // High-level extraction across .hap, .hsp, .hqf, and nested .app bundles:
    let modules = abc_modules(bytes)?;
    for module in &modules {
        println!(
            "{} (via {:?}, {:?}): {} bytes",
            module.entry_name,
            module.container_path,
            module.compression,
            module.data.as_slice().len(),
        );
    }

    // Custom resource caps and low-level central-directory inspection:
    let custom = abc_modules_with_limits(bytes, Limits::DEFAULT)?;
    assert_eq!(custom.len(), modules.len());
    if let Container::Module(archive) = Container::sniff(bytes)? {
        assert_eq!(archive.entries().count(), ZipArchive::open(bytes)?.entries().count());
    }
    Ok(())
}
```

## Verification

Run the crate unit, synthetic container, and adversarial fuzz-sweep gates:

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
