# abcd-hap

Pure-Rust, in-memory, unpack-only reader for OpenHarmony and HarmonyOS application containers (`.hap`, `.hsp`, `.app`, `.hqf`).

## Purpose & Layering Contract

`abcd-hap` sits at the container ingress edge of the `abcd-rs` workspace, turning raw application package bytes (`&[u8]`) into extracted ArkCompiler `.abc` payloads and manifest slices without touching the filesystem or invoking C/C++ code.

- **Zero-C, pure-Rust dependency footprint**: runtime dependencies are strictly [`miniz_oxide`](https://crates.io/crates/miniz_oxide) (raw DEFLATE inflation) and [`thiserror`](https://crates.io/crates/thiserror).
- **Strict upward-free layering**: `abcd-hap` has zero runtime dependency on `abcd-isa`, `abcd-file`, `abcd-ir`, or any analysis crate (`abcd-file` appears only in `[dev-dependencies]` for end-to-end integration tests).
- **Unpack-only in-memory boundary**: callers pass `&[u8]` and receive `AbcModule<'_>` payloads (`EntryData::Borrowed(&[u8])` for top-level `STORED` entries, `EntryData::Owned(Vec<u8>)` for `DEFLATE` or nested `.app` entries) ready for `abcd-file` decoding.

## Container & Security Architecture

OpenHarmony packages are ZIP archives in the restricted dialect produced by `developtools_packing_tool` (single-disk, unencrypted, 32-bit classic ZIP, methods `STORED` = 0 and `DEFLATE` = 8, optional APK-style signing block immediately before the central directory):

1. **Backward EOCD scan & central-directory consistency**: `ZipArchive::open` scans backwards across at most `64 KiB + 22 B` for `PK\x05\x06`. A candidate EOCD is accepted only if its comment length lands exactly on EOF *and* its declared central directory (`PK\x01\x02` count, byte size, and range before EOCD) walks cleanly from start to end. This neutralizes fake EOCD signatures embedded inside archive comments and ignores opaque signing blocks between the final local entry and the central directory.
2. **Local-header data framing & bounded inflation**: per-entry payload slices are resolved from each entry's local file header (`PK\x03\x04`) using local `name_len` + `extra_len`, while `DEFLATE` streams are inflated via `decompress_to_vec_with_limit` capped at the declared `uncompressed_size` and verified for exact output length.
3. **Content-driven classification & `.abc` enumeration order**: `Container::sniff` classifies by entry set rather than file extension. Within any module container (`.hap`, `.hsp`, `.hqf`), `abc_modules` extracts `ets/modules.abc` first when present, followed by all remaining `*.abc` entries (case-insensitive suffix) in central-directory order — covering per-ability Stage layouts (`ets/**/*.abc`), legacy FA layouts (`assets/js/**/*.abc`), and arbitrary `.abc` paths — alongside container-level `module.json` (or fallback `config.json`) and `patch.json`.
4. **Depth-bounded `.app` unpacking with provenance**: outer `.app` bundles containing `*.hap` / `*.hsp` entries are inflated and unpacked recursively up to `MAX_CONTAINER_DEPTH = 2`, recording the outer-to-inner archive chain in `AbcModule::container_path` (for example `["entry.hap"]`) and rejecting deeper `.app`-in-`.app` nesting.

## Key Invariants

- **Total on arbitrary `&[u8]` (zero panics)**: every offset, length, and slice calculation uses checked arithmetic and checked indexing; `#![cfg_attr(not(test), deny(clippy::unwrap_used))]` is enforced across non-test code. Truncated, corrupt, encrypted, multi-disk, or ZIP64 inputs deterministically return `Err(abcd_hap::Error)`.
- **Path-traversal immunity by construction**: archive entry names are treated strictly as in-memory lookup keys and provenance labels (`String`), never resolved against host filesystem paths.
- **Zero-copy preservation for top-level `STORED` payloads**: `STORED` entries in top-level `.hap` / `.hsp` / `.hqf` archives borrow directly from the caller's `&[u8]` (`EntryData::Borrowed`) and expose `Compression::Stored { data_offset }` as an alignment hint.
- **Specifications & workspace standards**: see [`../design/hap-container.md`](../design/hap-container.md) for the authoritative OpenHarmony container format and ZIP dialect specification, and [`../design/standards.md`](../design/standards.md) for workspace-wide safety, determinism, and verification rules.

## Quick Start

```rust,no_run
use abcd_hap::{Container, ZipArchive, abc_modules};

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

    // Low-level container sniffing and raw ZIP central-directory inspection:
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
