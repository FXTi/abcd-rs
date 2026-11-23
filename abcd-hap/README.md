# abcd-hap

Pure-Rust, in-memory, unpack-only reader for OpenHarmony / HarmonyOS application containers (`.hap`, `.hsp`, `.app`, `.hqf`).

Every OpenHarmony package container is a ZIP archive using a restricted dialect produced by `developtools_packing_tool` (`STORED` and `DEFLATE` entries, optional APK-style signing block before the central directory). `abcd-hap` parses the central directory directly from `&[u8]` with zero filesystem I/O and zero dependency on `abcd-file` or `abcd-isa`.

## Features

- **Total on arbitrary bytes**: checked bounds arithmetic throughout; hostile or truncated inputs return `Result::Err(abcd_hap::Error)`, never panics.
- **Zero-copy where possible**: `STORED` entries borrow directly into the caller's `&[u8]` (`EntryData::Borrowed`); `DEFLATE` entries inflate via `miniz_oxide` into `EntryData::Owned`.
- **Stage, FA, and nested `.app` layouts**:
  - Stage model: `ets/modules.abc` + `module.json`
  - FA / multi-module packages: discovers every `*.abc` bytecode entry in archive order alongside `config.json` / `module.json`
  - `.app` / `.appqf` bundles: recurses into nested `.hap` / `.hsp` / `.hqf` archives (bounded by `MAX_CONTAINER_DEPTH = 2`) and preserves `container_path` provenance
- **Signing-block tolerant**: locates the End of Central Directory (EOCD) from the end of the buffer and follows central-directory offsets directly.

## Quick start

```rust,no_run
let bytes = std::fs::read("entry-default.hap").unwrap();
let modules = abcd_hap::abc_modules(&bytes).unwrap();

for module in &modules {
    println!(
        "{} (provenance {:?}): {} bytes",
        module.entry_name,
        module.container_path,
        module.data.as_slice().len(),
    );
}
```

Low-level archive inspection is also available via `ZipArchive::open(&bytes)` and `Container::open(&bytes)`.

See [`../design/abcd-hap-research.md`](../design/abcd-hap-research.md) for the upstream `developtools_packing_tool` research and format details.

## License

Apache-2.0.
