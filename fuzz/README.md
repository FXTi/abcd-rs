# abcd-fuzz

`cargo-fuzz` (`libFuzzer` + AddressSanitizer) targets for `abcd-rs` untrusted-input boundaries:

- `fuzz_hap_container` — `abcd_hap::abc_modules` ZIP/container unpack + inner `abcd_file::decode`
- `fuzz_abc_decode` — `abcd_isa::decode`, `abcd_isa::decode_legacy`, `abcd_file::decode`, `pandasm::emit_file`, and `abcd_lift::lift_file` + `abcd_ir::verify_module`
- `fuzz_pandasm_parse` — `abcd_file::pandasm::parse_file_with_version` (`12.0.6.0` and `24.0.0.0`)

## Running locally

Requires `cargo-fuzz` (`cargo install cargo-fuzz`) and a nightly Rust toolchain:

```sh
cargo +nightly fuzz run fuzz_hap_container -- -max_total_time=60
cargo +nightly fuzz run fuzz_abc_decode -- -max_total_time=60
cargo +nightly fuzz run fuzz_pandasm_parse -- -max_total_time=60
```

CI gates `cargo check --manifest-path fuzz/Cargo.toml --bins` in Tier 1 so API changes never rot the fuzz targets.
