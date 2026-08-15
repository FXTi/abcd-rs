# CI/CD 设计

## Job 清单与理由

| Job | 内容 | 为什么存在 |
|-----|------|-----------|
| `fmt` | `cargo fmt --all -- --check` | 全仓格式门槛，`-D warnings` 之外的第二道门 |
| `vendor-check` | 两 crate 跑 `vendor-sync.rb --check-local` | vendor 与上游锁定版本一致（见 vendor-sync.md） |
| `common-files-consistency` | 跨 crate 共享文件 diff 校验 | 共享文件漂移检测 |
| `build` | ubuntu / macos / windows 三平台 `cargo build` + `cargo test` | FFI + 代码生成管线的跨平台门槛（Ruby 代码生成、C++ 编译、MSVC shim） |
| `coverage` | cargo-llvm-cov → Codecov | 覆盖趋势（build.rs 在 `CARGO_LLVM_COV` 下给 C++ 插桩） |

全局 `RUSTFLAGS: "-D warnings"`——警告即失败。刻意**不加** actions/cache（ci.yml 内有注释说明：workspace 小，缓存带来的陈旧产物/配额问题多于收益）。

## 为什么没有 release job

第一代的 `release` job 构建 5 目标静态 `abcd` 二进制（musl 双架构 via cross、macOS 双架构、Windows MSVC+mimalloc）。第二代是**纯库 workspace**（无二进制 target），该 job 连同 `Cross.toml` 一并移除。

第二代的分发形态是 **crates.io**（每个 crate 的 `Cargo.toml` 已带 keywords/categories/license/description）。未来需要时补一个 `cargo publish` 工作流（tag 触发 + `cargo publish --dry-run` 门槛），而不是恢复二进制发布。

## vendor-sync 自动化

见 vendor-sync.md：每日 cron 同步上游 → 构建测试 → 自动 PR；失败自动 issue。这依赖 GitHub 仓库上的 Actions（分支推送 + PR/issue 权限），是"上游更新 → rebase PR → pull 本地"工作流的基础。

## 测试约定

- 所有测试用合成字节码/Builder 构造，**不依赖 `modules.abc`**（该文件不入库）。
- 已知失效测试用 `#[ignore]` 并注明原因（如 `encode_roundtrip` → C++ dedup 崩溃）。
- 对 ISA 数据的事实性断言（如 `SUSPEND`/`CALL` 标志未分配给任何指令）以 regression 测试固化，ISA 变动时由测试显式提醒更新。
