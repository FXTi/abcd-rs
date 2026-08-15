# vendor 同步体系

## 原则

1. **vendor 文件与上游零 diff**。`*/vendor/` 下的文件是 arkcompiler `runtime_core` master 的逐字节副本，拉取源是 `raw.githubusercontent.com/openharmony/arkcompiler_runtime_core`（OpenHarmony 的 GitHub 官方镜像）。曾使用 `raw.gitcode.com`，但其 WAF 对 GitHub Actions 的境外 IP 一律返回 HTTP 418，导致每日同步全部失败，故切换为镜像源。任何上游改动通过同步脚本整体拉取，**绝不在 vendor 文件上打本地补丁**。
2. **本地适配用 shim / 编译选项，不碰 vendor**。缺失的传递头用 `-include vendor_fixups.h` 注入；重型依赖（logger/securec/zlib/os 抽象/pgo）用独立 shim 头 + include 路径优先级覆盖；行为差异用宏（`-DNDEBUG`、`-DSUPPORT_KNOWN_EXCEPTION`）。
3. **元数据锁定**。每个 vendor 文件的 sha256 记录在 `vendor/.sync-metadata.yml`；`--check-local` 比对实际文件与元数据，任何本地改动都会被 CI 抓到。

## 机制

| 文件 | 作用 |
|------|------|
| `vendor-sync-files.yml` | 本地路径 → 上游路径映射（crate 内） |
| `vendor-sync.rb` | 同步驱动：拉取、diff、写入、重建元数据；`--dry-run` / `--force` / `--check-local` |
| `vendor/.sync-metadata.yml` | `base_url` + 每文件 sha256 |

`vendor-sync.rb` 是这套机制**脚本本体**，与上游保持一致的契约由 CI 保证（见下）。它要求 Ruby ≥ 3.1（Psych 4 的 `YAML.safe_load_file`）；本地若 Ruby 过老，`--check-local` 会不可用——这是预期行为，一致性检查以 CI 的 Ruby 3.2 环境为准，本地构建管线（gen.rb）仍只需 Ruby 2.5+。

注意：映射文件（`vendor-sync-files.yml`）不自动发现上游**新增**的文件——上游引入新依赖头时（如 2026-08 的 `timers.h`），需要人工把新文件加入映射（内容同步后由每日任务自动跟进）。

## CI 中的一致性检查

两条 job 守护契约：

1. **`vendor-check`**：两个 crate 各跑 `vendor-sync.rb --check-local` —— vendor 与元数据 sha256 必须吻合，等价于"与上游锁定版本一致"。
2. **`common-files-consistency`**：跨 crate 共享文件必须逐字节相同——`vendor-sync.rb` 本身，以及 shim（`platform_compat.h`、`securec.h`、`utils/logger.h`）。改共享文件必须两个 crate 同步改，否则 CI 红。

## 日常同步流程（自动化）

`vendor-sync.yml` 每日 00:00 UTC（或手动触发）对每个 crate：

1. `vendor-sync.rb -v --force` 拉上游；
2. vendor 有变化才继续：`cargo build` + `cargo test`；
3. 通过 → 推 `vendor-sync/<crate>/<时间戳>` 分支并开 PR（label: `vendor-sync`）；
4. 失败 → 自动开 issue（已有未关的同类 issue 则只追加评论）。

人工处理路径：GitHub 上对 PR 做 **Rebase and merge**（保持线性历史），然后本地 `git pull origin main` 继续开发。若上游变化破坏构建，issue 里带失败日志链接。
