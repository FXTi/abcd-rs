# abcd-rs 设计文档

ArkCompiler ABC 字节码 Rust 工具链（第二代）的设计文档。全部为 Markdown，与代码同仓库维护。

## 索引

| 文档 | 内容 |
|------|------|
| [overview.md](overview.md) | 总体架构：定位、crate 分层、数据流、版本分层、当前状态 |
| [isa.md](isa.md) | ISA 层：代码生成管线、Bytecode 枚举、解码/编码、分类与版本 API |
| [file-format.md](file-format.md) | ABC 容器层：文件布局、accessor/bridge 设计、builder、shim 策略 |
| [ir.md](ir.md) | SSA IR：lift / opt / lower 全链路设计、寄存器分配、论文依据 |
| [vendor-sync.md](vendor-sync.md) | vendor 同步体系：零 diff 原则、元数据锁定、一致性检查 |
| [ci.md](ci.md) | CI/CD：job 设计理由、发布形态 |

## 一句话管线

```
.abc ──decode──▶ abcd-isa ──▶ abcd-file ──lift──▶ abcd-ir (SSA) ──opt──▶ ──lower──▶ abcd-file ──encode──▶ .abc
```
