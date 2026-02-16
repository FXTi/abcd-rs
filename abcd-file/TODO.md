# abcd-file TODO

## 当前状态

abcd-file（原 abcd-parser）目前只支持读取/解析 .abc 文件，且不区分文件格式版本。
需要逐步扩展为完整的 .abc 文件读写库，并支持版本条件化的文件格式差异。

## 版本条件化解析

- [ ] 解析 header 时提取 version 并存入 AbcFile，供后续解析阶段使用
- [ ] 根据版本决定 literal array 存储位置（header 内 vs 独立 region）
  - 参考 `ContainsLiteralArrayInHeader()`：version >= 11.0.2.0 时 literal array 在 header 中
- [ ] 根据版本决定 index header 中是否包含 proto 区域
  - 参考 `file_format_version.h.erb` 中的 `CONTAINS_PROTO_IN_INDEX_HEADER`
- [ ] 根据版本处理 line number program 格式差异
- [ ] 添加版本兼容性检查：解析时验证文件版本在 [minVersion, version] 范围内

## 文件写入支持

- [ ] 设计 AbcFileBuilder API，支持增量构建 .abc 文件
- [ ] 实现 header 写入（magic, version, checksum, offsets）
- [ ] 实现 string table 写入（MUTF-8 编码 + 去重）
- [ ] 实现 class/method/code 写入
- [ ] 实现 literal array 写入（版本条件化位置）
- [ ] 实现 index section 写入（版本条件化 proto 区域）
- [ ] 实现 checksum 计算（Adler32）
- [ ] 与 abcd-isa 的 BytecodeEmitter 集成：接收 emit 产物写入 code section

## 测试

- [ ] 为每个版本条件化分支添加测试用例
- [ ] round-trip 测试：解析 → 重建 → 二进制比对
- [ ] 使用真实 .abc 文件（不同 API level 生成）验证兼容性
