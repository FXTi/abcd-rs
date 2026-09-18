# Agent Roadmap — abcd-rs 完善计划

> 状态表随工作推进更新。规则见 MEMORY.md「Agent collaboration」节。
> 编排：orchestrator（kimi-coding/k3）派发任务卡；worker（kimi-coding/k3）执行有界任务；
> 一切产出经四道门禁（fmt → workspace tests → 定向测试 → 逐行 diff 复审）后方可落盘。

## 阶段总览

| 阶段 | 内容 | 状态 |
|------|------|------|
| Phase 0 | Bridge/封装层全面审计（完整性/清爽/漂亮） | **进行中** |
| Phase 0.5 | 审计 findings 的 P0/P1 修复批 | **完成（12 commits：ff092bb…81d3b71）** |
| Phase 1 | Lower 正确性旧账（out-of-SSA 破环、val_reg 溢出槽、lower 实体重定位通道） | 未开始 |
| Phase 2 | VM oracle 证据链（corpus_lower_oracle → 1119 passed fixture 全量） | 未开始 |
| Phase 3 | P1 漏洞（参数所有权三连修、encode_debug_info 作用域、SSA trivial-phi） | 未开始 |
| Phase 4 | 证据升级（真实 9/11 读验证、pandasm 逐指令对照） | 未开始 |
| Phase 5 | 清扫（死依赖、-sys README、panic 路径）+ FormatProfile 评估 + IR v0.2 决策点 | 未开始 |

## Phase 0 任务登记

| # | 任务 | 执行者 | 状态 |
|---|------|--------|------|
| 0.1 | 基线 `cargo test --workspace --offline` | orchestrator | **完成（2026-09-18，exit 0）** |
| 0.2 | abcd-isa-sys + abcd-isa 审计 | worker A (k3) | **完成**（3 P0 全部经 orchestrator 运行时探针证实：invalid opcode abort exit 134×2、Imm(300)→44 静默截断） |
| 0.3 | abcd-file-sys 审计 | worker B (k3) | **完成**（4 P0：file_size 未校验、element_size 未校验、ARRAY_* cb 丢失、LNP 无界解析降级 P2） |
| 0.4 | abcd-file 封装层审计 | worker C (k3) | **完成**（5 P0 / 多 P1,P2；orchestrator 已独立复核三条：嵌套 LA 句柄错位实锤、参数注解 decode 零覆盖实锤、read_class_name lossy 实锤） |
| 0.5 | 横切机械检查（死表面/重复文件/护栏/回调约定） | worker D (k3) | **完成**（报告 /tmp/workerD_report.md；orchestrator 复核修正：表 1 有 14 个函数指针假阳性，真实死表面 isa 25 + abc 83 = 108/324；表 3 护栏结论已独立验证一致） |
| 0.6 | findings 复核、去重、定级 | orchestrator | **完成**（4 份报告全量复核；14 个假阳性修正；3 个 P0 运行时探针证实；worker D 的 5 项/B 的 4 项/A 的 2 项/C 的 3 项存疑全部裁决） |
| 0.7 | 产出 design/review-bridge-wrapper.md，维护者对齐 | orchestrator + maintainer | **报告已产出，待维护者过目** |

## Phase 0.5 任务登记（范围由维护者 2026-09-18 划定）

P0 全 10 条；P1 的 ⑪⑫⑬⑭⑯⑱⑲；⑰ 参数注解扩模型；CI（㉒）不动；README 重写（⑳㉑）与 ⑮ 回调文档进 Phase 5 清扫批。

| # | 任务 | 执行者 | 状态 |
|---|------|--------|------|
| 0.5.1 | #1 decode 无效 opcode abort → 生成 isa_is_valid_opcode + bridge 预检 + 回归测试 | orchestrator | **完成**（ff092bb；探针实证 exit 134→Err(InvalidOpcode(0))） |
| 0.5.2 | #2 encode 操作数越界静默截断 → dispatch 范围检查 + EncodeError + 回归测试 | orchestrator | **完成**（99120c6；探针实证 Imm(300) 不再截断为 44，改报 OperandOutOfRange） |
| 0.5.3 | #3 file_size>len 拒绝 + #10 element_size 白名单 + #4 ARRAY_* cb + ⑬ LiteralTag static_assert | worker E (k3) | **完成**（ce9c25e；orchestrator 逐行复审 diff 通过，7/7 测试绿） |
| 0.5.4 | #5 debug 作用域 + #8 嵌套 LA 句柄 + #9 MUTF-8 字符串 + ⑯ class_name 无损/删 SendSync + ⑱ panic 改错误 | worker F (k3) | **完成**（9f10556；orchestrator 复审 + 全 workspace 复验绿；新发现 F-new-1 已登记 review 文档） |
| 0.5.5 | ⑪⑫ FFI 护栏（isa_bridge 59 + builder 75）+ ⑯ abc_foreign_item_name_off | worker H (k3) | **完成**（1134bba；orchestrator 抽查 + 复验通过；裁决：新增 ISA_EMIT_INTERNAL_ERROR(-5)） |
| 0.5.6 | #6/#7 注解静默写 0 改错误 + ⑲ tag 字符/is_entity_array_tag 走 AVT + ⑯c decode.rs 换 abc_foreign_item_name_off | worker F 延续 | **完成**（f20d7e0；含 decoy 防 handle-0 误通过的回归设计；F-new-2 登记） |
| 0.5.7 | ⑲ emitter.rs 常量走 sys、MethodHandleType bindgen 导出 + annotation.rs 引用、AVT 弱钉注释 | worker G (k3) | **完成**（333268a；orchestrator 复审 + 独立复验通过） |
| 0.5.8 | ⑰ 参数注解扩模型 | worker G + worker F | **完成**（9139631、9e5ec81、81d3b71；契约：runtime 折叠进 compile-time，与 #9 先例一致） |
| 0.5.9 | 全量验证 + 报告状态列更新 + 逐 commit | orchestrator | **完成**（51 套件绿 + 语料 4/4 绿；review 文档 fix log 已更新） |

## 审计纪律

- 审计期间 abcd-isa-sys / abcd-isa / abcd-file-sys / abcd-file 冻结功能性改动（允许新增测试文件）。
- findings 必须有 file:line 证据；不接受无指向的结论。
- 修复走项目既有评审流程：逐 commit + 回归测试 + design 状态列更新。
