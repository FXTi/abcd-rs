# Agent Roadmap — abcd-rs 完善计划

> 状态表随工作推进更新。规则见 MEMORY.md「Agent collaboration」节。
> 编排：orchestrator（kimi-coding/k3）派发任务卡；worker（kimi-coding/k3）执行有界任务；
> 一切产出经四道门禁（fmt → workspace tests → 定向测试 → 逐行 diff 复审）后方可落盘。

## 阶段总览

| 阶段 | 内容 | 状态 |
|------|------|------|
| Phase 0 | Bridge/封装层全面审计（完整性/清爽/漂亮） | **完成（2026-09-18，报告 design/review-bridge-wrapper.md）** |
| Phase 0.5 | 审计 findings 的 P0/P1 修复批 | **完成（12 commits：ff092bb…81d3b71）** |
| Phase 1 | Lower 正确性旧账（out-of-SSA 破环、val_reg 溢出槽、lower 实体重定位通道） | **完成（2026-09-19，4 commits：30d254a/0620a12/99e5a52/793e234）** |
| Phase 2 | VM oracle 证据链（corpus_lower_oracle → 1119 passed fixture 全量） | **进行中** |
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

## Phase 1 任务登记（2026-09-18 开工）

orchestrator 静态分析确认的三个 bug 机制（worker 需在代码中复核）：

- B1 条件前驱 phi 拷贝：`layout.rs` 把 `(pred, succ)` 拷贝插到 pred 终结指令前，对该前驱的所有后继一视同仁——CondBranch 前驱的两条边拷贝在两条路径上都执行。
- B2 槽位级并行拷贝：`regalloc.rs` 的 `resolve_parallel_copies` 在 Value 空间排序/破环，但 coalescing 后不同 value 可共享寄存器，槽位级 hazard/cycle 被漏检（值层无环 ≠ 槽位层无环）。
- B3 isel acc 溢出读错：`isel.rs` 的 `val_reg` 在 `ensure_acc` 的 `Lda` 之后才 `Sta` 溢出 Acc 色寄存器操作数，溢出的已是被覆盖的 acc；且溢出槽在 0xfff0 高位区，超出任何合理帧声明。

| # | 任务 | 执行者 | 状态 |
|---|------|--------|------|
| 1.1 | B1+B2+B3 红色回归测试（手工构造 RegAlloc/IselResult 驱动 layout/isel + 迷你字节码模拟器断言语义；`#[ignore]` 保持主线绿） | worker P1-T1 (k3) | **完成**（30d254a；orchestrator 逐行复审 + 独立复验 4 条断言红色输出一致；Mov 操作数序对 vendor isa.yaml 签名核验无误） |
| 1.2 | B1+B2 修复：槽位级并行拷贝解析 + 每函数显式预留临时寄存器（溢出报错，禁 saturating）+ 条件边 trampoline 插入 | worker P1-T2 (k3) | **完成**（0620a12；orchestrator 逐行复审 + 独立复验：55 套件绿、3 条红转绿、e2e 循环交换测试绿、INVALID/saturating 清除 grep 实证、sub2/greater 语义对 vendor sig 核验） |
| 1.3 | B3 修复：溢出槽移入声明帧（spill-before-ensure_acc）；未分配 value 改硬错误 | worker P1-T3 (k3) | **完成**（99e5a52；orchestrator 复审：materialize_operands 顺序正确、ThrowUndefinedIfHole 顺手修复对 vendor sig `acc: in:top` 核验属实并批准、55 套件绿、3 条 B3 测试绿、grep 证据干净） |
| 1.4 | lower 实体重定位通道：`to_method_body` 产出 `abcd_file::MethodBody`（EntityTrace 溯源 + entity_offsets 恒等映射 + LA 索引反查），复用 `Builder::relocate_code_id` 零改动 | worker P1-T4 (k3) | **完成**（793e234；orchestrator 复审 + 独立复验：57 套件绿、in-suite 4 测试绿、语料 opt-in 18/18 真实 encode+重定位路径通过） |

Phase 1 复审中新登记（不进本期范围）：

- B4：acc-as-color 模型不跟踪物理 acc 被 `Lda` 覆盖——Acc 色的 live-through value 若跨越一条发射 `Lda` 的指令，其物理内容被杀，后续 `ensure_acc` 无操作假设即失效。属寄存器分配建模缺口（修复≈在 liveness 上叠加 acc-clobber 约束，或 IR v0.2 重新建模 acc），登记进 Phase 3 或 v0.2 决策点，由维护者定夺。

## Phase 2 任务登记（2026-09-19 开工）

| # | 任务 | 执行者 | 状态 |
|---|------|--------|------|
| 2.1 | corpus_lower_oracle：decode→lift→(optimize)→lower→to_method_body→encode 全链路重写 passed fixture，写盘 + `compare-rewritten-corpus.py` VM 对照；算术用例先行，lift-only 与 lift+optimize 分开报告 | worker P2-T1 (k3) | **完成**（f4c68f1；36/36 重写成功 0 skip；VM oracle 0/18——失败签名两种：9/11 NaN（参数 ABI 已知限制），12+ SIGSEGV（新发现 B5）） |

Phase 2 新发现（worker P2-T1，orchestrator 已核实 lift/mod.rs:192）：

- B5：`lift/mod.rs` 用 `method.arg_types.len()` 播种 `param_count`，但 12.0.x+ 文件无 proto shorty（格式事实 #A7）→ arg_types 为空 → IR param_count=0 → lowered 帧 num_args=0，而调用方仍按原 num_args 压参 → VM 越帧读写 → SIGSEGV。修复方向：param_count 改从 code header 的 num_args 播种（arg_types 仅在有 shorty 的版本提供类型信息）。**B5 + 参数 ABI 顶槽问题是 VM oracle 通过的前置条件，Phase 3 参数所有权三连修需提前。**

| 2.2 | 参数 ABI 端到端修复（B5 num_args 播种 + entry 参数播种消空 phi + copy-in prologue + param_values 权威身份）| worker P2-T2 (k3) | **完成**（900a39c；VM oracle 0/18→lift 18/18 + opt 18/18；orchestrator 复审 12 文件 diff + 独立复现红色（3 失败签名一致）+ 独立 oracle 复跑全绿） |
| 2.3 | 全量 VM oracle：1119 个 passed fixture 双变体重写 + 对照 | worker P2-T3 (k3) | **完成**（cae3712；重写 lift 1011/108skip、opt 1029/90skip；VM lift 390/1011、opt 462/1029；orchestrator 独立抽验：默认模式 18/18 兼容、disasm abort/wide-call/object-spread 三簇首验一致） |

## Phase 3 任务登记（由 P2-T3 全量 oracle 数据重排，2026-09-19）

原 Phase 3 范围（参数所有权三连修）已在 2.2 提前消化大半；剩余 SSA trivial-phi、dominance、string-pool 所有权、exception CFG。以下按 P2-T3 数据登记失败簇（lift 390/1011、opt 462/1029）：

结构性（encode/lower skip 或输出畸形，确定性高、根因少，优先）：

| # | 簇 | 规模 | 现状 |
|---|----|------|------|
| S1 | MethodId 重定位失败 "cannot relocate code entity: MethodId index N"（class-accessors×9 + newtarget-this×9 + lexicalEnv×36） | 54/变体 skip | 待诊断 |
| S2 | wide-call encode "operand out of range for the instruction encoding" | 18 skip | 待诊断 |
| S3 | object-spread lower-untraceable:StringId（func_main_0 raw 0x7-0x9 不在 entity_offsets） | 18 skip | 待诊断 |
| S4 | ark_disasm 'This line should be unreachable' abort——我们 encode 出的字节码让上游反汇编器崩溃（module-exports×12 + test-namespace×12 + test-constant-propagation×12） | 36 VM 失败 | 待诊断（严重：输出畸形） |
| S5 | 13.0.1.0-only abort 'F/pandafile: Invalid span offset'（module-exports/test-namespace/test-constant-propagation×6） | 18 VM 失败 | 待诊断（疑似 debug LNP span，版本特定） |
| S6 | ~~MultipleAccOperands（fusion 路径）~~ **根因已纠正**：regalloc 活性分析漏 try→handler 异常边（try 体以 Throw/Unreachable 结尾时 live-out 为空）→ handler 读取的值互不干涉 → 全染 Acc → handler 自己的 Add 触发硬错误；失败函数里根本没有 CondBranch。fusion 三重不健全是潜伏问题（非语料触发器）一并修复 | 18 skip | **已修（9dad2cb，见 3.2）** |

VM 语义簇（需逐簇拆根因）：

| # | 簇 | 规模（lift/opt） | 现状 |
|---|----|------|------|
| V1 | 错值 stdout-diff 大簇（array-index/bitwise/numeric/bigint/property-ops/call-shapes/control-flow/decrement/literals/symbol/exception-finally/for-in 等） | 268/204 | 混合族：B4 acc-clobber + vreg-hole 空 phi + 字面量数组缺口 + call-shapes NaN（新触发点） |
| V2 | iterator/generator/destructuring exit 255 'undefined' 抛出 | 128/? | 疑似 vreg-hole + 迭代器/生成器语义缺口 |
| V3 | NewTarget undefined 族（proxy×18、typed-array×18） | 36 | NewTarget 未穿透 lowered 构造调用 |
| V4 | optional-chain SIGSEGV | 18/12+6 | 新崩溃签名（不同于已修的参数 ABI SIGSEGV） |
| V5 | class heritage 'TypeError: parent class is not constructor'（super-properties、test-deault/explicit-constructor） | 54/0 | opt 变体全绿→lift 的 class 定义路径缺陷 |
| V6 | opt 回归：test-branch-elimination 18/18→0/18（stdout 'bad'，疑似 SCCP 过折叠）；for-in 0→timeout 死循环 | 各 18 | 优化器语义 bug，优先于继续扩 opt 覆盖 |
| V8 | 新暴露（S1 解封后达 VM）：class-accessors lift 'Object is not callable'、opt 'class constructor cannot called without new'；newtarget-this 同类 | 36×2 | 类/构造器语义簇，待诊断 |
| V7 | template/tagged-template 'Cannot convert UNDEFINED to JSObject' / 'Cannot load property of null' | 36 | 疑似 tagged-template 字面量数组 strings 缓存 |

| 3.1 | 结构性簇诊断（S1-S5） | worker P3-T1 (k3) | **完成**（只读；S4/S5 同根因=abcd-file 不建模 module record（_ESModuleRecord 字段写回悬挂偏移 + ≤12.x 伪 LA），lowering 洗清——orchestrator 已独立实证恒等重写即损坏；S1=string_entities 名字键撞名（首录者胜）+ 静默错方法双胞胎 N2；S2=wide.callrange 未选择 + sta/lda 无 wide 形需低位 scratch；S3=copydataproperties 被建模成合成名 StoreProperty；新登记 N1-N6） |
| 3.2 | S6 修复：异常边活性 + handler live-in 禁染 Acc + fusion 三前提门禁 | worker P3-T2 (k3) | **完成**（9dad2cb；worker 探针纠正 orchestrator 根因——真身是异常边活性洞，fusion 为潜伏不健全；orchestrator 独立复现红色 4 失败 1 钉住、直方图 lift 1011→1029/lower-other 18→0） |
| 3.3 | S3 修复：copydataproperties 专属 InstData + lift/isel 臂（含 deprecated 形） | worker P3-T3 (k3) | **完成**（86f810a；附纠正：旧 lift 臂操作数角色与 vendor 相反，已对 sig+pandasm 实证修正；orchestrator 干净 worktree 独立复验：61 套件绿、直方图 untraceable 18→0、object-spread VM 18/18） |
| 3.4 | S4+S5 修复：abcd-file 建模 module record（FieldValue::ModuleData/LiteralArrayRef + 桥接 module-data 写路径 + ScalarValueItem ID 引用自动重定位）；identity 证据面扩到 module 用例（N6） | worker P3-T4 (k3) | **完成**（158ee23+312d960；orchestrator 独立实证：恒等重写 module-exports 9.0.0.0 从 disasm abort/VM FATAL → VM 打印 42 exit 0；72 fixture disasm 净、54/54 VM 过、62 套件绿；新登记 N7 moduleRequestPhaseIdx blob、N8 typeSummaryOffset 存疑） |
| 3.5 | S1+N2 修复：DefineFunc/DefineMethod/DefineClassWithBuffer 携带 method_offset 作身份；kind 限定 EntityTrace；to_method_body 校验 all_methods 成员；inline 改 offset 匹配 | worker P3-T5 (k3) | **完成**（740611b；红色实证 S1 encode 报错 + N2 静默错方法 [145,145]vs[145,178]；orchestrator 复验：直方图 encode 72→18（仅剩 S2）、重写 1047→1101、算术基线 18/18 不退；新暴露 V8：class-accessors/newtarget-this 达 VM 但语义失败） |
| 3.6 | S2 修复：低位共享参数窗口 + wide 形选择 + 5 低位 scratch 中转（N4 一并消灭） | worker P3-T6 (k3) | **完成**（b90bc00；设计变更批准：窗口低位预留而非帧顶——300 参数两两干涉必超 255，与上游 es2abc 输出一致；orchestrator 独立复验：直方图清空 1119/1119、wide-call 18/18×2、全量 VM lift 516/opt 636 与 worker 一致；新登记 N9 CreateObjectWithExcludedKeys 同类连续假设） |

**结构性簇 S1-S6 全部关闭（2026-09-19）**。剩余：V 族语义簇（V1-V8）、B4、vreg-hole、N7/N8/N9、SSA trivial-phi、dominance/string-pool/exception CFG 复审。

| 3.7 | vreg-hole 修复：Braun 基例 preds.is_empty() → 惰性共享帧初值常量（vreg=undefined / acc=hole） | worker P3-T7 (k3) | **完成**（2972495；vendor 纠正：vreg 初值是 undefined 不是 hole——orchestrator 用语料 NaN 签名 corroborate；VM 层零翻转（124 例失败另有根因），修复立足 SSA 合法性；0/1119 零元 phi；orchestrator 复验门禁+直方图 1119/0；新登记 N17 种子常量的 B4 残余暴露 + MCS/acc_score 不一致观察、N18 无前驱死 catch 块） |
| 3.8 | V 族诊断（V3/V4/V8） | worker P3-T8 (k3) | **完成**（只读；orchestrator 已独立实证 N10：静态 compute_rpo 反转逻辑 + 动态 exception-finally 反汇编 handler 在函数 pc 0） |
| 3.9 | N10 修复：compute_rpo 先反转可达后序再追加未访问块 | worker P3-T9 (k3) | **完成**（ff23195；orchestrator 独立复验：红色 2 失败签名一致、字节稳定守卫通过、lift oracle 516→575（+59，零回归，两跑一致——worker 报 571，差 4 例归因环境噪声，双方翻转族完全一致：lexicalEnv/destructuring catchall 族）；opt 不变（N11 掩盖）） |
| 3.10 | Construct 调用种类 | worker P3-T10 (k3) | **完成**（083db56；orchestrator 复验：66 套件绿、proxy/newtarget-this 18/18×2 独立复跑一致；vendor 证据链核实（ctor=range 首寄存器、argc 含 ctor、ctor 兼 newTarget）；inline 显式跳过 Construct 决策批准；lift 615/opt 696；新登记 N19 typed-array 残值、N20 管道非确定性） |
| 3.11 | N20 确定性审计+修复 | worker P3-T11 (k3) | **完成**（16dc8ff；三处根因皆字节级：layout edge_codes HashMap→BTreeMap、decode LA extras HashSet→排序、lift 封印序→块序；orchestrator 独立复验：3 次重写两两 diff=0、67 套件绿、新基线 lift 618/opt 696 复跑一致。遗留 wart 登记：layout legacy 兜底路径对 handler 边拷贝的语义假设——handler 当前无 CFG 前驱故不可达，N13 落地时须重审） |
| 3.12 | N11 修复：augmented_succs 共享 + 异常中性合并守卫 | worker P3-T12 (k3) | **完成**（606cdcd；orchestrator 复验：红色 5 失败复现、lift 树与确定性基线逐字节一致、opt 666 复跑一致。-30 为**诚实回归**：unused-ldhole×18 是 N13 族被 N11 删 handler 掩盖的旧失败、iterator-close×12 是 N21 wart 活化——靠删代码换来的通过被取消，证据完整性为正。新登记 N21（P1）：handler 边 phi 拷贝的 legacy 内联放置在 CondBranch 前驱上腐蚀正常边值） |
| 3.13 | N21+N13 异常边建模：ValueDef::ExceptionParam + handler 入口 Sta 序幕 + phi 结果钉槽 + 入值写穿透存储 + legacy 内联删除改硬错误 | worker P3-T13 (k3) | **完成**（0270f9b；两条批准修正 + 一条新修正（def-block→per-entry 放置，destructuring 的 vreg 重绑定形态证伪纯定义点放置）全部成立；orchestrator 独立复验：69 套件绿、7/7 测试、双跑字节一致、delta 集合恰为 339 try fixture×2、lift 660(+42)/opt 696(+30) 零回归、翻转族精确吻合；新登记 N22 异常值活性保守回传 +1 寄存器） |
| 3.14 | 空跳转 phi 守卫 | worker P3-T14 (k3) | **完成**（4a6d6ae；守卫条件=汇聚边 phi 值不等则拒绝消块，同值照常合并；orchestrator 复验：红色 2 失败 1 钉住复现、lift 树零变化、opt 差集恰 6 文件、opt 702 复跑一致；merge_single_succ_pred 审计结论：不同 bug 类，无需加守卫；新登记 N23 SCCP 折叠留陈旧 phi 条目——无活失败） |
| 3.15 | N14 generator 三件套建模（Getresumemode 误映射 + acc 操作数丢失；opt SIGSEGV 机制已钉死） | 待定 | 未开始（下一棒） |

P3-T8 诊断结论（2026-09-19，全部有 file:line + 运行时证据，oracle  harness 无幻影）：

- **N10（P0）**：`compute_rpo`（analysis/mod.rs:37-47）把不可达的 catch handler 追加在 post_order 末尾再整体反转 → handler 块排在 entry 之前 → layout 平铺后 handler 落在函数 pc 0，调用即进 handler。阻塞全部 8 个含 catchall 的用例族（144 fixture）。修复：先反转可达后序，再追加未访问块。
- **缺 Construct 调用种类**（V3+V8-opt 共同根因）：CallKind 无 Construct；lift 把 Newobjrange 映射成普通 Call → `new` 变普通调用，NewTarget 未定义（proxy/typed-array 36，class-accessors/newtarget-this opt 36）。
- **N11（P1）**：opt `remove_unreachable_blocks`（dce.rs:429-475）只走终结指令后继 → 静默删除 catch handler 并修剪 try_regions——异常路径被删。
- **N12（P2）**：ThrowIfSuperNotCorrectCall lift/isel 双重损坏（操作数捏造、acc 输入丢失、kind 硬编码 0）。
- **N13（P1）**：handler 入口 acc（捕获的异常对象）从未在 lift 播种 → handler 里的 throw 重抛的是陈旧值。
- **N14（P1）**：generator 三件套建模错误——Getresumemode 被 lift 成 ResumeGenerator；SuspendGenerator 丢 acc 里的 yield 值；ResumeGenerator/GetResumeMode 丢 acc 里的 genobj。opt 变体 SIGSEGV 机制已钉死（DCE 删 yield 值 → resume 后 acc=undefined → 野指针解引用）。
- **N15（P3）**：DefineClassWithBuffer 丢 imm2（_count）——运行时忽略，仅字节差异。
- **N16（P3）**：Newobjapply ↔ CallKind::Apply arity 重载往返脆弱。
- V4 更正：optional-chain 的 SIGSEGV 数据已过时（S2/S6 时代已愈）；现行失败 = 空跳转 phi 输入丢失（dce.rs:303-318 按前驱去重模型无法表达两条汇聚边的不同值——MEMORY.md 已知风险的具体语料实例）+ N14。
- B4 从"潜伏"升级为**实锤**：class-accessors lift 18 例的 acc 覆盖链完整钉出（lda.str "value" → ldundefined 覆盖 → definegettersetterbyvalue 拿到 false；prototype 覆盖 → stglobalvar B = prototype → 'Object is not callable'）。
- 修复顺序（性价比）：N10 → Construct → N11 → 空跳转 phi 守卫 → N14 → N12+N13 → B4（大）。

## 审计纪律

- 审计期间 abcd-isa-sys / abcd-isa / abcd-file-sys / abcd-file 冻结功能性改动（允许新增测试文件）。
- findings 必须有 file:line 证据；不接受无指向的结论。
- 修复走项目既有评审流程：逐 commit + 回归测试 + design 状态列更新。
