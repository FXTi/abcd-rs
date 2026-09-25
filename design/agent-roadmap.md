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
| Phase 2 | VM oracle 证据链（corpus_lower_oracle → 1119 passed fixture 全量） | **完成（2026-09-20：双变体 VM oracle 1119/1119）** |
| Phase 3 | P1 漏洞 + V 族语义簇 + 优化器正确性 | **完成（2026-09-20，P3-T1…T22；见下方登记）** |
| Phase 4 | 证据升级（真实 9/11 读验证、pandasm 逐指令对照、补 fixture） | **完成**（2026-09-20，P4-T6；orchestrator 复验：逐指令套件 6/6、oracle 1149/1149×2 复跑一致） |
| Phase 5 | 清扫（死依赖、-sys README、panic 路径）+ FormatProfile 评估 + IR v0.2 决策点 | **完成**（2026-09-21，P5-T1+P5-T2；决策简报 design/phase5-decision-briefing.md 待维护者拍板 D1-D4） |

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
| 3.15 | N14 generator 三件套建模 | worker P3-T15 (k3) | **完成**（aa6e786；vendor sig 逐条核验；orchestrator 复验：门禁绿、字节差集恰 36、lift 666/opt 708 复跑一致、18 例 SIGSEGV 清零、生成器剩余 12 例归 B4） |
| 3.16 | N24 oracle 工具链卫生 | orchestrator | **完成**（3883291；标签+finally 清理+客户端超时兜底；默认行为不变、崩溃族跑后容器零残留实证） |
| 3.17 | N12 ThrowIfSuperNotCorrectCall 修复 | worker P3-T16 (k3) | **完成**（cd410e5；kind 语义钉死（0=TDZ 守卫/1=重绑守卫，acc=this）；orchestrator 复验：72 套件绿、差集恰 144、lift 666 零翻转、opt 690 复跑一致；opt -18 为诚实回归——修复前的通过跑的是不可能抛错的空检查，修复后撞上 B4；新登记 N25 ThrowConstAssignment、N26 ThrowUndefinedIfHole 两寄存器形（同类）） |
| 3.18 | **B4：acc-as-cache 重构**——Phase 3 收官战 | worker P3-T17 (k3) | **完成**（7816ccc；orchestrator 复审 tracker 不变式/meet/全臂覆盖 + dabai 门禁 73+29 套件绿 + 本地 oracle 复跑 lift 1026/opt 894 与 worker 完全一致：lift +360 零回归、opt +210/-6（6 例=N27 优化器空 phi 既存 bug，test-namespace/optimized）；B4 是 V1 大簇主根因实锤。新基线：**lift 1026/1119（91.7%）、opt 894/1119（79.9%）**） |

P3-T8 诊断结论（2026-09-19，全部有 file:line + 运行时证据，oracle  harness 无幻影）：

- **N10（P0）**：`compute_rpo`（analysis/mod.rs:37-47）把不可达的 catch handler 追加在 post_order 末尾再整体反转 → handler 块排在 entry 之前 → layout 平铺后 handler 落在函数 pc 0，调用即进 handler。阻塞全部 8 个含 catchall 的用例族（144 fixture）。修复：先反转可达后序，再追加未访问块。
- **缺 Construct 调用种类**（V3+V8-opt 共同根因）：CallKind 无 Construct；lift 把 Newobjrange 映射成普通 Call → `new` 变普通调用，NewTarget 未定义（proxy/typed-array 36，class-accessors/newtarget-this opt 36）。
- **N11（P1）**：opt `remove_unreachable_blocks`（dce.rs:429-475）只走终结指令后继 → 静默删除 catch handler 并修剪 try_regions——异常路径被删。
- **N12（P2）**：ThrowIfSuperNotCorrectCall lift/isel 双重损坏（操作数捏造、acc 输入丢失、kind 硬编码 0）。
- **N13（P1）**：handler 入口 acc（捕获的异常对象）从未在 lift 播种 → handler 里的 throw 重抛的是陈旧值。
- **N14（P1）**：generator 三件套建模错误——Getresumemode 被 lift 成 ResumeGenerator；SuspendGenerator 丢 acc 里的 yield 值；ResumeGenerator/GetResumeMode 丢 acc 里的 genobj。opt 变体 SIGSEGV 机制已钉死（DCE 删 yield 值 → resume 后 acc=undefined → 野指针解引用）。
- **N15（P3）**：DefineClassWithBuffer 丢 imm2（_count）——运行时忽略，仅字节差异。
- **N16（P3）**：Newobjapply ↔ CallKind::Apply arity 重载往返脆弱。
- **N27（P1，P3-T17 登记）**：优化器（SCCP/trivial-phi 类）留下 entries 为空的 phi，其宿主槽位从无写入 → 调用读到帧垃圾——N23 当时"无活失败"，现在有 6 例活失败（test-namespace/optimized opt 变体，B4 重排槽位后从 wrong-benign 变 wrong-fatal）。属 opt 域，下一棒。

| 3.19 | N27 优化器空 phi 修复 | worker P3-T18 (k3) | **完成**（76cb828；双根因：SCCP 折枝留陈旧 phi 条目（N23 关闭）+ merge 重键造空 phi；修复=条目随 pred 删除 + 单前驱 phi 替换而非重键 + verify 结构兜底（可达零前驱 phi 报错，N18 死块豁免）；orchestrator 复验：红色 3/3 远端复现、lift 1026 不变、opt 894→900 精确 +6 零回归。新登记 N28 copyprop "ADCE 会清理"假设的残余风险） **新基线：lift 1026 / opt 900（80.4%）** |
| 3.20 | 诊断（只读）：opt-only 失败族 | worker P3-T19 (k3) | **完成**（scratch 验证 10/10 VM 通过；orchestrator 抽查两声明成立；实际 opt-only 差=126 非 219。编号冲突已重排为 N36-N41） |
| 3.21 | 诊断（只读）：双变体共挂族 | worker P3-T20 (k3) | **完成**（五根因全部 file:line+反汇编+VM 签名三重钉死；orchestrator 抽查 N35/N33/N33 静态证实；登记 N29-N35；预期上限 lift 1119 / opt ~993） |
| 3.22 | 修复批六连（N35→N29→N33→N30→N31+N32→N34，每个一 commit + 红色先行 + vendor 引用） | worker P3-T21 (k3) | **完成**（2b61870/e22962c/4eb28ba/cf19614/d2b9b6a/3a22adf；orchestrator 独立复现终态：**lift 1119/1119（100%）**、opt 993/1119，每检查点零回归；81 套件绿；N32 零翻转字节证明成立。残留观察：stthisbyvalue/stprivateproperty/testin 无语料覆盖——按 vendor 检视修复，Phase 4 补 fixture） **新基线：lift 1119 / opt 993（88.7%）** |
| 3.23 | opt 修复批：N36 双引擎交换 → N37 -0.0 守卫 → N38 SCCP 异常三层+N41 → N39/N40 | worker P3-T22 (k3) | **完成**（65f9704/1999fd4/d7f8533/a797fc1；N36 附带纠正 Shr/Ashr 符号性反转（vendor 验证）；orchestrator 独立复现终态：**lift 1119/1119、opt 1119/1119，双 100%，零失败零缺失**；85 套件绿；每检查点 lift 硬门槛守住） |
- **N25（P2，P3-T16 登记）**：ThrowConstAssignment 同属 N12 类双重损坏——vendor `throw.constassignment v:in:top`（isa.yaml:987-991，acc:none）的寄存器操作数承载变量名字符串值，lift（translate.rs:1516-1528）捏造合成名 `const_assign_N` 并丢弃寄存器操作数，isel（isel.rs:1211-1214）硬编码 `Reg(0)` 占位。
- **N26（P2，P3-T16 登记）**：ThrowUndefinedIfHole 双寄存器形态 opcode 身份损坏——vendor `throw.undefinedifhole v1:in:top, v2:in:top`（isa.yaml:998-1002，acc:none；v1=name，v2=value），lift 捏造合成名 `hole_check_N`，isel 一律重发为**另一条 opcode** `throw.undefinedifholewithname`（0x09，string_id + acc 形态）——往返把寄存器形态换成 acc 形态（N14 getresumemode 同类）。
- V4 更正：optional-chain 的 SIGSEGV 数据已过时（S2/S6 时代已愈）；现行失败 = 空跳转 phi 输入丢失（dce.rs:303-318 按前驱去重模型无法表达两条汇聚边的不同值——MEMORY.md 已知风险的具体语料实例）+ N14。
- B4 从"潜伏"升级为**实锤**：class-accessors lift 18 例的 acc 覆盖链完整钉出（lda.str "value" → ldundefined 覆盖 → definegettersetterbyvalue 拿到 false；prototype 覆盖 → stglobalvar B = prototype → 'Object is not callable'）。
- 修复顺序（性价比）：N10 → Construct → N11 → 空跳转 phi 守卫 → N14 → N12+N13 → B4（大）。

P3-T20 新登记（2026-09-20）：

- N29（P0）：`callruntime.definefieldbyvalue` lift 操作数交换（v1=key/v2=obj 被绑反）——一行修，解锁 tagged-template×18 并解除 template 阻塞。
- N30（P1）：`gettemplateobject` 被建模成 LoadProperty(obj, 0)——template×18 的最终阻塞；tagged-template 的 .raw/缓存语义也有潜伏错误。
- N31（P1）：`starrayspread` 塌缩成单条 StoreProperty 且丢 acc-out——call-shapes×18。
- N32（P1）：isel StoreProperty::ByValue 与 lift Stobjbyvalue/Stthisbyvalue 携带一致的 acc↔v2 置换——双置换今日字节透明，但是地雷（N31 已踩爆）；opt 会看到交换后的 key/value。
- N33（P0）：`getnextpropname` → GetPropIterator 塌缩（注释自认）→ 迭代器套娃 → 堆爆炸 GC abort——for-in×18，最坏的失败形态。
- N34（P2）：私有属性指令族整体未建模（create 丢弃；ld/st/define/testin 塌缩成 ByIndex(0)）——private-field×3。
- N35（P0）：IR 无 LiteralBigInt（ldbigint→LiteralString）——bigint×18。

P3-T19 新登记（2026-09-20；原编号 N29-N34 与 P3-T20 撞号，重排为 N36-N41）：

- N36（P0）：peephole + sccp 折叠引擎对**所有非交换**二元操作数序折叠错误——IR 约定 left=acc/right=reg，但 vendor 语义是 `vreg OP acc`（即 right OP left），两个引擎都按 left OP right 算。覆盖 numeric-operators/bitwise/test-branch-elimination（V6 真身：不是折叠条件错，是这个交换被 SCCP 首轮结构化播种掩盖、copyprop 后暴露）共 54 例 opt 失败。
- N37（P1）：isel `LiteralNumber(-0.0)` 命中 `*n == (*n as i32) as f64` → 误发 `ldai 0`（+0.0）——literals×18（Object.is(-0,0)）；不修 opt 也可经原始 fldai 触发（潜伏 lower bug）。
- N38（P1）：SCCP 异常不健全三层——(i) CFG 遍历只看终结指令（handler 出口边在下游 merge 被忽略→phi 被错误常量替换）；(ii) handler phi 的块尾值对块内抛出点不健全；(iii) Eq/NotEq 折叠经 ToNumber 强转（undefined==undefined 折成 false 改写了 es2abc 的 finally 守卫）。修复件已验证：SCCP 用 augmented_succs + handler phi 强制 Bottom + nullish 规则；peephole 只做保守化（去掉 LiteralNull→0.0）——peephole 的 eq-nullish 折叠被证明不健全，不要加。
- N39（P3 潜伏）：`Bytecode::Not` vendor 语义是**位反**（~acc），lift 标成 LogicalNot——往返掩盖；任何未来 `~常量` 折叠会错。
- N40（P3 潜伏）：peephole StrictEq 用 to_bits 折叠——`0===-0` 错判 false、同位 NaN 错判 true；改成普通 `a == b`。
- N41（P2 潜伏）：peephole as_number 把 LiteralNull 映射成 0.0 → `null==0` 会错折 true。

## 全量发现对账表（2026-09-20 双 100% 时点；每条发现的最终状态，补漏自聊天记录）

| 条目 | 内容 | 状态 |
|---|---|---|
| N1 | _ESScopeNamesRecord 悬挂偏移 | ✅ 修复（312d960，S4/S5 一并） |
| N2 | 静默错方法引用双胞胎 | ✅ 修复（740611b） |
| N3 | DeprecatedSetobjectwithproto 合成名 "__proto__"（无语料覆盖） | ✅ 修复（e9fd5db，P4-T1：专用 SetObjectWithProto{proto,obj}，现代+deprecated 两臂都映射，isel 发当代 opcode；合成往返测试） |
| N4 | range-call 连续寄存器假设 | ✅ 修复（b90bc00） |
| N5 | copydataproperties dst>255 高位风险族 | ✅ 覆盖于 S2 的 u8 审计+scratch 路由 |
| N6 | identity 证据面只有算术 | ✅ 修复（312d960 扩 module 用例） |
| N7 | moduleRequestPhaseIdx blob 同类悬挂（不在 passed 集） | ✅ 修复（71adc56，P5-T2：u32 字段按**字段名**匹配（merge-abc 把它挂在模块自身 record 上，runtime/disassembler 也按名匹配）→ FieldValue::ModuleRequestPhase 结构化解码（无 tag 的 [u32 count][u8 lazy 标志]* blob，vendor ModuleLazyImportFlagAccessor 布局）→ 新受控 bridge writer 重发 + ScalarValueItem ID 自动重定位；blob 偏移与 module blob 一样排除出 tag 化 LA 解码。红色实证：pre-fix 重写把 0xcd4 裸偏移写回，新文件该处是 count=0 的零填充 → 运行时读到零 lazy 标志（lazy 静默变 eager）；post-fix 9/9 fixture（12.0.6.0 lazy_import 三案 ×3 profile）恒等重写快照+标志一致、本地 docker ark_disasm 全 0 退出、字段指向有效新 blob（count=1 flags=[1]）） |
| N8 | typeSummaryOffset 是否偏移存疑 | ✅ 裁决+落地（P5-T2 裁决 + 2026-09-20 维护者拍板硬错误，e8c8446）：**是嵌套文件偏移**（2022-08-18 changelog 第 5 条），但上游无生产者/消费者/语料样本。维护者裁决：decode 遇此字段名即硬错误 `Error::TypeSummaryOffset`（名匹配置于分派首位——上游把字段挂在 _ESModuleRecord 自身，否则被 catch-all u32 臂误路由进 module-data 解码；有钉住测试），消息引 changelog 并请用户上报；永不 warning、永不静默 I32 穿透。red-first 实证（pre-fix 静默 Ok(Some(I32))/None） |
| N9 | CreateObjectWithExcludedKeys 连续键假设+wide 形未选 | ✅ 修复（d5ec683，P4-T1：keys mov 填充共享低位窗口（与 range call 共存取 max），>255 选 wide 形；语料仅 object-spread imm=0，字节不变） |
| N10-N14 | handler pc0 / opt 删 handler / ThrowIfSuper / handler acc / generator 三件套 | ✅ 全修（ff23195/606cdcd/cd410e5/0270f9b/aa6e786） |
| N15 | DefineClassWithBuffer 丢 imm2（仅字节差异） | ✅ 修复（3ed4228，P5-T2：P3-T8 的"runtime 忽略"登记**有误**——vendor 两个现代 handler 都把 imm2 读作 length 并传给 RuntimeSetClassConstructorLength（runtime_stubs-inl.h:1037→1227-1240），imm2 是类构造器的 .length；InstData 建模 count:u16，三条 lift 臂绑定，isel 发真实值。红色：module-exports/class-accessors 语料 imm2=1 而 pre-fix isel 硬编码 0；post-fix 语料字节差集恰为这两族 36 文件/变体且 pandasm 逐文件仅 imm2 一行 0x0→0x1） |
| N16 | Newobjapply↔Apply arity 往返脆弱 | ✅ 修复（53ba936，P5-T2：实际断点比登记更尖锐——deprecated.callspread 的 lift **丢了 v3（参数数组）**且以 1-arg "Apply" 被 isel 降级成 newobjapply（调用变构造）；0-arg Apply 静默发 callarg0。修复：新增 CallKind::NewObjApply（记录 acc=数组/v=ctor 的角色互换）、deprecated.callspread 保留全部三操作数按 N3 先例降当代 apply、isel 错误 arity 一律 LowerError 硬错误。红色远端实证：pre-fix 探针 (Apply,1) + 0-arg 无错误通过；post-fix 3/3 绿。无语料字节差） |
| N17 | 种子常量 B4 残余 + MCS/acc_score 不一致观察 | Ⓜ️ moot（acc_score 已被 B4 删除） |
| N18 | 无前驱死 catch 块清理 | ✅ 修复（cdab3d0，P5-T1：lift 末尾按 augmented 可达性（终结指令+try→handler 边，与 opt N11/verify N27 同模型）清扫死代码岛；任务书字面规则（仅终结指令边+保留 handler）经语料探针证明会误删 1146 个活 catch 体块，已修正——480 个真死块被清扫，2787 fixture 中零 handler 被误伤；死 handler 随岛清除，verify/opt_verify/lift 三套件 2787 全绿） |
| N19 | typed-array 残值 ×12 | ✅ 已愈（终态双 100% 覆盖证明；具体由 B4/T22 修复链吸收） |
| N20 | 管道非确定性 | ✅ 修复（16dc8ff） |
| N21 | handler 边拷贝 legacy 内联 | ✅ 修复（0270f9b） |
| N22 | 异常值活性保守 +1 寄存器 | 📝 无害记录（不修） |
| N23 | SCCP 折叠留陈旧 phi 条目 | ✅ 修复（76cb828） |
| N24 | oracle 容器僵尸 | ✅ 修复（3883291） |
| N25/N26 | ThrowConstAssignment / ThrowUndefinedIfHole 双寄存器形 opcode 身份损坏 | ✅ 修复（f121d74/55dba05，P4-T1：name 改为寄存器 VALUE；ThrowUndefinedIfHoleWithName 独立变体保留 string_id+acc 形；P1 期 unsupported 标记移除） |
| N27 | 优化器空 phi | ✅ 修复（76cb828） |
| N28 | copyprop "ADCE 会清理"假设残余风险 | 📝 残余风险记录（verify 兜底已就位） |
| N29-N35 | T20 五根因 | ✅ 全修（T21 六连） |
| N36-N41 | T19 opt 域六条 | ✅ 全修（T22 四连） |
| F-new-1 | vendor writer 创建顺序敏感（SET_FILE 偏移） | ✅ 修复（980ec16，P5-T2：根因在**我们的 bridge** 而非 vendored writer——flush_lnp_staging 在 literal staging 未应用时就 ComputeLayout 并烘焙字符串偏移，finalize 的 AddItems 再撑大 LA → 烘焙值过期；创建顺序只决定哪些字符串被移。修复=烘焙前先 flush literal staging（幂等），创建顺序约束消失。红色实证：hazard 测试 pre-fix 解出 "\u{2}\u{2}" 而非 "late.js"。附带修复 N55 encode 侧） |
| F-new-2 | 注解内嵌 LA 的方法引用写裸源偏移 | ✅ 修复（8a6671f，P5-T2：encode_literal_value_simple 接入实体句柄解析（offset 优先 + entity_map 名字兜底），不可解析即 CodeRelocation 硬错误；另发现 decode 把 '#' 标量注解元素按数组误读（vendored GetArrayValue 重解释不会失败）——vendor pandasm annotation.h 证明 '#' 只有标量形（GetArrayTypeAsChar 无 LA 情形），decode 改直读标量，annotation_all_types.rs 的旧 '#' 数组钉按 vendor 契约更正） |
| 死表面 | 108/324 导出未用 | ✅ **维护者拍板保留**（2026-09-20，D3：publish 形态 crate 保留完整导出面，不删） |
| CI #22 | 重复 vendor 文件保护 | ⏸️ 维护者决定不动 |
| SSA trivial-phi | 删除不写全 uses | ✅ 实质关闭（76cb828 替换式）+ N28 残余记录 |
| dominance 复审 | Phase 3 遗留评审项 | ✅ 实质覆盖（eb62547，N45：verify use-def 支配检查上线，四条豁免文档化） |
| string-pool 所有权复审 | 引用类型字符串池所有权 | ✅ 实质覆盖（9988e40，N46：FILE-BOUND 契约文档化，审计确认无消费者解析） |
| exception CFG 复审 | 异常 CFG 语义 | ✅ 实质覆盖（N10/N11/N13/N21 + augmented_succs 共享审计）；系统性复审并入 dominance 复审一起做 |
| Phase 5 清扫批 | literal_val_to_c 死代码、builder 二次 finalize staging、-sys README（#20/#21）、回调文档（#15）、abcd-file README 漂移 6 项、P2 测试缺口 | ✅ P5-T1 完成（2e38fbe/69a4cd8/58af748/92a5cbb/ab17b40/ba7e40e；二次 finalize 审计声明证伪=假阳性，契约钉测试+注释；另见 N18/N49/N50 行） |
| Phase 4 | 9/11 真实读验证（444+477 fixture）、pandasm 逐指令对照、stthisbyvalue/stprivateproperty/testin 补 fixture | **完成**（P4-T6，48cddf4 + fixture commit：pandasm 逐指令对照 2787 fixture / 12996 方法 / 2,691,470 指令零 mismatch（6 版本 × 3 profile 全矩阵，9.0.0.0+11.0.2.0 经 v24 超集表 decode 与上游 ark_disasm 输出逐指令相等——真实读验证达成）；stprivateproperty/testin 新 fixture 各 15（11.0.2.0+，9.0.0.0 es2abc 拒私有字段语法）经 scripts/gen-opcode-fixtures.py 可复现，oracle 双变体 30/30；stthisbyvalue 不可由 es2abc 发射 → N51 登记） |

| N42 | peephole+SCCP 位/移折叠用 Rust 饱和转换代替 JS ToInt32/ToUint32（≥2³¹/负移位/NaN/Inf 全错） | ✅ 修复（72975eb，P4-T3：共享 to_int32/to_uint32 对 vendor DoubleToInt number_helper.cpp:1137-1158 核验；双引擎 4 红探针+扩展表红转绿；N36 操作数序测试零回归） |
| N43 | reconstruct_try_blocks 的 min/max 单区间假设 RPO 连续——可被交错破坏 → 异常误分发 | ✅ 修复（P4-T4：每连续段一个 TryBlock，同 region 相邻段合并——连续 region 字节不变；红探针+嵌套+单段钉住；语料实证 8 族 region 非连续（旧字节 gap 内含 throw/callarg1/tryldglobalbyname 等真投掷指令，误分发潜伏未触发）；重写差集恰为此 8 族（lift 132/opt 108 文件），逐例 VM oracle 144/144+108/108，全量 1119/1119 双变体） |
| N44 | opt::inline 产出模块非法 IR（参数未映射/前驱未重建/try 区域丢失……） | ✅ 已隔离（cab3ab8，P4-T3）→ **v0.2 重写落地**（v2-P3b，D2=要：35ca7de 等 7 commit；v0.1 同形体 red-first 实证非法 IR，新实现按构造消灭三死因；vendor 帧槽模型 [func][newTarget][this][formals…] 坐实——初版参数模型 oracle 挂 18/1149 后修正；v0.1 inline 不移植，随 P4 删除） |
| N45 | DomTree 正确但零消费者（死代码）；verify 缺 use-def 支配检查 | ✅ 修复（eb62547，P4-T5：verify_dominance 接入 DomTree，四条文档化豁免——CFG 不可达块/phi 边使用/entry 定义值/ExceptionParam；DomTree 文档修正（post_idom 不存在）并脱离死代码状态；2757 fixture 零误报） |
| N46 | Type::Reference(StringId) 引用源文件池而 Module 不持有——今日安全（无消费者解析） | ✅ 已文档化（9988e40，P4-T5：types.rs/module.rs 注释钉死 FILE-BOUND 契约 + 未来 module-only encoder 的 remap 义务；审计确认无消费者解析，无错池解析点） |
| N47 | SCCP add_cfg_edges 对 Return/Unreachable 终结提前返回跳过异常边 | ✅ 修复（fd8a5d2，P4-T5：非分支终结 fall through 到异常边追加；格点观察红探针——handler 内可折叠 binop 修复前不折） |
| N48 | ADCE 把可观察 load（getter/品牌检查/CreateRegExp 等）当纯——死结果删除会丢副作用 | ✅ 修复（87e51b9，P4-T5：vendor isa.yaml 无 can_throw 属性且全组 x_none——不可派生，转 vendored runtime 证据逐条引用；GetIterator/GetAsyncIterator/LoadProperty/LoadPrivateProperty/TestPrivateProperty/CreateRegExp/LoadGlobalVar 七形标 essential；纯计算仍清扫的对照钉住） |
| N49 | layout 块区间公式（next-greater-offset）对零长块会把后继块代码吞进区间——今日无触发（每块必有终结指令≥1 字节码），潜伏 P3 | ✅ 修复（8d16a59，P5-T1：核实 select_inst 每个终结指令臂必发 ≥1 字节码——已验证 IR 上零长块不可能；但 lower_function 接受未验证 IR（UnallocatedOperand 先例），无终结指令的块会零发射→偏移混叠→try/handler 区间吞块→静默异常误分发。layout 展平时零发射即硬错误 LowerError::ZeroExtentBlock（与 HandlerEdgeCopies 同类不一致输入先例）；red-first 实证修复前返回 Ok） |
| N50 | TryLoadGlobalByName（未定义即 ReferenceError）与 LoadSuperProperty（getter）也是可观察 load，未进 N48 清单 | ✅ 修复（38db1e8，P5-T1：vendored runtime 引用钉死——RuntimeTryLdGlobalByName（runtime_stubs-inl.h:1739-1748，未找到即 ReferenceError " is not defined"）与 RuntimeLdSuperByValue（:681-697，GetProperty 调 super getter）；red-first 两形被删实证；全量重写双变体 1149/1149 零 skip、差集为空=**字节中性**（语料无死结果 tryldglobalbyname/ldsuperbyname），oracle 影响为零） |
| N51 | stthisbyvalue 无法经 es2abc 生成 fixture：es2panda（master 源码 grep 无发射点 + 镜像 6 版本 × 3 profile × 2 种 `this[k]=v` 源形态共 36 次编译实证）从不发射它——`this[k]=v` 一律 ldthis+stobjbyvalue（pandagen.cpp StoreObjProperty/StoreObjByValue）；整个 this-by-* 族（ldthisbyname/stthisbyname/ldthisbyvalue/stthisbyvalue）语料零覆盖 | ✅ 关闭（2026-09-20 维护者拍板硬错误，bab1efb+a8c2699）：两个 lifter 遇四形即 `LiftError::UnsupportedThisByAccess(助记符)`（v0.2 沿 UnsupportedSuperByIndex 先例；格式层 decode/encode 不动，isel/lower 不动——LoadThis/LoadProperty 他形仍用）。red-first：两个 lifter 各 4 个合成体测试 pre-fix 静默 Ok。手工 pandasm fixture 补覆盖成为可选项但不再必须——遇到即报错上报 |
| P4-T1 | N25+N26+N3+N9 修复批 | worker P4-T1 (k3) | **完成**（f121d74/55dba05/e9fd5db/d5ec683；每条 red-first 实证；语料重写 1119/1119 双变体、与 /tmp/t22-verify 基线字节差为空、本地 docker oracle 双变体 1119/1119）**+ orchestrator 联合复验通过（fmt/91 套件/字节差 0/oracle 复跑一致；N3 范围扩大批准）** |
| P4-T2 | dominance/string-pool/异常 CFG 系统复审 | worker P4-T2 (k3) | **完成**（只读；两 P1 声明 orchestrator 静态核实；N42-N48 登记） |
| P4-T3 | N42（双引擎 JS 整数转换）+ N44（inline 隔离） | worker P4-T3 (k3) | **完成**（72975eb/cab3ab8；red-first 均远端实证；语料重写 1119/1119 双变体零 skip、与 /tmp/t22-verify 字节差为空、本地 docker oracle 双变体 1119/1119，image sha256:5e7627…）**+ orchestrator 联合复验通过（同上）** |
| P4-T4 | N43 try 区域连续性修复（reconstruct_try_blocks 单区间假设 → 按块区间） | worker P4-T4 (k3) | **完成**（方案 (a)：每保护块一段、同 region 相邻段合并——格式证据：vendored CodeItem 持 try_blocks 向量 file_items.h:1370-1373,1426、运行时首匹配扫描 method.cpp:86-107、encode/decode 多条目往返 encode.rs:1313-1348/decode.rs:1790-1839；red→green 远端逐字实证；新测试 lower_try_range_contiguity.rs 三例（交错排除/单段合并钉住/嵌套首匹配序）；workspace 套件绿；语料重写 1119/1119 双变体零 skip，与 /tmp/t22-verify 字节差集恰为 8 个非连续 region 族（lift 132/opt 108 文件），scratch 解码对照证明指令流逐函数相同+覆盖仅为精化+gap 含真投掷指令，差集逐例 oracle 144/144+108/108，全量 oracle 双变体 1119/1119；新登记 N49 零长块区间公式潜伏）**；orchestrator 复验：fmt/92 套件绿、差集精确 240 文件、oracle 双 1119/1119 复跑零失败** |
| P4-T5 | 加固批：N45（DomTree 接入 verify）+ N46（文件绑定类型文档化）+ N47（SCCP 异常边 fallthrough）+ N48（ADCE 可观察 load 保守化） | worker P4-T5 (k3) | **完成**（fd8a5d2/9988e40/eb62547/87e51b9；每条 red-first 远端逐字实证：N47 格点观察——handler 内可折叠 binop 修复前不折（return+throw 两形）、N45 非支配使用+同块先用后定义两红探针 + 豁免钉住、N48 七形死结果被删红色清单；N46 审计确认无错池解析点故纯注释。门禁逐 commit：fmt + workspace + 定向 + corpus_verify/corpus_opt_verify 2757 全绿零误报。终态检查点：重写 1119/1119 双变体零 skip，lift 与 /tmp/n43-verify 字节恒等；opt 差集 300 文件全部归因——N47=12 文件（test-raw-try-catch handler 折叠 ldai 0xa，N47-only 树复证同 hunk）、N48=288 文件（死 LoadProperty(ldobjbyname×108@9.0.0.0) 保留 + 操作数链 ldlexvar 留存 + IC/字符串池重编号；9.0.0.0 全差集反汇编直方图佐证，无 ldglobalvar/getiterator/createregexp/私有属性死结果存在于语料）；本地 docker oracle 双变体 **1119/1119**（image sha256:5e7627…），remote run 目录已清理） |
| P4-T6 | 9/11 真实读验证：pandasm 逐指令对照升级 + stthisbyvalue/stprivateproperty/testin fixture | worker P4-T6 (k3) | **完成**（48cddf4 = Task A：real_module_abc.rs 全量 JSON substring 解析 → python3 标准 JSON 清单模式；新增 exported_corpus_instructions_match_upstream_pandasm——每 fixture 每方法解码指令流与 reference.pa（上游 ark_disasm 自身输出）逐指令对照（mnemonic+canonical 操作数：v/a 槽位、hex imm、fldai 按值 bits、字符串/方法实体按 MUTF-8 原始字节、跳转按解析后目标下标、字面量数组按内容 token；映射表见测试注释）；abcd-isa-sys 模板新增生成的 Bytecode::operands()（Operand::Reg/Imm/Entity/Label）。Task B：scripts/gen-opcode-fixtures.py + scripts/corpus-fixtures/ 两源（可复现生成）；新 case local/private-property-store（stprivateproperty）与 local/private-property-in（testin）各 5 版本 × 3 profile = 30 fixture（9.0.0.0 语法拒绝，同 private-field 先例无行）；compare-rewritten-corpus.py 增 unknown-case 回退（镜像 baked 清单无新 case 时 run+对照清单 runtime 记录）。实证：对照 2787 fixture / 12996 方法 / **2,691,470 指令零 mismatch**（全 6×3 矩阵，9/11 经 v24 超集 decode 与上游反汇编逐指令相等）；corpus_lift/verify/opt_verify 2787 全绿；lower 重写 lift 1149/1149 opt 1149/1149 零 skip；本地 docker VM oracle **双变体 1149/1149**（image sha256:5e7627…），新 fixture 双变体 30/30；remote run 目录已清理。新登记 N51：stthisbyvalue 不可由 es2abc 发射（es2panda 无发射路径，36 次矩阵编译实证）） |
| P5-T1 | Phase 5 清扫批九连（死 literal_val_to_c / 二次 finalize 复审 / N18 死块清扫 / N49 零长块 / N50 可观察 load / #15 回调文档 / #20#21 -sys README / abcd-file README 6 项 / P2 测试缺口） | worker P5-T1 (k3) | **完成**（2e38fbe/69a4cd8/cdab3d0/8d16a59/38db1e8/58af748/92a5cbb/ab17b40/ba7e40e；行为项全部 red-first 远端实证；**偏差两起**：(i) 二次 finalize 审计声明证伪——AddItems=assign、UpdateId=overwrite，双 finalize 今日即幂等，staging 保留反而是 post-finalize 追加的正确性前提，诚实处理=注释钉契约+测试钉行为；(ii) N18 任务书字面规则经语料探针证明误删活 catch 体（terminator-unreachable non-handler 含 1146 个活块），改用 augmented 可达性（与 opt N11/verify N27 同模型），480 真死块清扫、零 handler 误伤。P2 测试缺口分诊：3 项廉价测试落地（typed-array 模型级 decode、is_external 往返、两种 split dedup），余项登记理由。终态检查点：重写 lift 1149/1149 opt 1149/1149 零 skip 直方图空，与 N50 树字节恒等（后续全为 docs/测试），本地 docker oracle **双变体 1149/1149 missing 0**（image sha256:5e7627…），remote run 目录已清理）**新登记 N52：typed ARRAY_* 字面量 decode 后 LiteralArrayIdx 包裹的是裸文件偏移而非表索引（LiteralValue::LiteralArray 有 offset→index 重写，ARRAY_* 没有）——模型语义 wart，无语料触发，待 v0.2 定夺**；orchestrator 复验通过（fmt/97 套件绿；oracle 双 1149/1149 复跑一致；与 t6 基线差集 108 文件全部属 try 族=N18 清扫预期；item 2 假阳性纠偏已对 vendor file_items.cpp:1161-1164 `items_.assign` 实证）** |

| N53 | `callruntime.definesendableclass` 塌缩进 InstData::DefineClassWithBuffer 且 isel 重发**当代** defineclasswithbuffer——opcode 身份损坏（sendable 语义走 RuntimeCreateSharedClass，与 RuntimeCreateClassWithBuffer 不同 stub），N26 同类。语料 24.0.0.0 sendable-class fixture 均 runtime not-applicable 且不进重写集 → 潜伏。P5-T2 于 N15 修复时发现 | ✅ 修复（9159e9a，v2-P2b：v0.2 建模 `Op::DefineSendableClass` + lift 解塌缩 + abcd-lower 正确重发 `callruntime.definesendableclass`；对照器加文档化分歧规则 8（v0.1 冻结折叠）；pre/post ark_disasm 实证：pre-fix 重写发 defineclasswithbuffer（损坏），post-fix 发 callruntime.definesendableclass 与原 fixture 一致。v0.1 的折叠保留为冻结 oracle 行为） |
| N54 | `deprecated.defineclasswithbuffer` lift 操作数角色损坏：vendor 运行时读 v1=lexenv、v2=proto（interpreter_assembly.cpp:4625-4648），我们 lift 以 v1 为 base(proto)、丢 v2（且当代形从帧 env 取 lexenv）——双重角色错。语料零 fixture（reference.pa 全 grep 无）→ 潜伏 | ✅ 关闭（e1d87fe，v2-P2b：双 lifter 硬 LiftError（N8/N51 原则——零证据路径，遇到即报错）；red-first 远端实证 pre-fix 双 lifter 静默接受；corpus_verify 字节中性绿） |
| N55 | decode 给无 debug info 项的方法捏造 `debug: Some(source_file: Some(""))`（vendor DebugInfoExtractor::GetSourceFile 对缺失条目返回 ""，debug_info_extractor.cpp:318-324；decode.rs:415 无条件 Some 包装）；且 vendor extractor 遇 file_=EntityId(0) 的 debug 项时 GetSpanFromId 抛 INVALID_FILE_OFFSET（file.h:190）→ 整文件 debug 区全灭 | ✅ 修复（279b6cc，v2-P2b：decode 仅当方法索引项结构上有 debug 项才挂 debug（abc_method_debug_info_off），vendor "" 映射为 None；**第二半程调查坐实**：bridge 把 extractor 构造异常的 nullptr 当"无 debug"=**静默整文件 debug 丢失** → 改硬错误 Error::DebugInfoExtraction（零 debug 项的文件不会抛，null 绝不良性）；dedup_variants fixture 恰好在构建这种退化 debug 项、此前靠静默丢失才绿——修 fixture 补 SET_FILE。字节中性：三个 debug-info fixture 重写 pre/post 逐字节一致 + corpus_verify 绿） |
| P5-T2 | 对账表遗留批：F-new-1 / F-new-2 / N7 / N8 / N15 / N16 | worker P5-T2 (k3) | **完成**（980ec16 F-new-1 / 8a6671f F-new-2 / 71adc56 N7 / 3ed4228 N15 / 53ba936 N16 + N8 裁决登记；逐条 red-first 远端实证；终态检查点：重写 lift 1149/1149 opt 1149/1149 零 skip 直方图空，与 /tmp/t51-verify 字节差集恰为 class-accessors+module-exports 两族 36 文件/变体且 pandasm 逐文件仅 defineclasswithbuffer imm2 一行 0x0→0x1（=N15 语义修正），本地 docker oracle 双变体 1149/1149（image sha256:5e7627…）；新登记 N53/N54/N55；remote run 目录已清理）**；orchestrator 复验通过（fmt/101 套件绿、差集精确 72 文件=N15、oracle 双 1149/1149 复跑一致、容器零残留；F-new-1 bridge 修复机制对 vendor 烘焙序实证）** |

| N56 | Builder `literal_array_add_module_request_phase` + module-data staging 疑似损坏 module blob 字符串偏移（decode: invalid entity offset；无 Builder 先例，疑 bridge staging 顺序问题，abcd-file 域） | ✅ 修复（c79220d，诊断 worker v2-P2a + orchestrator 落地）：**原假设证伪**——bridge/vendored writer 输出逐字节正确（对照实验：phase 字段挂别的类全绿、字符串逐字验证）；真根因是 `decode_field_at` **分派臂顺序**：`_ESModuleRecord` catch-all u32 臂排在 N7 名匹配臂之上，merge-abc 布局（phase 字段挂模块记录自身）被误路由进 module-data blob 解码器 → 整文件不可 decode。修复=一臂重排（N8 同型陷阱，N8 修过顺序而 N7 臂后加没修）。语料零暴露的原因：es2panda 把 phase 字段挂独立的 `L_ModuleRequestPhaseRecord;`（9 fixture 探针实证）。red-first：9 红 3 绿 orchestrator 独立复现 → 4 精选测试（同类 decode/300 字符串池增长/往返/异类对照）；abcd-file 91/91 + 语料套件字节中性 |

| N57 | v2-P1 折叠 `apply` → Call{Dynamic,this,args:[array]} 与 callthis1 同形——spread 语义丢失，v0.2 lower 无法忠实还原（18 个 runtime-passed 文件） | ✅ 落地（55c989b，v2-P2c；orchestrator 复验绿） |
| N58 | v2-P1 折叠 supercallspread(42 passed) 与 callruntime.supercallforwardallargs(12 passed) 同形 Call{Super,[x]}——v0.1 分发 supercallspread vs supercallthisrange(argc=1)，单一选择必破一边 | ✅ 落地（894f573，v2-P2c；orchestrator 复验绿） |
| N59 | createobjectwithbuffer vs createarraywithbuffer 都折成 AllocObject{shape}——对象/数组标签不在字面量数组内容里（平铺 buffer 内容不可嗅探），语料无处不在 | ✅ 落地（b3be74b，v2-P2c；orchestrator 复验绿）：Op::AllocArray{shape: Option<ConstId>}（None=createemptyarray） |
| N60 | own-store 族（stownbyname 6 / definefieldbyname+definepropertybyname 90 / callruntime.definefieldbyvalue 180 passed 文件）折进 StoreProp 族——v0.1 StoreOwnProperty→stownby*（define-own 语义），v0.2 只能发 stobjby*（普通 set，走 setter/原型链），语义+字节双分歧 | ✅ 落地（73e0d05，v2-P2c；orchestrator 复验绿） |
| N61 | trystglobalbyname（54 passed 文件）折进 StoreGlobal——tolerant store 变 throwing stglobalvar，字节必分歧、全局缺席时语义分歧 | ✅ 落地（9425e73，v2-P2c；orchestrator 复验绿） |
| N62 | 重复内容字面量数组经 v0.2 内容键控常量池合并：同内容两个表索引→一个 ConstId→一条重定位条目（v0.1 按表索引两条），53 文件与 v0.1 重写差一个 4 字节索引区条目+下游偏移；指令流全同、运行内容全同、oracle 不可见 | ✅ **维护者拍板接受**（2026-09-21）：门禁 2 终态=「1149/1149 − 53 N62 归属文件」；v0.2 保持格式无关 IR 原则，不引入表索引溯源；若未来出现需要逐站字面量数组身份的消费者再重启（分析 design/n62-literal-array-dedup-divergence.md） |
| N63 | v0.1 SCCP 把 ExceptionParam 留在 Top（格点单位元）→ phi(异常对象, 常量) 被误折为常量：异常路径真触发时折叠错误——v0.1 的潜伏正确性 bug，oracle 绿只因语料里该路径从不触发（opt-try-catch-func/test-raw-try-catch/optimized 6 文件） | ✅ 裁决登记（2026-09-21，v2-P3 发现）→ **关闭**（P4：v0.1 已删除，bug 随载体消亡；v0.2 把 ExceptionParam 解析为 Bottom、保留 phi，严格更健全——随 P3 门禁 2 的 M3b 归属分歧被维护者接受） |
| P3-M1/M2 | v2opt 与 v0.1 opt 的另两类归属字节差异：M1（72 文件）折叠出的 NaN/+∞——v0.1 降级为 fldai，v0.2 保留 ldnan/ldinfinity 身份；M2（12 文件）v0.1 ADCE 手工清单把 DefineFunc 标 essential，v0.2 诚实 effects 表（vendor RuntimeDefinefunc 不跑用户代码）允许删除死 definefunc+闭包链 | ✅ 维护者拍板接受（2026-09-21，与 N63 同批）：v2 严格更好或 VM 中性；v0.1 对齐被否决（不为对齐往 effects 表写假话） |
| RADAR | tag 雷达落地（维护者批准+两处修正：OpenHarmony- 前缀宽松匹配、按 tag 时间取最新零版本解析）+ common-files-consistency 删除（维护者裁决：shim 不同步也没关系） | ✅ 完成（38ce6a6/3d4e2b1/77d2e99/791dd2c；54 个前缀匹配 tag 按 committer date 取最新=v7.0-Release；三次 dispatch 实证：首轮抓到 dup-check 真 bug（jq null 插值假阳性）已修、第二轮开出 PR #20（常开红 PR=v7.0 移植成本文档，按设计）、第三轮幂等零重复；CI 绿；orchestrator 抽查 PR #20 正文/幂等/ci.yml 无残留全符） |

| V-SUB | vendor 同步机制改造：ruby 复制+一致性检查 → **git submodule 内嵌上游**（crate 根，无 vendor/ 层）；pin=实证 master commit 7303d5c2（95 文件 blob 全匹配）；CI 周期检查=OpenHarmony-* 最新 tag vs pin（雷达设计在 design/ci-rework-plan.md，参考实现 3092de4，待维护者批准落地） | ✅ 完成（72f0908…e1a7282 + 6919592 descope；**pin 按内容认定**：被删快照 95 文件与 master HEAD 逐字节全匹配；file_reader 漂移证实为上游自身 legacy 死路径（build.rs 本就不编译它）。CI 创新：submodules:true 不可用（上游有悬空嵌套 gitlink + NTFS 非法路径）→ **sparse 克隆只取六个消费子树（15MB vs 280MB）**。orchestrator 独立复验：workspace 701/0、语料 30/0、梦想门禁 1149/1149、CI 六任务全绿 run 35983596889） |

| N68 | **G6**：现代 async 族字节码（asyncfunctionawaituncaught/resolve/reject）的值在 **acc** 传递（isa.yaml `acc:inout:top`；runtime interpreter-inl.cpp ASYNCFUNCTIONAWAITUNCAUGHT_V8），但 abcd-lift 只建 funcobj 寄存器操作数——值根本不进 IR | ✅ 修复（d-P12，da1f3c0/6e44ce3/efc1dd2/e810dfd；三 op 加 funcobj 字段 + lift 读 acc 为值 + lower 重发正确 + 反编译异步 fold（AsyncResolve→return/AsyncReject→throw）；连带修 deprecated 形中寄存器误绑 + asyncgeneratorreject 同款。acc 语义缺席族第四例关闭） |

| N67 | abcd-lift 的 `this_value()`/`this_param=params[0]` 按帧槽模型（0xF）其实指向 **func 槽**而非 this——**潜伏 bug**：仅被 `Bytecode::Ldthis`（和 N51 硬错误族）消费，而 ldthis 全语料 0 出现（es2abc 永远读槽 2）故所有门禁不可见。修=按 inline.rs 的 slot_roles 模型解析 This 角色槽（params[2] @0xF）。function.rs:210 与 abcd-lift 注释的 params[0]=this 文档同属此 bug 的记载 | ✅ 修复（bb56e51，d-P6：this_value() 走 canonical abcd_ir::frame（0xF→params[2]，注解感知，无 this 位/短参数→undefined 兜底）；lift_ldthis.rs 4 钉测试 + 红-first stash 实证 2/4 红；字节中性 3447 文件 diff 空；注释清扫 5af02ec） |

| N66 | abcd-taint call_flow 的 arg→param 绑定沿用 T4 旧约定（params[0]=this、args[i]→params[i+1]），但 vendor 帧槽模型（P3b 坐实）是 [func][newTarget][this][formals…]（callType 注解位，语料全无注解→默认 0xF→3 隐式槽）——真实字节码上 args[0] 错绑到隐式槽，解析调用实参流全 FN（t-P1 探针 c1/d3/e3 实证）。语料冒烟未暴露（命中全是过程内/状态基流 + 通配播种）。连带漂移：T4/§5.3 绑定表与 abcd-lift 注释同为旧理解（inline.rs 持有正确模型） | ✅ 修复（6da5e03，t-P1 附带：call_flow 全接帧槽模型——0xF 默认 this→params[2]/args[i]→params[3+i]、注解形按位读、非静态无注解走保守全参数过近似不静默丢；3 个双向精度钉测试；探针 c1/d3/e3 由 KNOWN-FN 翻 TP 且 runner 强制更新标注=仪器自证。**orchestrator 独立复验**：probe 表 tp=11 fp=4 fn=4 violations=0 逐字复现、默认冒烟 hits=0 / 正控 36 不变（字节中性）、scoped workspace 114 套件绿；CallType 与 inline.rs 复制一处，共享 helper 收敛已登记） |

| N65 | `delobjprop` 操作数双重反转：vendor 语义 obj=v0/prop=acc/result→acc（isa.yaml:1293-1296 acc:inout），abcd-lift:720 把 acc 读成 object、v0 读成 key，abcd-lower:1136 同形反转写回——**双反相消**，字节恒等/VM oracle 全绿但 IR 语义错（反编译器等语义消费者现形）。源自 v0.1（parity 同反不查），d-P4 发现。语料 18 文件（property-ops 族）runtime-passed 但因字节不变而绿 | ✅ 修复（7fa03cb，d-P4 附带：lift+lower 双边交换；red-first 钉测试 lift_unit/lower_delobjprop_roles/decompile golden s25；acc:inout 族全审计无更多反转（deprecated 形本就正确，无 N66）。**orchestrator 独立复验**：自跑 v2lift 对 P2 基线 **0 差异**（worker 报的 13 个 N55 时代 debug 序差异不复现——字节恒等比其声称更强）、VM oracle 1149/1149（sha256:5e7627bdcb78…）） |

| N64 | abcd-ir verify.rs 的私有支配集被**不可达 Normal 前驱**污染：可达块若有任一不可达 Normal 前驱，全集初始化把它的 dom 集清空 → verify 视其为 Normal 不可达 → 其 uses 豁免 N45（仅弱化不强化）。v2-P5a 支配一致性测试发现（11.0.2.0/local/destructuring 块 32/34/35/45） | ✅ 修复（b41f643，orchestrator 自修，维护者授权解冻 abcd-ir：先算 Normal 可达性再过滤不可达前驱出支配迭代。red-first：worktree@HEAD 新鲜构建红（误豁免实证）、修复后绿。门禁：abcd-ir 25/25、corpus_lift_verify 2787 零新错误、支配一致性 31086 块 0 分歧、workspace 零失败、fmt 净。**过程事件**：远端共享 target 缓存两次给出陈旧二进制假红/假绿——红绿证据必须 touch 强制新鲜构建） |

## 审计纪律

- 审计期间 abcd-isa-sys / abcd-isa / abcd-file-sys / abcd-file 冻结功能性改动（允许新增测试文件）。
- findings 必须有 file:line 证据；不接受无指向的结论。
- 修复走项目既有评审流程：逐 commit + 回归测试 + design 状态列更新。

## IR v0.2 任务登记（2026-09-21 开工；设计 design/ir-v0.2.md，维护者已批 D1+三问）

| # | 任务 | 执行者 | 状态 |
|---|------|--------|------|
| v2-P0 | abcd-ir2 骨架：taxonomy + Effects + Ty + verifier 骨架（零格式依赖 Cargo 强制） | worker v2-P0 (k3) | **完成**（e83a2c4；orchestrator 复审 effects 派生表/Ty 格 join/verifier 豁免语义 + 复验：fmt/103 套件绿/ir2 22 测试绿/doc 零警告） |
| v2-P0.5 | abcd-ir2 分类表扩到 ISA 全覆盖 | worker v2-P1 (k3) | **完成**（741fb8e；22 个新 op + payload homes + 全套 vendor 依据 effects；orchestrator 复审 effects 条目（GetTemplateObject/ArraySpread/SetObjectWithProto）+ 复验 fmt/ir2 23/23 绿；设计文档 §4.1 已同步为 ~70 ops） |
| v2-P1 | abcd-lift 转换器 + v0.1 parity 对照 | worker v2-P1 (k3) | **完成**（57f336f+6ab12b7；关门复现：**2787/2787 lift 零失败零 pending、verifier 零错误、12996 函数 1,434,154 token 零不一致**——函数数与上游 pandasm 方法数精确相等；workspace 109 套件绿；新登记 N56 Builder module-blob staging 疑似损坏） |
| v2-P1a | abcd-file 嵌套字面量数组 decode | worker v2-P1a (k3) | **完成**（6d1fcd0；worklist 递归收集（排序批=N20 确定性、先注册后解码=循环安全、排除规则与表头一致）；orchestrator 复验：新套件绿、real_module_abc 7/7、2787 fixture decode-diff 恰 57 个、恒等重写 ark_disasm 全净且与 reference.pa 内容一致（模布局重编号）） |
| v2-P2 | lower：v0.2 Module → MethodBody（复用重定位通道），VM oracle 对齐 1149/1149×2 | worker v2-P2 (k3) | **完成**（N62 裁决落地=接受归属分歧，门禁 2 终态「1149/1149 − 53 N62 归属」；379dfc0/1717d4a/5d749ef/a54f004/540e9a2/4cb9d51/a170e96/8e3e514；新 crate abcd-lower 全套移植 + fusion.rs 新增反折叠分析。**orchestrator 独立复验全绿**：v2lift 1149/1149 零跳过、VM oracle 1149/1149（sha256:5e7627bdcb78…）、确定性两次全量重写 0 差异、fmt 净、workspace 139 套件全 ok 零 warning、字节恒等 1096/1149 + 53 恰为 N62 四族指令流恒等；中途门禁抓到 3 个真字节保真 bug 已修 540e9a2） |
| v2-P2a | N56 诊断（Builder module-blob staging 疑似损坏）：最小复现+定责+修复 sketch，**只读不落 commit** | worker v2-P2a (k3) | **完成**（2026-09-20：7 变体复现 + 对照实验证伪 bridge staging 假设，真根因=decode 臂顺序；orchestrator 落地修复 c79220d，见 N56 行） |
| v2-P2c | N57-N61 落地：abcd-ir2 补 CallKind::Apply/SuperSpread/SuperForwardAllArgs + AllocArray + StoreOwnProp 族 + TryStoreGlobal，abcd-lift 解除 5 处折叠，compare.rs 分歧表同步 | worker v2-P2c (k3) | **完成**（55c989b/894f573/b3be74b/73e0d05/9425e73；每项带合成体测试 + 真实 fixture pre/post 证据；对照器五区分改精确比较，唯一残余折叠 SuperForwardAllArgs→super 系 v0.1 自身表示所限、文档化；orchestrator 独立复验：fmt 净、ir2+lift 59 测试绿、parity 2787/0 mismatch、workspace 132 套件全 ok——P2 已同步集成全部新 op 含 TryStoreGlobal 臂） |
| v2-P2b | N53（建模 SendableClass）+ N54（deprecated.defineclasswithbuffer 双 lifter 硬错误）+ N55（decode debug "" 捏造修复） | worker v2-P2b (k3) | **完成**（e1d87fe/9159e9a/279b6cc；中途 5h 限额打断一次，恢复零丢失；orchestrator 独立复验：fmt 净、workspace 143 套件全 ok 零 warning、parity 2787/0、corpus_verify+opt_verify 绿；N53 sendable 证据=ark_disasm pre/post；N55 第二半程坐实静默 debug 丢失→硬错误） |
| v2-P3 | pass 移植：SCCP/copyprop/DCE/peephole（T3 Effects 表），opt 变体 oracle 对齐 | worker v2-P3 (k3) | **完成**（47f343e/a01b47c/7ef09aa/537b97e/2d06fb2；新 crate abcd-opt 5334 行，inline 不移植=D2；ADCE 本质性全由 Effects 派生（无手工清单），TryGetGlobal effects 缺口修复（vendor 依据）；ExceptionParam→Bottom 坐实 N63。**orchestrator 独立复验全绿**：v2opt 1149/1149 零跳过、VM oracle 1149/1149（sha256:5e7627bdcb78…）、确定性两次全量重写 0 差异、v2lift 路径零污染、fmt 净、workspace 154 套件全 ok 零 warning、parity 2787/0、字节恒等 **143=53 N62+90（M1=36+18+18/M2=12/M3b=6 逐族精确吻合）**） |
| v2-P3b | inline 在 v0.2 上重写（D2=要；按构造消灭 N44：形式↔实际参数映射、调用点前驱重建、try 区域保留、产出 verifier 洁净；opt-in 不进默认管线；门禁=inline-on 语料 oracle 1149/1149） | worker v2-P3b (k3) | **完成**（9bd8653/35ca7de/0bf9636/d1435af/2b4a379/0b5bde1/1180b95；中途 5h 限额打断一次恢复零丢失。里程碑发现：**vendor 帧槽模型 [func][newTarget][this][formals…]**（callType 注解位，语料全无注解→默认 0xF→3 隐式槽；method_literal.cpp Initialize + 实证探针）——初版参数模型 oracle 18/1149 挂，修正后绿。内联统计：18 点/210 指令（typescript-enum IIFE 族），跳过直方图在案（unresolved-callee 5268 等=保守策略）。**orchestrator 独立复验**：v2inline oracle 1149/1149（sha256:5e7627bdcb78…）、确定性 0 差异、v2lift/v2opt 对基线 0 差异、fmt 净、157 套件绿、parity 2787/0） |
| v2-P4 | 替换：abcd-ir **删除**（不留档，维护者 2026-09-21 拍板；git 历史即留档），abcd-ir2 正名 abcd-ir；parity 对照器/v0.1 语料 driver 一并退役 | worker v2-P4 (k3) | **完成**（b42e8f4 退役对照器(-1665 行)/d0060a5 删 v0.1(-26370 行)/c6fbe36 改名/ec68bee 文档；**orchestrator 独立复验**：fmt 净、workspace 101 套件 462 测试零失败零 warning、自跑 driver 三变体对验收基线 **0 差异**、v2opt oracle 1149/1149（sha256:5e7627bdcb78…）、corpus_lift_verify 2787/12996 钉住绿；远端目录全清。**v0.2 正式成为 abcd-ir**） |
| v2-P5a | **abcd-analysis** 基建 crate（维护者 2026-09-21 再裁决：不叫 abcd-dataflow）：`control/`（RPO/后继/支配/循环/区域/可达性——含 abcd-lower analysis.rs 迁入+字节恒等门禁）+ `dataflow/`（单调框架/use-def/IFDS 骨架/heap v0 分配点键控+强弱更新+精度阶梯文档）+ `callgraph/`（on-the-fly）；abcd-ir verify 保留私有最小支配实现+语料一致性钉测试 | worker v2-P5a (k3) | **完成**（32fefb8/4c3b90f/06093d0/800fcbf；control（含 lower analysis.rs 迁入+re-export shim）/dataflow（单调框架+use-def+IFDS 骨架+heap v0+AliasOracle 六方法接缝）/callgraph（on-the-fly+UnknownCallees 显式）。**orchestrator 独立复验全绿**：自跑 v2lift 对基线 **0 差异**、调用图直方图 sites=10962/resolved=345/unknown=10617（96.9% unknown=语料 callee 多为全局加载如 print，保守策略的真实代价）、支配一致性 31086 块 0 分歧、fmt 净、106 套件绿零 warning、corpus_lift_verify 绿。新发现 **N64** 登记（verify 支配污染弱化 N45，仅弱化不强化，待修）） |
| v2-P5b | abcd-taint 应用 crate：source/sink 配置 + top-20 builtin 摘要注册表（call-to-return 拦截/exclusive/回退阶梯/缺失计数）+ 污点驱动 + loc 报告，语料 print sink 冒烟 + 5 族精度探针 | worker v2-P5b (k3) | **完成**（d00657a/95a5333/b910b4c/f48c00c/47ad48e；fact=基值(Local/Heap-AllocSiteSet/Global/ModuleVar/LexVar)+k 截断字段链；**名字解析穿过全局加载链绕开 96.9% unknown 墙**；top-20 按语料频率实证选取（print 3795 主导）。**orchestrator 独立复验**：默认冒烟 1149/0 hits 真阴性+确定性、正控 all-params **18 fixture/36 条流入 print**、探针 5 族 tp=1 fp=0 fn=0 全绿（14 机制测试同绿）、fmt 净、未触域门禁全绿；workspace 唯二失败=d-P1 在制品与 P5b 无关） |

## 反编译轨道（2026-09-21 维护者批准登记；crate 名 abcd-decompile，动词家族）

历史：项目初代即反编译器（5de5ab9 abcd-decompiler+abcd-cli；1a8e3f4 二代转型移入 recovery/gen1/；f045e4a 存档删除，git 历史可查）。v0.2 设计非目标但"不许堵死"（ir-v0.2.md §1），§7 元数据契约已为它保留 Import/ExportDecl + loc + 无损 Sym。

| # | 任务 | 状态 |
|---|------|------|
| d-P0 | 规划+技术准备：design/decompile.md（架构、IR 适配审计、先例调研、阶段门禁） | **完成**（40ef9d0；gen1 考古 + 87 op 适配审计 32T/48N/7H + G1-G5 缺口登记；orchestrator 复审落盘） |
| d-P1 | 基建前置：区域结构化分析落 abcd-analysis::control（支配/循环 P5a 已交付）；门禁=合成 CFG 测试 + 2787 全量结构化/不可约计数报告（预期≈0）+ 确定性 | worker d-P1 (k3) | **完成**（c538017/d357e3c；中途 5h 限额打断一次恢复零丢失。模式无关归约：循环剥离+出口尾吸收（消灭 360 假多入口）、条件臂全后支配合并+兄弟臂回避、Alternates/Labeled 多入口续体、Irreducible 折叠节点；不可约检测=环减支配回边。**orchestrator 独立复验逐字复现**：12996/12996 结构化、**不可约核 0、逃生舱 0**、try 区域 1797 零错误（234 处 try 切断结构化区域=es2abc 字节级连续 try 范围的观察而非错误）、cross_arm_edges 690 留给 d-P3 作复制提示、10 个合成测试绿、113 套件绿、fmt 净） |
| d-P2 | 表达式恢复（SSA → 表达式树；内联规则走 Effects 表；phi→临时变量；命名合法化器） | worker d-P2 (k3) | **完成**（1c6fa83/def104b/8d7f296；新 crate abcd-decompile：expr.rs 表达式模型/recover.rs 恢复/names.rs+legalize.rs 命名。内联规则 O(1) 前缀和效应屏障；单使用按操作数槽计（文档化强化 §4.1）；影子守卫防 `const foo=foo` TDZ。**orchestrator 独立复验**：语料门禁 2787/12996 函数、**1,398,139 指令 1:1 有去向**、fallback 仅 hard-7 族 1230 条（全在文档化集合）、确定性两次逐字节一致、19 黄金测试 + 7 lib 绿、fmt 净、117 套件绿、lift_verify 未触绿；发现 §5 表 T=32/N=48 与摘要 31 的行级漂移（按行为准，记录在 fitness.rs）） |
| d-P3 | 结构化+发射 v1：区域树→语句 AST（语法糖折叠/try-catch 投影/模块与类重建）+ 文本发射（d-P4 做精修与梦想门禁） | worker d-P3 (k3) | **完成**（9f28122/f0abca3/b554a89/0c6b5e2/34ce9b7；中途 5h 限额打断一次恢复零丢失。结构化器（phi 落点规则/try 投影含切断边界 270 处/handler shim 1755/交替臂标签块/不可约状态机兜底语料 0 触发）+ 折叠（for-of 12/for-in 18/对象 36/数组 54/switch 467）+ 发射器 v1（优先级表/诚实注释）。**orchestrator 独立复验逐字复现**：2787 fixture / 12996 函数 / 13152 体 / **22,934,182 字节 JS**、确定性两次逐字节一致、零 panic、不可约 0、node --check 40/40、19 黄金族绿、fmt 净、119 套件绿、未触域全绿；v1 限制清单在案（cross_arm 885 空条件合并=d-P4 最大可读性项、finally 复制按设计延迟、var 用于 phi 临时量防 TDZ）） |
| d-P4 | 发射精修 + 梦想门禁：反编译→es2abc 重编译→ark_js_vm 行为对照（复用 compare-rewritten-corpus.py 流，1149 运行时记录）；失败桶化归因（decompile bug/es2abc 不能/预期 fallback/fixture 不支持）+ source_code 文本次级 oracle | worker d-P4 (k3) | **完成**（1499904…56b6a4e 共 9 commit；cross-arm 折叠 885→558 folds/594 复制块/114 诚实残余；**梦想门禁 951/1149（82.8%）**：decompile-bug 108（try 投影近似族 72 + 私有属性缓冲 18 + 深 lexenv 18，全登记）/es2abc-cant **0**/预期 fallback 54/fixture 不支持 36（模块 G2）；门禁抓到并修复 10 个真发射器 bug + N65。**orchestrator 独立复验**：本地端到端重跑梦想门禁（生成器重生成 6.43MB JS→es2abc 重编译→docker oracle，219s）951/108/0/54/36 逐字复现、fmt 净、122 套件绿零 warning、N65 树字节恒等 0 差异 + oracle 1149/1149；文本 oracle 转向 manifest source（source_code 全系占位符——新发现：es2abc 从不内嵌源码）**反编译轨全线收官**） |

排序：与 taint 轨道平行（crate 不相交）；d-P0 现在就做，d-P1 起等 FlowDroid 对照结论（若支配树/循环分析落 abcd-dataflow 则受其节奏影响）。

## 清尾队列（2026-09-23 维护者拍板：全部纳入计划，按序执行；E 系列同日入列）

| # | 任务 | 内容 | 状态 |
|---|------|------|------|
| d-P5 | B1 try 投影精度 | 72 fixture：try 投影与 es2abc 字节级 try 范围对齐（handler 续体接合点）；门禁=梦想门禁 951→1023 | **完成**（b9370b6/5495a17/ed8cbe3/62c4460/87e36ad/a4630cb；五个根因全部 IR/VM 级实证：RC1 切断条件吞掉 try 接合点、RC2 异常 phi 冲刷排在 throw 后成死代码、RC3 finally 链止步于 shim 处理过的 plan、shim 区域闭包漏传递包含、循环退出三连（switch 折叠把循环 break 变 switch break=死循环直接机制）。**orchestrator 独立复验**：本地重跑梦想门禁 190s——**1023/36/0/54/36 逐字复现（精确 +72 零回归）**、fmt 净、122 套件绿零 warning、新 6 个 red-first 黄金测试；偏差登记：b9370b6 中间态有两个 red-first 占位黄金测试红（bisect 注意）） |
| d-P6 | B2 私有成员缓冲属性 | 18 fixture：class 成员缓冲的属性位（static/实例/private brand）进 IR（abcd-ir+abcd-lift+abcd-decompile） | **完成**（7bdc98d/bb56e51/5af02ec + orchestrator 1080431；vendor 编码坐实：缓冲=[三元组对…, 末槽 i32 nonStaticNum]（class_info_extractor.cpp:36-42,78），`MemberAttrs{is_static,kind}` 纯投影 lower 忽略故字节保真；新 classfold.rs 反转 es2abc 实例初始化降级。**含 N67**（ldthis 改绑 This 角色槽 params[2]@0xF，abcd_ir::frame canonical 模块公开；字节中性证明 3447 文件 diff 空）。**orchestrator 独立复验**：本地梦想门禁 185s **1041/18/0/54/36 逐字复现**、125 套件绿零 warning、红-first 核实） |
| d-P7 | B3 深 lexenv×try | 18 fixture：for-update-continue-1 族作用域重建 | **完成**（60518eb；根因：G1 兜底命名按读取点相对层键控导致同一帧名字随读者深度漂移——module 顶孤儿预声明永不赋值→undefined is not callable；修=NameScopes 以定义点继承环境播种（传递+环保护+确定性）+ 兜底键改绝对链索引。预诊断的两条嫌疑（phi 遮蔽/try 复制）经实证为**非问题**（var 提升=别名非遮蔽；复制保持行为）。**orchestrator 独立复验**：本地梦想门禁 215s **1059/0/0/54/36 逐字复现（decompile-bug 桶清零，精确 +18 零旁动）**、fmt 净、workspace 减 abcd-taint 119 套件零失败） |
| d-P8 | D 可读性批次 | finally 复制折叠、arrow-vs-function、多 catch 合并、LexStore 作用域重建、--ts | **完成**（e04bb7a/de03123/0dabfbd/c113050/134a195/4e97012；finally_fold=18（alpha 等价全证明，兜底保留注释）、scope_fold=237、多 catch 合并带绑定别名（语料 0 触发）、--ts 诚实限定（签名仅 ≤11 格式存活=1944+2124 函数，12+/24 零=#A7）、**arrow 其实可恢复**（NC_FUNCTION⇔arrow，六版本探测一致，FunctionKind::Arrow/AsyncArrow 增列于 abcd-ir——偏差：动 abcd-ir/abcd-lift，kind 位在方法索引非 definefunc 指令故字节中性）。**orchestrator 独立复验**：梦想门禁 177s **1059/0/0/54/36 逐项落地后重验不变**（铁律达成）、lower corpus oracle 绿（Arrow 穿透 round-trip 无损）、fmt 净、125 套件绿零 warning） |
| d-P9 | C1 模块 G2 | 36 fixture：lift 用 ModuleData 把槽位解析成名字 + 模块模式完善 | **完成**（5bf361e/4ff404d/bd6f184；根因纠偏：call-entry 形态本就正确，唯一失败=槽位↔名字对应（合成 m{index} 对不上导出记录）——decompile 侧 module_slot_names 双文件事实通道解析（TDZ 守卫名 + 存储的 DefineFunc/Class 名含 12.0.6+ 内部名解混淆），冲突即毒化保持合成名（诚实规则 g03/g04 钉）；零 lift/IR 改动故字节中性按构造；export as default 保留字修正。**orchestrator 独立复验**：本地梦想门禁 193s **1095/0/0/54/0 逐字复现（fixture-unsupported 桶清零）**、fmt 净、126 套件绿零 warning） |
| d-P10 | G4 模板 raw | 36 fixture：核实 raw 是否在字面量数组，在则保留 | **完成**（c3345fc/11f863a/610f30f/3aeb221；raw 在文件字符串表逐字存活（cooked/raw 相邻成对），vendor 布局坐实 [raw, cooked]（raw=索引 0：es2panda literals.cpp Literals::GetTemplateObject 建 templateArg=[rawArr, cookedArr]；运行时 template_string.cpp 按 0/1 读）。纯 decompile 侧：recover.rs template_strings_of 从 const 池对或命令式 AllocArray+StoreOwnPropDyn 建列序列双解析（Mov 穿透、连续性校验、未知用法诚实回退）；发射=恒等 tag 反引号字面量逐字带 raw（`((_=>_)`a${0}b`)`，${0}=惰性多段分隔符，连接处安全证明注释），cooked-only 仅 raw 真缺时兜底（逐案注释+计数）。零 lift/IR 改动=字节保真按构造。黄金 g01–g10 + t16 更新。门禁逐字 **1131/0/0/18/0**（1095+36），floor 提升，determinism 复验，fmt 净，远程 workspace 127 套件绿零 warning，36 fixture node --check + node 行为逐字节对齐 oracle） |
| d-P11 | C2 生成器/异步管道 | 18 fixture：生成器协议状态机重建为 async/function* 体（最贵） | **完成**（生成器族全关——门禁逐字 **1149/0/0/0/0 全量通过**，expected-fallback 桶清零，decompile 轨道收官。vendor 降级模型坐实：es2panda generatorFunctionBuilder.cpp Prepare/Yield/CleanUp + functionBuilder.cpp SuspendResumeExecution/resumeGenerator/HandleCompletion，运行时 GeneratorResumeMode{RETURN=0,THROW=1,NEXT=2}；六版本两形态（baseline/debug=内联立即数、optimized=共享常量 temp）。folds::generator_machine_fold（先于其余 Stage-B fold 运行=dispatch 统一为 if 链）整机消除：入口协议 suspend、CreateIterResultObj(v,false) 解包、Resume/GetResumeMode 完成对、resume-mode dispatch 消解为 continuation；resume 值有真实用途时绑 `const t = yield v`；按函数 all-or-nothing 以入口点为闸门（g05 钉），未匹配站点保留响亮回退；funcObj+模式立即数常量仅零引用时清扫。语料计数 gen_driver_sites=54 entry=18 bound=0。异步族保持记录回退=**新 IR gap G6**（现代 asyncfunctionawaituncaught/resolve/reject 值在 acc（isa.yaml acc:inout:top），lift 只建 funcobj 寄存器——值根本不到 IR，无 sound 的 decompile 侧 fold；异步 fixture 门禁 not-applicable 故零行成本；修复=lift 加 acc 操作数，按 G6 记录请求，decompile 轨道不动 lift）。黄金 g01–g06（内联/共享常量、绑定 yield、循环内 yield、入口闸门 bail、异步诚实底）。floor 1131→1149，determinism 复验，fmt 净，远程 workspace 绿零 warning，node --check 40/40） |
| d-P13 | N68 残余：异步状态机完整 fold（d-P12 登记项） | ✅ 完成（见 d-P12 行续记；AsyncGenerator kind 残余🔲注册见下行） |
| d-P14 | AsyncGenerator kind（async function*：CreateGeneratorObj 入口 + AsyncGeneratorResolve/yield 机）fold——d-P13 登记的站立残余（语料残余 fallback：ResumeGenerator 12、GetResumeMode 9、Param(funcobj) 3；黄金 a07 钉住 bail） | ✅ 完成（worker d-P14：folds::async_generator_machine_fold 整机消除 async function* 机械——vendor 模型 asyncGeneratorFunctionBuilder Prepare/Yield/DirectReturn/ExplicitReturn/CleanUp + functionBuilder Await/AsyncYield/HandleCompletion（ResumeMode RETURN=0/THROW=1/NEXT=2；运行时 ASYNCGENERATORRESOLVE v0=gen/v1=value/v2=done，js_generator_object.h GeneratorResumeMode）。CreateAsyncGeneratorObj 入口协议 suspend 消解；`yield v` 三段（pre-await + 死 AsyncGeneratorResolve yield 点 + 三向 dispatch：RETURN 臂 await 后 done=true 完成、THROW 臂 throw、NEXT=continuation）折回 plain `yield`（resume 值有真实用途时绑 `x = yield v`）；源码级 await 走 d-P13 站点（yield-point 守卫：pre-yield await 绝不脱离其 yield 机械单独折叠）；`return {value: genobj, done: X}`（lift v0.1-parity 的 asyncgeneratorresolve 折叠形态）→ `return X`；显式 return 的 await（ExplicitReturn，无 HandleCompletion）一并消解；catch-all AsyncGeneratorReject 由 async_driver_fold 折 throw。按函数 all-or-nothing 入口闸门。语料直方图 **ResumeGenerator 12→0、GetResumeMode 9→0、Param(funcobj) 3→0**（functions_with_fallbacks 51→48），agen_entry=3/yields=3/awaits=3/returns=6；梦想门禁 1149/1149 全桶零；黄金 ag01–ag04 红先行（plain yield、await+绑定 yield+显式 return、三向 sabotage per-site bail、入口闸门 bail；a07 转为无入口 suspend 形态的闸门 bail 钉）；node 行为证据 I:3/J:1/7/K:5/false/42/true（for-await 累积、yield 链贯穿拒绝、send-value/await/显式 return）+ 3 语料输出 node --check。yield*（YieldStar）语料无载体，保持响亮回退） |

| d-P15 | yield\*（YieldStar 委托）fixture + fold | ✅ 完成（9fd9791 起 6 commit；**fixture 从零造**（5 个手写源，镜像 es2abc 24.0.0.0 编，独立目录 decompile-fixtures/yield-star/，语料不动）；vendor 模型 functionBuilder.cpp YieldStar:177-342（ResumeMode 三向 + IteratorClose 管道 + 委托穿透 suspend）实证于自带 pandasm；fold 覆盖同步/异步 × 裸兄弟/try 碎块两种结构化形态；**orchestrator 独立复验**：node 四组精确 stdout 复现、梦想门禁 1149/1149 不动、fmt 净、workspace 零失败零警告。**新发现登记见 N69/N70**） |
| N69 | **结构化器 try 碎片化 bug**（d-P15 发现）：try 区域横跨循环时被碎成"finally 式"连续片段，try 后的语句会在 catch 路径上错误执行——已有 known-issue 钉测试（yield_star_node_throw_main_known_fragmentation）；非 yield* 特有 | ✅ 修复（f88810e，d-P16：根因=emit_mixed 的 Seq 臂只在单层合并同 plan 子项，跨层嵌套的未保护 join 导致逐级碎片包装——d-P5 的 cut_classify 早就能分类 Seq 切口但驱动从未调用；修=Mixed Seq 走重命名的 emit_cut_try 提升，d-P5 全部相位 1 守卫不变。钉测试翻转为正确断言（node 实证 catch 路径不再跑到 try 后语句）；**语料计数器零移动**（2787 无此形状——这正是它存活的原因；载体是 d-P15 的 yield-star fixture）；orchestrator 复验：翻转钉绿、梦想门禁 1149 不动、fmt 净、136 套件绿零警告） |
| N70 | d-P13/d-P14 覆盖缺口：plain-async 的 for-await driver 形态（其 ResumeGenerator 读被消解的 AsyncFunctionEnter fallback → node 下静默断）——d-P15 的 (c) 证据因此走手写 driver 绕行 | ✅ 修复（d3cd676，d-P16：三层根因——①funcObj 经循环头 phi 别名到达机械（精确 temp 守卫失败）修=别名闭包 fixpoint 贯穿闸门/匹配/清扫；②循环内 dispatch 的 THROW 臂是 loop-exit break 到循环后 throw（非 d-P13 匹配的内联形）修=collect_loop_exit_throws 预验 + 接受 break 路由臂；③async_driver_fold 的 uses==1 闸门对 finally 式复制 catch-all 失败导致**拒绝被错误 resolve 成 resolve**——修=uses==declares 配对。node 实证 for-await driver 精确 stdout + 拒绝探针正确 reject。**残余登记**：driver 输出是正确可跑的 while 循环而非 pretty 的 for await 字面量（for_await_of fold 不匹配此形态——将来可读性增强）+ 死 loop-exit throw 保守保留（移除需整节点不可达分析）） |

| d-P17 | N70 残余两件：for-await pretty fold（driver 形态：头部含 await 临时量 + done 臂吞并循环后尾部）+ 死 loop-exit throw 清理（需整节点不可达分析） | worker d-P17 (k3) | **完成**（5059825/071d0d6/09cc93d/a6ca98f/969ce02+1b1ab91；新兄弟匹配器 match_for_await_driver：头部 await 临时量必需形（for-await 本就 await next() 结果）+ done 臂尾部重归位 + 循环簿记 phi 不变量折叠 + 迭代器清理 try 接续折叠——driver 输出口字面量 `for await (const value of v10)` 形（黄金钉）；死 throw 清理=整节点不可达证明（seq_flow/node_flow、标签跳转 bail、异常边推理），s40/s41 保留钉。**orchestrator 独立复验**：梦想门禁 1149/1149 不动、node stdout 逐字节不变（含新拒绝探针）、语料计数器零移动、fmt 净、731 测试绿零警告）**残余清零** |

| t-P1 | E6 评估基建 | 带人工标注真实污点的 fixture 集（爬级触发器的可信基线） | **完成**（0716d7b/4f0a27f/86869b7 等 5 commit：22 探针 5 族 + annotations.json ground truth（VM 实跑校验）+ gen-taint-probes.py 生成器 + probes.rs runner（expected-FN 消失会强制失败=爬级仪器）。基线表 tp=11 fp=4 fn=4：4 个 expected-FP（a4/a5/b2/c2）+ 4 个 known-FN（b3→rung1、c4→rung2、d4→rung2、e5→rung1）全部带 closes_at_rung 标注。附带抓到并修复 N66（orchestrator 复验全绿）） |
| t-P2 | E1 rung-1 引擎 | Boomerang 形按需别名查询（AliasOracle 接缝后的真引擎） | **完成**（570004c/f911ee0/ee08231；记忆化反向 points_to（深度上限 8 + rung-0 声底回退、heros 平衡括号逐查询上下文栈、帧槽绑定穿过参数）、CallGraph::refine_with_points_to 第二消费者、ABCD_TAINT_RUNG A/B 开关。**探针 tp 11→13 / fp 4→2 / fn 4→2 violations=0**（a4/a5 翻 clean、b3/e5 翻 tp、b2 诚实重标 rung-2 环境身份）。**orchestrator 独立复验**：探针表逐字复现 + A/B rung-0 复现三处引擎依赖条目、冒烟逐字节不变（桥接 5517 未知点零触发=语料 callee 全是全局加载的诚实归因）、125 套件绿） |
| t-P3 | E3 原型链摘要查找 | points-to 驱动的接收者类型近似（依赖 t-P2） | **完成**（71b9e5d/be96a74/ca050b7/c810fb0；abcd-taint/src/prototype.rs 新模块：分配点种类→原型族 + 常量链 + **全局存储出处**（语料关键件）+ GetIterator→Iterator.prototype；优先级=直接名→用户体→原型族→保守保留（additive-only，从不 exclusive）；注册 Array.pop/push、String.charCodeAt/repeat/slice、Iterator.next/return。**orchestrator 独立复验**：探针 tp=16 fp=3 fn=2 violations=0（5 新探针，22 旧探针逐字复现）、冒烟计数器 lookups 7626→10254/unknown 357→69（Iterator 收编 288）逐字复现、charCodeAt/pop 出缺失榜/s.next 诚实留守、125 套件绿零 warning） |
| t-P4 | E4 mini-gap 完整传播器 | 摘要暂停/回调/恢复（高阶内置函数摘要的前置） | **完成**（ed689e5/bf460f0/6ac35b9/e5308fa；gap.rs：counter-free 静态扫描 + GapCallGraph 只包求解器图 + 进入臂按 N66 帧槽播种（exclusive 杀 callee 体不杀 gap 边）+ 返回臂按 return_to_result 接回；forEach/map/filter 三件套注册；e13 诚实标注 expected-fp（机制孪生证明返回通道静默，命中来自既有 unknown-base 通配）。**orchestrator 独立复验**：探针 tp=20 fp=4 fn=2 violations=0（6 新 gap 探针，27 旧探针逐字复现）、冒烟两配置逐字节不变（TAINT-GAPS 0/0，语料 trio 零出现的字节扫描归因）、fmt 净、126 套件绿零 warning） |
| t-P5 | E5 摘要库扩展 | miss 计数器驱动；真实 @ohos.* API（待真实应用语料） | **完成**（8de0966/8cb7101/00bd315/57ab5fb；replace 双形态注册（字符串形=Base+Param(1)→Return；函数形=gap 机制空链返回——探针+机制双钉）；二线=RegExp.prototype.test（**新解析臂：es2abc 六版本全部把正则字面量降级为 `new RegExp(...)`——构造器结果族**）+ split/join/parseInt（可达性证据为零的预防注册）+ Object.assign 结果恒等流；**exclusive 政策落地**（默认 NO；白名单=纯判定/纯变换；发现 parseInt 必须 non-exclusive——killSource 会 FN SSA 复用形）；backlog 分类写入 README（用户全局/生成器不透明/类实例 CG 缺口/混淆伪影——防后人追错）。**orchestrator 独立复验**：探针 tp=30 fp=4 fn=2 violations=0、冒烟计数器逐字复现（replace+r.test 出缺失榜、unknown 69→51、native_keep 942→924、edges 不变）、fmt 净、workspace 零失败零 warning） |
| t-P6 | E2 rung-2 PTA | APAK 形上下文敏感指针分析（阶段级；触发器：分发误报实证） | **完成**（dd65b48/3dfb4fc/6883801/768bcf0；abcd-analysis/src/dataflow/pta.rs：对象按 (alloc InstId, 1-call-site ctx) 键控 + 逐对象字段桶 + delta 传播 + **调用图/PTA 协同演化不动点**（无 CHA 回退=字节码无声明类型，函数值一等公民）+ NewLexEnv 环境身份通道 + 25M 步预算响亮降级。探针三级严格超集：r0 tp=28/viol=10 → r1 tp=30/viol=5 → **r2 tp=32 fp=1 fn=0 viol=0**（b2/c4/d4/e7/e13 全关，c2 锋利化 wontfix）。**orchestrator 独立复验**：三级探针表复现、RUNG2-HISTOGRAM resolved 345→1533/PTA 计数器/确定性复现、正控首次移动 18→126 fixture 36→234 hits 复现、冒烟 body_step 108→810/native_keep 924→222 复现、fmt 净、workspace 零失败零 warning；默认 alias_rung=2（0/1 可切）） |
| d-P12 | N68/G6 异步 acc 值缺口 | abcd-lift 现代 async 族（awaituncaught/resolve/reject）改读 acc 为值、v0=funcobj（vendor interpreter-inl.cpp:5357-5366 实证）+ lower 字节中性证明 + abcd-decompile 异步 fold（AsyncResolve→return/AsyncReject→throw/AwaitUncaught→await）；证据层：字节恒等 + pandasm 逐指令 + node --check/行为（VM 对异步 not-applicable，dream gate 重编译须零语法错） | worker d-P12 (k3) | **完成**（da1f3c0 红探针/6e44ce3 核心修复/efc1dd2 异步 fold/e810dfd 证据；三 op 加 funcobj 字段（lower 必须重发 v0）；deprecated resolve/reject 还抓出**中寄存器误绑**（vendor 读最后槽，中间仅日志）+ asyncgeneratorreject 同款 gap。证据驱动偏差：21 个异步 fixture 的字节恒等前提被证伪——pre-fix 重写本就有语义残缺（acc 数据流断裂），pandasm 逐行归因；其余 3426 文件 0 差异。**orchestrator 独立复验**：梦想门禁 1149/1149 全桶零（206s 本地端到端）、corpus_lower_async 绿、pandasm 2.69M 指令 0 mismatch、探针 tp=32 fp=1 fn=0 不变、fmt 净、132 套件零 warning；node 行为证据 A:42/B:7/C:5 精确断言。**N68 残余已由 d-P13 接续关闭**（557e5cb/79d3215/aea1069/9533cd7：async_machine_fold 整机消除异步 suspend/resume 机械——vendor 模型 asyncFunctionBuilder+Await/HandleCompletion（ASYNC kind 的 dispatch 只有 THROW 臂）；fallback 直方图 AsyncFunctionEnter 18→0、SuspendGenerator 18→0、GetResumeMode 27→9、ResumeGenerator 30→12（残余=AsyncGenerator kind，已注册）；orchestrator 独立复验：梦想门禁 1149/1149 全桶零（213s 自跑）、直方图逐字复现、fmt 净、133 套件绿零 warning）） |

顺序：d-P5→d-P6→d-P7→d-P8→d-P9→d-P10→d-P11→t-P1→t-P2→t-P3→t-P4→t-P5→t-P6（E 系由触发器把关，顺序反映依赖与成本）。

**维护者决策（2026-09-20）**：D2（inline 是否在 v0.2 IR 上重写）**排在 v2-P3 之后**再议——pass 框架落地后才有讨论内联的基座；D3（死 FFI 表面 108/324）**拍板保留**，对账表已核销。v2-P2 启动前按约定暂停，等维护者发话。

**维护者决策（2026-09-21，v2-P3 关门后）**：**D2 = inline 要**——在 v0.2 IR 上重写（v2-P3b 任务，按构造消灭 N44：参数映射/前驱重建/try 区域保留/verifier 洁净）；**P4 = v1 不留档**——swap 时 abcd-ir crate 直接删除（git 历史即留档），parity 对照器/语料 driver 等 v0.1 依赖物随之一并退役。 |

**维护者决策（2026-09-25，测试质量评估后）**：① **90% 口径 = 我们的代码、含语料全量**（nightly coverage-true artifact；当前地板：我们的 Rust 84.38% 已经 orchestrator 复现）；**同日修正：桥接 C++ 留在分母**——自己写的代码自然要测，靠上层 Rust 驱动覆盖；可证死的面走 q-P1 删除而非排除；分母只排除 vendored `**/arkcompiler_runtime_core/**`（R4）；② 委托桥接死代码详析（量化可删面 + 证明厂商必要逻辑已全部经活导出可达 → q-P1）；③ 批准六个廉价弱测试修复（W1/W4/W5/W6/W8/W9 → q-P2；红先行纪律：W5 的 hits==0 与 W8 的零-skip 门须先验证不变量当前成立方可落地）。

| q-P1 | 桥接 C++ 死面详析 | 只读分析：逐符号盘点两 -sys 桥接导出 × Rust FFI 引用映射；区分"Rust 不引用"（可删）与"引用但罕执行"（保留）；量化删除面；证明厂商必要逻辑全覆盖 | worker q-P1 (k3) | **完成**（571cbbb，design/bridge-surface-analysis.md：332 导出=LIVE 226+TEST-ONLY 6+DEAD 100（isa 25+abc 75）；可删 ≈852-950 行（isa 248/abc 604；行距边界系统性少计 1 行已勘正）；历史 108/324 漂移对账（+8 活导出、8 旧死转活/转测试钉）；完备性双向证明：37 组必需 vendor 能力全有活导出链、Rust 仅经 bindgen 白名单触达 vendor、零缺失；file.cpp 排除后 File 方法并入 file_bridge.cpp:137-309=链接必需不可删；TEST-ONLY 6 保留钉 #A8/#B3/#16。删后桥接覆盖率估算 59%→~76%CI/~77%含语料。**orchestrator 独立复验**：导出计数/分类抽查/行数求和/build.rs 排除与白名单/无 feature 逐项复现） |
| q-P2 | 六弱测试修复 | W1 version 断言 / W4 探针命中行号 / W5 hits==0 门（先验当前零命中）/ W6 inline 确定性默认开 / W8 零-skip 门（先验当前零 skip）/ W9 spawn-to-probe + node --check 转致命 | worker q-P2 (k3) | **进行中** |
