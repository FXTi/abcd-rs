# abcd-rs 反编译质量 TODO

与闭源反编译器对比后的差距清单。数据基于 `modules.abc` (华为相册) 反编译结果。

---

## P0 — 致命缺陷

### P0-1: class 语法恢复

**现状**: 输出 0 个真正的 `class` 定义，只有 22,608 个 `/* class */` 注释。所有方法被拆成扁平函数 `function constructor_X()` / `function methodName()`。

**闭源**: 2,279 个 `const rN = class X { ... }` 定义，覆盖 1,599 个文件，11,229 个方法归属到类内部。

**目标**:
- 识别 `defineclass` 指令，将 constructor + methods 合成为 `class X { constructor() {...} method() {...} }` 语法
- 消除 `func_main_0` 包装函数（当前每个文件都有），顶层代码直接内联
- 恢复 `const rN = class X { ... }; X = rN;` 模式

**示例**:
```javascript
// 当前输出
function func_main_0() {
    default = /* class */ PhotosAbilityStage;
    return;
}
function constructor_PhotosAbilityStage(...p1) {
    return super(......__rest_0);
}

// 期望输出
const r1 = class PhotosAbilityStage extends SharedAbilityStage_ {
  constructor(...p1) {
    super(...p1);
    return this;
  }
};
PhotosAbilityStage = r1;
```

**影响面**: 1,599 个文件 / 2,279 个类 / 11,229 个方法

---

### P0-2: 方法体丢失（跨块状态传递不完整）

**现状**: 42,269 个 `return;`（闭源仅 49 个），约 3,027 个函数体只有一行 `return;`。跨块累加器/寄存器传递已实现基础版本，但大量逻辑仍未恢复。

**闭源**: 使用 `return undefined;`（40,680 个）表示显式无返回值，方法体完整。

**根因分析**:
- 多前驱块（合并点）当前使用 `Undefined` 作为初始状态（保守策略），导致后续块丢失表达式
- try/catch 块的 handler 入口状态未正确初始化
- 某些指令（如 `callthisN` 的多步操作）跨块时中间状态丢失

**示例**:
```javascript
// 当前输出
function setResource(p1, p2, p3) {
    return this;  // 丢失了三次 addParam 调用
}

// 期望输出
setResource(p1, p2, p3) {
    this.addParam('objType', p1).addParam('objId', p2).addParam('objName', p3);
    return this;
}
```

**影响面**: ~3,027+ 个空函数，总代码量差 33%（629K vs 943K 行）

---

### P0-3: 无变量声明

**现状**: `let` 15 次、`const` 0 次、`var` 0 次。寄存器值直接内联或丢失。

**闭源**: `let` 14,260 + `const` 55,401 + `var` 6,514 = 76,175 个变量声明。

**目标**:
- 对每个函数体，分析寄存器使用模式，在函数开头生成 `let r2, r3, r4;` 声明
- 单次赋值的寄存器使用 `const`
- 词法变量（`stlexvar`/`ldlexvar`）使用 `var`
- 闭源格式: `let r2;` 在方法体开头，`const r42 = ...` 在首次赋值处

**示例**:
```javascript
// 当前输出
function addParam(p1, p2, p3) {
    if ((undefined !== p2) || (null === p2)) { ... }
}

// 期望输出
addParam(p1, p2, p3) {
    let r15, r18;
    if (p2 !== undefined) {
        if (p2 !== null) {
            const r12 = p3 === undefined;
            ...
        }
    }
}
```

**影响面**: 76,175 处

---

### P0-4: 匿名函数/闭包未内联

**现状**: 12,415 个 `/* func anonymous_0x1 */` 注释占位符，闭包体完全未反编译。

**闭源**: 17,511 个内联 `function (p1) { ... }` 匿名函数。

**根因**: `definefunc` / `definemethod` 创建的内部函数被当作独立顶层函数输出，未被内联到调用点（如 `.filter()`, `.reduce()`, `.map()` 的参数位置）。

**示例**:
```javascript
// 当前输出
function getReportableParams() {
    x_1_1 = new.target;
    x_1_2 = this;
    return Object.keys(x_1_2.params).filter(/* func anonymous_0x1 */).reduce(/* func anonymous_0x1__1 */, {});
}

// 期望输出
getReportableParams() {
    var x_1_2 = this;
    return Object.keys(x_1_2.params).filter(function (p1) {
      let r6;
      if (x_1_2.reportIgnoredParamKeys.has(p1)) {
        r6 = false;
      } else {
        r6 = true;
      }
      return r6;
    }).reduce(function (p1, p2) {
      p1[p2] = x_1_2.params[p2];
      return p1;
    }, {});
}
```

**影响面**: 12,415 处

---

## P1 — 重要缺陷

### P1-1: 无 label 控制流

**现状**: 9 个 `label_`。

**闭源**: 34,292 个 `label_N: { ... break label_N; }` 块。

ArkCompiler 大量使用 labeled block + break 来表达复杂分支（类似 switch-case fall-through、多层 if-else 的提前退出）。这是 structuring 阶段需要识别的模式。

**示例**:
```javascript
// 期望输出
label_0: {
    if (typeof p2 !== 'string') {
        if (typeof p2 !== 'number') {
            if (typeof p2 !== 'boolean') {
                this.params[p1] = JSON.stringify(p2);
                break label_0;
            }
        }
        this.params[p1] = String(p2);
    } else {
        this.params[p1] = p2;
    }
}
```

**影响面**: 34,292 处

---

### P1-2: 无继承关系 (extends / super)

**现状**: 0 个 `extends`，`super()` 调用被破坏为 `super(......__rest_0)`。

**闭源**: 1,023 个 `class X extends Y` + 正确的 `super(...p1)` 调用。

**根因**: class 合成时未解析 `defineclass` 的父类参数；`super` 调用的参数传递逻辑有 bug（spread 被重复）。

**影响面**: 1,023 处

---

### P1-3: export 不完整

**现状**: 2,570 行 export。

**闭源**: 10,771 行 export。

缺失约 76% 的导出语句。可能原因：
- module record 中的 local_export 未完全解析
- class 内部的 export 标记未传递
- 某些 indirect_export / star_export 未处理

**影响面**: ~8,200 处缺失

---

### P1-4: 条件逻辑错误

**现状**: 6,430 个 `if (true)` 永真条件（闭源 0 个）。

**根因**:
- `jeqz`/`jnez` 的条件恢复在某些模式下产生常量 `true`/`false`
- 布尔运算符错误：`||` 应为 `&&`（如 `(undefined !== p2) || (null === p2)` 应为 `(p2 !== undefined) && (p2 !== null)`，对应 `jeqz` 短路求值链）
- 条件表达式在跨块传递时退化为常量

**示例**:
```javascript
// 当前输出（错误）
if ((undefined !== p2) || (null === p2)) { ... }

// 期望输出
if (p2 !== undefined) {
    if (p2 !== null) { ... }
}
```

**影响面**: 6,430 处

---

## P2 — 语法问题

### P2-1: 破损的 spread 语法

**现状**: 964 个 `......`（六个点），应为 `...`（三个点）。

**根因**: `copyrestargs` + spread 参数传递时，`...` 被重复拼接。

**影响面**: 964 处

---

### P2-2: 错误的对象字面量 / 属性访问

**现状**: 7,591 个 `[0] =` 模式，对象字面量被错误解析为数组索引赋值。

**根因**: `createobjectwithbuffer` / `createarraywithbuffer` 的 literal array 解析时，内部 slot 信息（如 `[83886080]: 201351175`）被当作普通属性输出。这些是 ArkCompiler 内部的隐藏 class 元数据，不应出现在反编译结果中。

**示例**:
```javascript
// 当前输出（错误）
{ moduleTag: null, filter: null, [83886080]: 201351175, [65536]: 710570752 }

// 期望输出
{ moduleTag: 'EvntColl', filter: new JsonFilter_(...) }
```

**影响面**: 7,591 处

---

### P2-3: new.target 滥用

**现状**: 4,925 次 `new.target`（闭源 1,084 次）。

**根因**: 词法环境捕获（`ldlexenv` / `stlexenv`）被错误映射为 `new.target`。实际上很多场景应该是闭包的词法变量捕获。

**影响面**: ~3,841 处误用

---

### P2-4: func_main_0 包装函数

**现状**: 每个文件都有 `func_main_0()` 包装（1,939 个）。

**闭源**: 顶层代码直接内联，无包装函数。

**目标**: 将 `func_main_0` 的函数体提升为模块顶层代码。

**影响面**: 1,939 个文件

---

## 已完成

- [x] import 语句生成（~12,950 行，与闭源持平）
- [x] 文件路径还原（目录结构正确）
- [x] 基础 export 语句
- [x] 寄存器命名 (r1, p1 格式)
- [x] 函数参数恢复
- [x] rest 参数检测 (...pN)
- [x] 词法变量命名 (x_N_N 格式)
- [x] 基础跨块状态传递
- [x] 枚举模式恢复 (EventType 等)
- [x] 简单 getter/setter 方法
- [x] module record 解析
- [x] annotation 解析
- [x] debug info 解析
