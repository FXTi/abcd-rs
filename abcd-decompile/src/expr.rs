//! The Stage-A expression tree (design/decompile.md §4.1).
//!
//! This is an *internal* model — d-P3/d-P4 consume it for structuring and
//! emission; it is NOT final JS text. Every node corresponds to a row of
//! the §5 fitness table; nodes for ops whose surface-syntax reconstruction
//! is a later-stage fold rule carry their operands verbatim plus a
//! documented fallback/plumbing status ([`NodeStatus`]).
//!
//! Precedence metadata: [`Expr::precedence`] gives the JS operator
//! precedence of the node's root (higher binds tighter; `u8::MAX` for
//! primary expressions) so the Stage-C printer can parenthesize correctly.
//! The Stage-A debug dump ([`crate::dump`]) prints fully parenthesized and
//! therefore never relies on it.

use abcd_ir::id::{ConstId, FuncId, ValueId};
use abcd_ir::module::FunctionKind;
use abcd_ir::op::{BinOp, CallKind, CmpOp, UnOp};

/// How faithfully a node expresses its source op (the fallback-honesty
/// bookkeeping behind the corpus coverage histogram).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NodeStatus {
    /// Direct surface-syntax mapping (fitness class T) or a complete
    /// Stage-A reconstruction of an N-class op.
    Expressed,
    /// A desugaring-plumbing node: semantics preserved verbatim, but the
    /// idiomatic surface form (`for…of`, literal fold, …) is a d-P3 fold
    /// rule. The node keeps every operand so the fold loses nothing.
    Plumbing,
    /// A documented fallback (fitness class H, or an N-class reconstruction
    /// Stage A cannot complete). Loud, never silent (gen1 lesson 6).
    Fallback,
}

/// A literal, rendered from [`abcd_ir::Const`] trees.
#[derive(Clone, Debug, PartialEq)]
pub enum Lit {
    /// `undefined`.
    Undefined,
    /// The TDZ hole — has no JS surface syntax; rendered as an annotated
    /// `undefined` by the emitter (a hole read is itself a compiler
    /// artifact the guard-elision rules remove).
    Hole,
    /// `null`.
    Null,
    /// A boolean literal.
    Bool(bool),
    /// A number literal as raw `f64` bits (NaN payloads and `-0.0` are
    /// preserved; [`crate::consts::render_number`] prints the shortest
    /// round-trip form).
    Number(u64),
    /// A string literal (unescaped content).
    String(String),
    /// A BigInt literal (decimal repr; printed `n`-suffixed).
    BigInt(String),
    /// An array literal shape (`createarraywithbuffer`).
    Array(Vec<Lit>),
    /// An object literal shape (`createobjectwithbuffer`): `(key, value)`
    /// in source order.
    Object(Vec<(Lit, Lit)>),
    /// A reference to a function in the module's function table (class
    /// member buffers). Emission-level construct — d-P4 resolves it to
    /// the method body.
    MethodRef(FuncId),
}

/// An expression-tree node.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    /// A literal.
    Lit(Lit),
    /// A resolved identifier (global, lexical binding, `arguments`, the
    /// function's own name, …). Already legalized.
    Ident(String),
    /// A reference to a Stage-A temporary (an SSA value that was not
    /// inlinable). The name is legalized and unique within the function.
    Temp {
        /// The SSA value behind the temporary (provenance for d-P3).
        value: ValueId,
        /// The legalized temporary name.
        name: String,
    },
    /// `object.name` (name legalized; emitted as `obj["name"]` by Stage C
    /// when the name is not a legal identifier — [`Expr::PropName`] keeps
    /// the RAW name and [`Expr::PropNameLegal`] flag for that decision).
    PropName {
        /// The receiver.
        object: Box<Expr>,
        /// The raw property name.
        name: String,
        /// Whether `name` survived the legalizer unchanged (Stage C may
        /// then use dot form; otherwise computed-string form).
        dot_legal: bool,
    },
    /// `object[index]` with a (usually constant) index.
    PropIndex {
        /// The receiver.
        object: Box<Expr>,
        /// The index.
        index: Box<Expr>,
    },
    /// `object[key]` with a computed key.
    PropDyn {
        /// The receiver.
        object: Box<Expr>,
        /// The computed key.
        key: Box<Expr>,
    },
    /// `object.#name` (private load). The name is resolved through the
    /// private-name registration when possible; otherwise a synthetic
    /// `#p{level}_{slot}` fallback (cosmetic, documented).
    PrivateLoad {
        /// The receiver.
        object: Box<Expr>,
        /// The private name (WITHOUT the leading `#`).
        name: String,
    },
    /// `#name in object`.
    PrivateTest {
        /// The receiver.
        object: Box<Expr>,
        /// The private name (WITHOUT the leading `#`).
        name: String,
    },
    /// `super.name` / `super[key]` (load).
    SuperProp {
        /// `Some(name)` for the named form, `None` + `key` for dynamic.
        name: Option<String>,
        /// The dynamic key (iff `name` is `None`).
        key: Option<Box<Expr>>,
    },
    /// A call. `kind` is kept verbatim for Stage C; the *shape* is already
    /// normalized here per the §5.3 binding table:
    ///
    /// - `Direct`/`Dynamic` → plain `callee(args…)` (`this` recorded;
    ///   `Dynamic` has `this: None`).
    /// - `Apply` → the `.apply(this, argsArray)` shape (`args` is exactly
    ///   `[array]`, `this` is `Some`).
    /// - `New` → `new callee(args…)` (`this: None`).
    /// - `Super*` → the `super(…)` shapes (`callee` is the `super` marker;
    ///   see [`Expr::SuperMarker`]).
    Call {
        /// The callee expression.
        callee: Box<Expr>,
        /// The `this` binding, when the kind carries one.
        this: Option<Box<Expr>>,
        /// The argument expressions, in order.
        args: Vec<Expr>,
        /// The call kind (verbatim from the IR).
        kind: CallKind,
    },
    /// The `super` callee marker (the callee of a `Super*` call).
    SuperMarker,
    /// `import(specifier)`.
    DynamicImport {
        /// The module specifier expression.
        specifier: Box<Expr>,
    },
    /// A unary operation (incl. `delete` via [`UnOp`] extension — see
    /// [`Expr::Delete`] for delete; Inc/Dec are PREFIX forms here).
    Unary {
        /// The operator.
        op: UnOp,
        /// The operand.
        operand: Box<Expr>,
    },
    /// `delete object[key]`.
    Delete {
        /// The target member expression.
        target: Box<Expr>,
    },
    /// A binary arithmetic/bitwise operation.
    Binary {
        /// The operator.
        op: BinOp,
        /// The left operand.
        left: Box<Expr>,
        /// The right operand.
        right: Box<Expr>,
    },
    /// A comparison (incl. `in` / `instanceof`).
    Compare {
        /// The operator.
        op: CmpOp,
        /// The left operand.
        left: Box<Expr>,
        /// The right operand.
        right: Box<Expr>,
    },
    /// `/pattern/flags`.
    RegExp {
        /// The pattern source.
        pattern: String,
        /// The flag string (`dgimsuy` subset, canonical order).
        flags: String,
    },
    /// An object literal from an `AllocObject` shape constant. The
    /// following own-store/spread sequence targeting the same value is
    /// kept as statements (the FOLD into this node is d-P3's desugar
    /// rule; [`crate::recover::builder_hook`] exposes it).
    ObjectLit {
        /// `(key, value)` entries from the shape.
        entries: Vec<(Lit, Lit)>,
    },
    /// An array literal from an `AllocArray` shape constant (`[]` when
    /// the shape is absent).
    ArrayLit {
        /// The elements.
        elements: Vec<Lit>,
    },
    /// A closure: a DEFERRED reference to the body [`FuncId`] (emission-
    /// level construct — d-P4 emits the body). `kind` selects the
    /// `function`/`function*`/`async function`/`async function*` prefix.
    Closure {
        /// The body in the module's function table.
        body: FuncId,
        /// The function's own name (display; legalized at emission).
        name: String,
        /// The function kind (verbatim).
        kind: FunctionKind,
        /// `(name, value)` captured bindings (documentation of the free
        /// variables; the values are expression trees).
        captures: Vec<(String, Expr)>,
    },
    /// A class definition: a DEFERRED reference to the ctor [`FuncId`]
    /// plus the member-buffer constant (d-P4 emits the class body).
    Class {
        /// The constructor.
        ctor: FuncId,
        /// Display name (the ctor's name; legalized at emission).
        name: String,
        /// The `extends` expression, when present.
        heritage: Option<Box<Expr>>,
        /// The member-buffer constant.
        members: ConstId,
        /// `true` for `DefineSendableClass` — fitness class H (no JS
        /// surface syntax); emitted as `class` + `/* sendable */`
        /// annotation at best. Reported as a hard-7 fallback.
        sendable: bool,
    },
    /// `yield value` (the `SuspendGenerator` op). The result is the
    /// resume value — Stage C prints the `x = yield v` form when the
    /// result is used. The `genobj` operand is generator-driver plumbing
    /// and is not kept (its definition, `CreateGenerator`, folds with
    /// `DefineFunc` + `FunctionKind::Generator` at d-P3).
    Yield {
        /// The yielded value.
        value: Box<Expr>,
    },
    /// `await value`. `uncaught` records the `AwaitUncaught` form (the
    /// caught-completion wrapper is machine-level and elided).
    Await {
        /// The awaited value.
        value: Box<Expr>,
        /// Whether the source op was `AwaitUncaught`.
        uncaught: bool,
    },
    /// `new.target`.
    NewTarget,
    /// `globalThis`.
    GlobalThis,
    /// The currently executing function object (`LoadFunction`) — the
    /// function's own name where known.
    SelfFunction(String),
    /// The unmapped `arguments` object.
    Arguments,
    /// `CopyRestArgs` — the rest-parameter array (`...rest` at
    /// `start_index`). Parameter-list reconstruction is d-P3/C.
    RestArgs {
        /// Index of the first rest argument.
        start_index: u16,
    },
    /// `GetTemplateObject` — template-literal reconstruction. IR gap G4
    /// (registered by d-P0): the raw-vs-cooked distinction is not
    /// verifiably preserved in the const pool, so this node is
    /// **cooked-only** (semantically equal for the VM gate, cosmetically
    /// lossy). Cache identity is elided by design.
    TemplateObject {
        /// The cooked template strings, when the literal operand resolved
        /// to a const string array.
        cooked: Option<Vec<Lit>>,
    },
    /// `{ value, done }` — the iterator result object. Invisible in
    /// source after the for-of fold (d-P3); kept verbatim meanwhile.
    IterResultObj {
        /// The iteration value.
        value: Box<Expr>,
        /// The done flag.
        done: Box<Expr>,
    },
    /// Desugaring-plumbing nodes for the iteration protocols. Each keeps
    /// its operand verbatim; d-P3 folds the shapes into `for…of` /
    /// `for await…of` / `for…in` / manual `.next()`.
    Iter {
        /// Which protocol op this was.
        op: IterOp,
        /// The object/iterator operand.
        obj: Box<Expr>,
        /// Status: `IteratorReturn`/`IteratorThrow` are fitness class H
        /// (iterator-cleanup protocol) and reported as hard-7 fallbacks.
        status: NodeStatus,
    },
    /// `CreateGenerator` — the generator object for a closure. Plumbing:
    /// folds with `DefineFunc` + `FunctionKind::Generator` at d-P3.
    CreateGenerator {
        /// The closure value.
        func: Box<Expr>,
    },
    /// `ResumeGenerator` / `GetResumeMode` — generator-driver plumbing,
    /// fitness class H (the state-machine encoding; folding it back into
    /// plain `yield` is d-P3 pattern work, R4). Kept as explicit fallback
    /// nodes.
    GeneratorDriver {
        /// `true` for `ResumeGenerator`, `false` for `GetResumeMode`.
        resume: bool,
        /// The generator object.
        genobj: Box<Expr>,
    },
    /// `AsyncResolve` / `AsyncReject` — async promise plumbing, fitness
    /// class H (R4). Explicit fallback nodes.
    AsyncDriver {
        /// `true` for resolve, `false` for reject.
        resolve: bool,
        /// The resolution value / rejection reason.
        value: Box<Expr>,
    },
    /// `CopyDataProps` (object spread plumbing): folds into a literal
    /// `{...src}` at d-P3; standalone fallback is `Object.assign`-style
    /// (semantics differ subtly — prefer the fold).
    CopyDataProps {
        /// Destination.
        dst: Box<Expr>,
        /// Source.
        src: Box<Expr>,
    },
    /// `SetObjectWithProto` — `__proto__: proto` inside a literal at
    /// d-P3 (the no-setter semantics match the op; a standalone
    /// `Object.setPrototypeOf` fallback is NOT identical — commented
    /// instead).
    SetObjectWithProto {
        /// The object whose prototype link is set.
        obj: Box<Expr>,
        /// The new prototype.
        proto: Box<Expr>,
    },
    /// `ArraySpread` — `...src` inside an array literal / call-args
    /// reconstruction at d-P3. (The op's result, the new index, is
    /// machine plumbing.)
    ArraySpread {
        /// The destination array.
        dst: Box<Expr>,
        /// The start index.
        index: Box<Expr>,
        /// The source iterable.
        src: Box<Expr>,
    },
    /// `CreateObjectWithExcludedKeys` — rest destructuring
    /// `{a, b, ...rest}` reconstruction at d-P3 (with the sibling
    /// excluded-key loads).
    RestObject {
        /// The source object.
        obj: Box<Expr>,
        /// The excluded key values.
        excluded: Vec<Expr>,
    },
    /// `DefineGetterSetterByValue` — computed-key accessor definition;
    /// folds into literal/class bodies at d-P3.
    DefineGetterSetter {
        /// The target object.
        obj: Box<Expr>,
        /// The computed key.
        key: Box<Expr>,
        /// The getter closure.
        getter: Box<Expr>,
        /// The setter closure.
        setter: Box<Expr>,
    },
    /// `GetModuleNamespace` — the namespace object of an imported module
    /// (ties to `import * as ns` at d-P4).
    ModuleNamespace {
        /// The module slot.
        index: u32,
    },
    /// A Stage-B folded object literal: an `AllocObject` shape plus the
    /// absorbed own-store/spread/proto/method sequence (the d-P3
    /// literal-fold desugar rule, design §4.2.6). Not produced by
    /// Stage A; [`crate::folds`] introduces it.
    ObjectBuild {
        /// The entries, in source order.
        entries: Vec<ObjEntry>,
    },
    /// A Stage-B folded array literal (same provenance as
    /// [`Expr::ObjectBuild`]).
    ArrayBuild {
        /// The elements, in source order.
        elements: Vec<ArrayElem>,
    },
    /// The documented fallback node: an op Stage A could not map, with
    /// its operand expressions kept verbatim. Loud, never silent.
    Fallback {
        /// The op name (static, from the fitness table).
        op: &'static str,
        /// Why this is a fallback.
        note: &'static str,
        /// The operand expressions.
        operands: Vec<Expr>,
    },
}

/// One entry of a Stage-B folded object literal ([`Expr::ObjectBuild`]).
#[derive(Clone, Debug, PartialEq)]
pub enum ObjEntry {
    /// `key: value` with a literal key (identifier/string/number form
    /// chosen by the emitter).
    KeyValue(Lit, Expr),
    /// `[computed]: value`.
    Computed(Expr, Expr),
    /// `...src` (`CopyDataProps` inside the builder sequence).
    Spread(Expr),
    /// `__proto__: proto` (`SetObjectWithProto`; the no-setter semantics
    /// match the op exactly).
    Proto(Expr),
    /// `name() { … }` (`DefineMethod`; `func` is the closure node).
    Method(String, Expr),
}

/// One element of a Stage-B folded array literal ([`Expr::ArrayBuild`]).
#[derive(Clone, Debug, PartialEq)]
pub enum ArrayElem {
    /// A plain element.
    Item(Expr),
    /// `...src` (`ArraySpread`).
    Spread(Expr),
}

/// The iteration-protocol op behind an [`Expr::Iter`] node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IterOp {
    /// `GetIterator` (for-of protocol lookup).
    GetIterator,
    /// `GetAsyncIterator` (for-await protocol lookup).
    GetAsyncIterator,
    /// `IteratorNext` (advance).
    Next,
    /// `IteratorReturn` (early-exit cleanup; fitness class H).
    Return,
    /// `IteratorThrow` (cleanup family; fitness class H).
    Throw,
    /// `GetPropIterator` (for-in enumeration).
    GetPropIterator,
    /// `NextPropName` (for-in binding update).
    NextPropName,
}

impl Expr {
    /// The JS operator precedence of this node's root (higher binds
    /// tighter; 20 = primary). Metadata for the Stage-C printer; the
    /// Stage-A dump prints fully parenthesized.
    ///
    /// Levels follow the MDN/ECMA-262 table: 2 = `,` · 3 = `=` ·
    /// 4 = `?:` · 5 = `??` · 6 = `||` · 7 = `&&` · 8 = `|` · 9 = `^` ·
    /// 10 = `&` · 11 = equality · 12 = relational/`in`/`instanceof` ·
    /// 13 = shifts · 14 = `+ -` · 15 = `* / %` · 16 = `**` ·
    /// 17 = unary · 18 = postfix · 19 = `new`/call/member · 20 = primary.
    pub fn precedence(&self) -> u8 {
        match self {
            Expr::Binary { op, .. } => match op {
                BinOp::Exp => 16,
                BinOp::Mul | BinOp::Div | BinOp::Mod => 15,
                BinOp::Add | BinOp::Sub => 14,
                BinOp::Shl | BinOp::Shr | BinOp::Ashr => 13,
                BinOp::BitAnd => 10,
                BinOp::BitXor => 9,
                BinOp::BitOr => 8,
            },
            Expr::Compare { op, .. } => match op {
                CmpOp::Eq | CmpOp::NotEq | CmpOp::StrictEq | CmpOp::StrictNotEq => 11,
                _ => 12,
            },
            Expr::Unary { .. } | Expr::Delete { .. } | Expr::Await { .. } => 17,
            // `yield` parses as an AssignmentExpression: as the operand of
            // any real operator it MUST be parenthesized (`yield v + w`
            // means `yield (v + w)`).
            Expr::Yield { .. } => 2,
            // Object literals are not PrimaryExpressions at statement /
            // member position; giving them the lowest precedence makes the
            // printer parenthesize them inside any operator context (the
            // statement-position rule lives in the emitter).
            Expr::ObjectLit { .. } | Expr::ObjectBuild { .. } => 0,
            // A `function` expression as a callee/operand parenthesizes
            // (`function f(){}()` is a declaration + error, not a call).
            Expr::Closure { .. } => 1,
            Expr::Call { .. }
            | Expr::PropName { .. }
            | Expr::PropIndex { .. }
            | Expr::PropDyn { .. }
            | Expr::PrivateLoad { .. } => 19,
            _ => 20,
        }
    }

    /// The node's Stage-A status for the coverage histogram (nodes not
    /// carrying an explicit status are [`NodeStatus::Expressed`] —
    /// plumbing nodes carry [`NodeStatus::Plumbing`] explicitly).
    pub fn status(&self) -> NodeStatus {
        match self {
            Expr::Iter { status, .. } => *status,
            Expr::GeneratorDriver { .. }
            | Expr::AsyncDriver { .. }
            | Expr::Class { sendable: true, .. }
            | Expr::Fallback { .. } => NodeStatus::Fallback,
            Expr::TemplateObject { .. }
            | Expr::IterResultObj { .. }
            | Expr::CreateGenerator { .. }
            | Expr::CopyDataProps { .. }
            | Expr::SetObjectWithProto { .. }
            | Expr::ArraySpread { .. }
            | Expr::RestObject { .. }
            | Expr::DefineGetterSetter { .. } => NodeStatus::Plumbing,
            _ => NodeStatus::Expressed,
        }
    }
}
