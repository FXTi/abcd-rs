//! Module graph: the top-level program container (`design/ir.md`).
//!
//! A [`Module`] describes a *program*: classes, functions, value flow,
//! types, annotations, module records, debug info. It owns the shared
//! identity tables ([`SymbolTable`], [`ConstPool`]) and the global arenas
//! ([`Inst`], [`Block`], [`Value`]) that give ids module-wide uniqueness
//! (T1). It never describes a *file*: no `version`, no `file_type`, no
//! offsets, no register/acc numbering, no literal-array indices, no
//! multi-bucket retention streams, no `num_vregs`/`num_args`.

use crate::consts::ConstPool;
use crate::function::{Block, FunctionData, Inst, Value};
use crate::id::{BlockId, ClassId, ConstId, FieldId, FuncId, InstId, Sym, ValueId};
use crate::symbol::SymbolTable;
use crate::ty::Ty;

/// Semantic modifier set (replaces format-layer access-flag bit layouts).
///
/// One shared set for classes, methods, and fields; meaningless bits for a
/// given attach site are simply absent.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Modifiers(u32);

impl Modifiers {
    /// No modifiers.
    pub const NONE: Self = Self(0);
    /// `public`.
    pub const PUBLIC: Self = Self(1 << 0);
    /// `private`.
    pub const PRIVATE: Self = Self(1 << 1);
    /// `protected`.
    pub const PROTECTED: Self = Self(1 << 2);
    /// `static`.
    pub const STATIC: Self = Self(1 << 3);
    /// `final`.
    pub const FINAL: Self = Self(1 << 4);
    /// `abstract`.
    pub const ABSTRACT: Self = Self(1 << 5);
    /// The class is an interface.
    pub const INTERFACE: Self = Self(1 << 6);
    /// The class is an enum.
    pub const ENUM: Self = Self(1 << 7);
    /// The class is an annotation type.
    pub const ANNOTATION: Self = Self(1 << 8);
    /// `readonly` (ArkTS).
    pub const READONLY: Self = Self(1 << 9);

    /// Whether `other` is fully contained in this set.
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    /// Union of two sets.
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

impl std::ops::BitOrAssign for Modifiers {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = self.union(rhs);
    }
}

/// Calling-convention and execution dialect of a class or function (`D6`,
/// `design/ir.md`, `design/decisions.md`).
///
/// `abcd-ir` unifies dynamic JS/TS and static ArkTS under one SSA IR while
/// keeping their calling conventions explicit:
///
/// - [`Dialect::DynamicEcma`]: `es2abc` dynamic frames carrying hidden leading
///   `[func][new.target][this]` slots ([`crate::frame::FrameSlots::DEFAULT`],
///   `H = 3`, overridable per function via `L_ESCallTypeAnnotation;`).
/// - [`Dialect::StaticArkTS`]: `static_core` / `ets2panda` typed frames with
///   **zero** hidden closure or `new.target` slots (`H = 0` via
///   [`crate::frame::FrameSlots::NONE`] on `static` methods; explicit receiver
///   `this` at `params[0]` via [`crate::frame::FrameSlots::STATIC_INSTANCE`]
///   on instance methods and constructors).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Dialect {
    /// Dynamic ECMAScript / TypeScript (`es2abc` hidden-slot convention).
    #[default]
    DynamicEcma,
    /// Static ArkTS (`static_core` / `ets2panda` typed convention, `#36`).
    StaticArkTS,
}

/// The source language a class was authored in (semantic authoring provenance,
/// decoupled from container execution [`Dialect`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SourceLang {
    /// ECMAScript (JavaScript).
    EcmaScript,
    /// TypeScript.
    TypeScript,
    /// ArkTS (`static_core` / `ets2panda` or dynamic ArkTS).
    ArkTS,
}

/// Semantic function kind (replaces format-layer `FunctionKind`
/// encodings).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FunctionKind {
    /// A plain function or method.
    Function,
    /// A class constructor.
    Constructor,
    /// A getter.
    Getter,
    /// A setter.
    Setter,
    /// A generator function.
    Generator,
    /// An async function.
    Async,
    /// An async generator function.
    AsyncGenerator,
    /// An arrow function (the file's `NC_FUNCTION` — non-constructible,
    /// lexical `this`/`arguments`; concise methods are `None` at the
    /// file level, never NC).
    Arrow,
    /// An async arrow function (the file's `ASYNC_NC_FUNCTION`).
    AsyncArrow,
}

/// A declared signature (format fact #A7: absent on 12+/24 files, hence
/// `Option` on [`FunctionData::sig`]). A declaration, kept separate from
/// the analysis-level [`Ty`] on values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    /// Declared return type (`None` = no annotation).
    pub return_ty: Option<Ty>,
    /// Declared parameter types; may be shorter than the parameter list.
    pub param_tys: Vec<Ty>,
}

/// An annotation element value. Elements reference only IR-owned
/// identities (`design/ir.md`): constants, classes, fields, names.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AnnValue {
    /// A constant from the module's [`ConstPool`].
    Const(ConstId),
    /// A class in the module's class table.
    Class(ClassId),
    /// A field of a class in the module's class table.
    Field(ClassId, FieldId),
    /// A bare name (enum-ish/string-ish annotation payloads).
    Name(Sym),
}

/// A single annotation. Retention-bucket classification in legacy containers
/// folds into one ordered list per attach site at lift; container-specific
/// emission is a lowering concern (`FormatProfile`), not IR content.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Annotation {
    /// The annotation type.
    pub class: ClassId,
    /// `(element name, value)` pairs.
    pub elements: Vec<(Sym, AnnValue)>,
}

/// A class field.
#[derive(Clone, Debug)]
pub struct FieldData {
    /// Field name.
    pub name: Sym,
    /// Field type annotation.
    pub ty: Ty,
    /// Modifiers.
    pub modifiers: Modifiers,
    /// Initial value, if any (a constant from the module pool).
    pub initial_value: Option<ConstId>,
    /// Annotations (single folded list).
    pub annotations: Vec<Annotation>,
}

/// Class structure metadata.
#[derive(Clone, Debug)]
pub struct ClassData {
    /// Class descriptor (e.g. `Lfoo/Bar;`) — a name, not a file offset.
    pub descriptor: Sym,
    /// Simple display name.
    pub name: Sym,
    /// Modifiers.
    pub modifiers: Modifiers,
    /// Source language.
    pub source_lang: SourceLang,
    /// Superclass, as an index into the module's own class table.
    pub super_class: Option<ClassId>,
    /// Implemented interfaces, as module class-table indices.
    pub interfaces: Vec<ClassId>,
    /// Fields.
    pub fields: Vec<FieldData>,
    /// Methods, as indices into [`Module::functions`].
    pub methods: Vec<FuncId>,
    /// Annotations (single folded list).
    pub annotations: Vec<Annotation>,
    /// Source file name, when known.
    pub source_file: Option<Sym>,
    /// Per-record ES module declarations for `--merge-abc` bundles (`moduleRecordIdx`
    /// paired with this class's own `moduleRequestPhaseIdx` when present). `None`
    /// for non-module classes and standalone `_ESModuleRecord` files (which
    /// populate [`Module::imports`], [`Module::exports`], and
    /// [`Module::module_requests`]).
    pub es_module: Option<EsModule>,
    /// Per-record scope-names literal array for `--merge-abc` bundles
    /// (`scopeNames` field on this class, resolved into [`Module::consts`]).
    /// `None` when absent.
    pub scope_names: Option<ConstId>,
}

impl ClassData {
    /// Construct an empty `EcmaScript` class shell for `descriptor` / `name`.
    pub fn new(descriptor: Sym, name: Sym) -> Self {
        Self {
            descriptor,
            name,
            modifiers: Modifiers::NONE,
            source_lang: SourceLang::EcmaScript,
            super_class: None,
            interfaces: Vec::new(),
            fields: Vec::new(),
            methods: Vec::new(),
            annotations: Vec::new(),
            source_file: None,
            es_module: None,
            scope_names: None,
        }
    }
}

/// Per-record ES module metadata attached to a `--merge-abc` record class.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EsModule {
    /// Import declarations of this module record.
    pub imports: Vec<ImportDecl>,
    /// Export declarations of this module record.
    pub exports: Vec<ExportDecl>,
    /// Module requests with their lazy-import flags, in request order.
    pub module_requests: Vec<ModuleRequest>,
}

/// One entry of a module's module-request list (`design/decisions.md` N7):
/// the specifier plus its lazy-import flag from the `moduleRequestPhaseIdx`
/// blob. The list is in module-record request order; declarations reference
/// specifiers by content ([`ImportDecl`]/[`ExportDecl`] carry the `Sym`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleRequest {
    /// The module specifier (`"./foo"`, `"std.core"`, …).
    pub specifier: Sym,
    /// Whether the request is lazily imported (raw flag `> 0`).
    pub lazy: bool,
}

/// An import declaration — a semantic ES module record (with container
/// `module_request_idx` pool indices resolved to the specifier symbols they
/// denote; `design/decisions.md` N7).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImportDecl {
    /// `import { import_name as local_name } from module_request`.
    Regular {
        /// Binding name in this module.
        local_name: Sym,
        /// Name exported by the source module.
        import_name: Sym,
        /// Module specifier.
        module_request: Sym,
    },
    /// `import * as local_name from module_request`.
    Namespace {
        /// Binding name in this module.
        local_name: Sym,
        /// Module specifier.
        module_request: Sym,
    },
}

/// An export declaration — a semantic ES module record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExportDecl {
    /// `export { local_name as export_name }` (no module request).
    Local {
        /// Binding name in this module.
        local_name: Sym,
        /// Name seen by importers.
        export_name: Sym,
    },
    /// `export { import_name as export_name } from module_request`.
    Indirect {
        /// Name seen by importers.
        export_name: Sym,
        /// Name exported by the source module.
        import_name: Sym,
        /// Module specifier.
        module_request: Sym,
    },
    /// `export * from module_request`.
    Star {
        /// Module specifier.
        module_request: Sym,
    },
}

/// Top-level IR module: owns all identity tables, arenas, and metadata.
///
/// The arenas (`insts`/`blocks`/`values`) are module-global so that every
/// id is unique module-wide — the stable-identity contract (T1) that makes
/// a [`ValueId`] usable as a taint-analysis key across pass pipelines.
#[derive(Clone, Debug, Default)]
pub struct Module {
    /// Container execution and calling-convention dialect (`D6`, defaults to
    /// [`Dialect::DynamicEcma`]).
    pub dialect: Dialect,
    /// Names as identity (T9).
    pub sym: SymbolTable,
    /// Typed constants, incl. array/object literal shapes.
    pub consts: ConstPool,
    /// Class table. [`StaticTy::Reference`](crate::ty::StaticTy::Reference)
    /// and [`crate::function::FunctionData::class_id`] index this.
    pub classes: Vec<ClassData>,
    /// Function table (metadata + body graphs).
    pub functions: Vec<FunctionData>,
    /// Import declarations (module semantics, not record encodings).
    pub imports: Vec<ImportDecl>,
    /// Export declarations.
    pub exports: Vec<ExportDecl>,
    /// Module requests with their lazy-import flags (`moduleRequestPhaseIdx`
    /// blobs; `design/decisions.md` N7), in module-record request order.
    pub module_requests: Vec<ModuleRequest>,

    /// Instruction arena.
    pub insts: Vec<Inst>,
    /// Basic block arena.
    pub blocks: Vec<Block>,
    /// SSA value arena.
    pub values: Vec<Value>,
}

impl Module {
    /// An empty [`Dialect::DynamicEcma`] module.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// An empty module configured with an explicit container [`Dialect`].
    #[must_use]
    pub fn with_dialect(dialect: Dialect) -> Self {
        Self {
            dialect,
            ..Self::default()
        }
    }

    /// Look up a function; `None` for out-of-range ids.
    pub fn func(&self, id: FuncId) -> Option<&FunctionData> {
        self.functions.get(id.index())
    }

    /// Mutable function lookup; `None` for out-of-range ids.
    pub fn func_mut(&mut self, id: FuncId) -> Option<&mut FunctionData> {
        self.functions.get_mut(id.index())
    }

    /// Look up a block; `None` for out-of-range ids.
    pub fn block(&self, id: BlockId) -> Option<&Block> {
        self.blocks.get(id.index())
    }

    /// Mutable block lookup; `None` for out-of-range ids.
    pub fn block_mut(&mut self, id: BlockId) -> Option<&mut Block> {
        self.blocks.get_mut(id.index())
    }

    /// Look up an instruction; `None` for out-of-range ids.
    pub fn inst(&self, id: InstId) -> Option<&Inst> {
        self.insts.get(id.index())
    }

    /// Mutable instruction lookup; `None` for out-of-range ids.
    pub fn inst_mut(&mut self, id: InstId) -> Option<&mut Inst> {
        self.insts.get_mut(id.index())
    }

    /// Look up a value; `None` for out-of-range ids.
    pub fn value(&self, id: ValueId) -> Option<&Value> {
        self.values.get(id.index())
    }

    /// Look up a class; `None` for out-of-range ids.
    pub fn class(&self, id: ClassId) -> Option<&ClassData> {
        self.classes.get(id.index())
    }

    /// Execution and calling-convention [`Dialect`] of `func`, determined by
    /// [`Module::dialect`] (`D6`, decoupled from per-class authoring
    /// [`SourceLang`]).
    #[must_use]
    pub const fn func_dialect(&self, _func: &FunctionData) -> Dialect {
        self.dialect
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;

    #[test]
    fn module_dialect_is_decoupled_from_source_lang_and_annotations_hash() {
        assert_eq!(Dialect::default(), Dialect::DynamicEcma);
        let mut dyn_mod = Module::new();
        assert_eq!(dyn_mod.dialect, Dialect::DynamicEcma);
        let desc = dyn_mod.sym.intern("LDynArkTS;");
        let mut cls = ClassData::new(desc, desc);
        cls.source_lang = SourceLang::ArkTS; // Dynamic es2abc ArkTS 1.0/1.1 class!
        dyn_mod.classes.push(cls);
        let fd = FunctionData::new(ClassId::new(0), desc, FunctionKind::Function);
        assert_eq!(
            dyn_mod.func_dialect(&fd),
            Dialect::DynamicEcma,
            "dynamic container with SourceLang::ArkTS must keep DynamicEcma ABI"
        );

        let static_mod = Module::with_dialect(Dialect::StaticArkTS);
        assert_eq!(static_mod.dialect, Dialect::StaticArkTS);
        assert_eq!(static_mod.func_dialect(&fd), Dialect::StaticArkTS);

        let ann = Annotation {
            class: ClassId::new(0),
            elements: vec![(desc, AnnValue::Field(ClassId::new(0), FieldId::new(1)))],
        };
        let mut set = HashSet::new();
        assert!(set.insert(ann.clone()));
        assert!(!set.insert(ann));
    }
}
