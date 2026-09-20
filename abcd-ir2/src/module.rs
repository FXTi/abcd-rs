//! Module graph: the top-level container (design/ir-v0.2.md §3).
//!
//! A [`Module`] describes a *program*: classes, functions, value flow,
//! types, annotations, module records, debug info. It owns the shared
//! identity tables ([`SymbolTable`], [`ConstPool`]) and the global arenas
//! ([`Inst`], [`Block`], [`Value`]) that give ids module-wide uniqueness
//! (T1). It never describes a *file*: no `version`, no `file_type`, no
//! offsets, no register/acc numbering, no literal-array indices, no
//! four-bucket annotations, no `num_vregs`/`num_args`.

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

    /// Whether the set is empty.
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }
}

impl std::ops::BitOr for Modifiers {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        self.union(rhs)
    }
}

impl std::ops::BitOrAssign for Modifiers {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = self.union(rhs);
    }
}

/// The source language a class was authored in (semantic, not a format
/// tag).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SourceLang {
    /// ECMAScript (JavaScript).
    EcmaScript,
    /// TypeScript.
    TypeScript,
    /// ArkTS.
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
/// identities (design/ir-v0.2.md §7): constants, classes, fields, names.
#[derive(Clone, Debug, PartialEq)]
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

/// A single annotation. The four v0.1 retention buckets fold into one
/// list per attach site; folding for a specific container version is a
/// lowering concern (FormatProfile), not IR content.
#[derive(Clone, Debug, PartialEq)]
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
}

/// An import declaration — a semantic ES module record (the N7-era
/// module-data model, with the file's `module_request_idx` pool indices
/// resolved to the specifier symbols they denote).
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

    /// Instruction arena.
    pub insts: Vec<Inst>,
    /// Basic block arena.
    pub blocks: Vec<Block>,
    /// SSA value arena.
    pub values: Vec<Value>,
}

impl Module {
    /// An empty module.
    pub fn new() -> Self {
        Self::default()
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
}
