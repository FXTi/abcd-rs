//! Exhaustive zero-recursion ID visitors, fragment/module ID remapping, and
//! structural [`Module`] equivalence checking (`#84` Part 2a).
//!
//! Every struct destructuring and enum `match` in this module is written
//! **without** `..` or `_` wildcards so adding any field or variant anywhere in
//! `abcd-ir` forces an explicit update at compile time. All nested [`Ty::Union`]
//! walks execute iteratively over explicit heap workstacks (`O(1)` call stack).

use crate::consts::Const;
use crate::function::{
    Block, Catch, ColumnEntry, DebugData, Edge, FunctionData, Inst, LineEntry, LocalName,
    LocalScope, TryRegion, Value, ValueDef,
};
use crate::id::{BlockId, ClassId, ConstId, FieldId, FuncId, InstId, Sym, ValueId};
use crate::module::{
    AnnValue, Annotation, ClassData, EsModule, ExportDecl, FieldData, ImportDecl, Module,
    ModuleRequest, Signature,
};
use crate::op::Op;
use crate::ty::{StaticTy, Ty};

// ============================================================================
// Per-type exhaustive ID visitors (`Const`, `StaticTy`, `Ty`, `Signature`, ESM)
// ============================================================================

impl Const {
    /// Visit every [`Sym`] referenced directly by this constant.
    pub fn for_each_sym<F: FnMut(Sym)>(&self, mut f: F) {
        match self {
            Const::EtsImplements(s) | Const::String(s) | Const::BigInt(s) => f(*s),
            Const::Undefined
            | Const::Hole
            | Const::Null
            | Const::Bool(_)
            | Const::Int8(_)
            | Const::Int32(_)
            | Const::Float32(_)
            | Const::Number(_)
            | Const::Int64(_)
            | Const::UInt64(_)
            | Const::Accessor(_)
            | Const::MethodAffiliate(_)
            | Const::BuiltinTypeIndex(_)
            | Const::LitNull(_)
            | Const::ArrayLiteral(_)
            | Const::TypedArrayLiteral { .. }
            | Const::ObjectLiteral { .. }
            | Const::LiteralBufferRef(_)
            | Const::MethodRef { .. } => {}
        }
    }

    /// Visit each mutable [`Sym`] referenced directly by this constant in exact
    /// [`Const::for_each_sym`] order.
    pub fn for_each_sym_mut<'a, F: FnMut(&'a mut Sym)>(&'a mut self, mut f: F) {
        match self {
            Const::EtsImplements(s) | Const::String(s) | Const::BigInt(s) => f(s),
            Const::Undefined
            | Const::Hole
            | Const::Null
            | Const::Bool(_)
            | Const::Int8(_)
            | Const::Int32(_)
            | Const::Float32(_)
            | Const::Number(_)
            | Const::Int64(_)
            | Const::UInt64(_)
            | Const::Accessor(_)
            | Const::MethodAffiliate(_)
            | Const::BuiltinTypeIndex(_)
            | Const::LitNull(_)
            | Const::ArrayLiteral(_)
            | Const::TypedArrayLiteral { .. }
            | Const::ObjectLiteral { .. }
            | Const::LiteralBufferRef(_)
            | Const::MethodRef { .. } => {}
        }
    }

    /// Visit every child [`ConstId`] referenced directly by this constant.
    pub fn for_each_const_id<F: FnMut(ConstId)>(&self, mut f: F) {
        match self {
            Const::ArrayLiteral(items) | Const::TypedArrayLiteral { items, .. } => {
                for &cid in items {
                    f(cid);
                }
            }
            Const::ObjectLiteral { keys, values } => {
                for &cid in keys {
                    f(cid);
                }
                for &cid in values {
                    f(cid);
                }
            }
            Const::LiteralBufferRef(cid) => f(*cid),
            Const::Undefined
            | Const::Hole
            | Const::Null
            | Const::Bool(_)
            | Const::Int8(_)
            | Const::Int32(_)
            | Const::Float32(_)
            | Const::Number(_)
            | Const::Int64(_)
            | Const::UInt64(_)
            | Const::Accessor(_)
            | Const::MethodAffiliate(_)
            | Const::BuiltinTypeIndex(_)
            | Const::EtsImplements(_)
            | Const::LitNull(_)
            | Const::String(_)
            | Const::BigInt(_)
            | Const::MethodRef { .. } => {}
        }
    }

    /// Visit each mutable child [`ConstId`] referenced directly by this constant
    /// in exact [`Const::for_each_const_id`] order (`keys` then `values` for
    /// [`Const::ObjectLiteral`]).
    pub fn for_each_const_id_mut<'a, F: FnMut(&'a mut ConstId)>(&'a mut self, mut f: F) {
        match self {
            Const::ArrayLiteral(items) | Const::TypedArrayLiteral { items, .. } => {
                for cid in items {
                    f(cid);
                }
            }
            Const::ObjectLiteral { keys, values } => {
                for cid in keys {
                    f(cid);
                }
                for cid in values {
                    f(cid);
                }
            }
            Const::LiteralBufferRef(cid) => f(cid),
            Const::Undefined
            | Const::Hole
            | Const::Null
            | Const::Bool(_)
            | Const::Int8(_)
            | Const::Int32(_)
            | Const::Float32(_)
            | Const::Number(_)
            | Const::Int64(_)
            | Const::UInt64(_)
            | Const::Accessor(_)
            | Const::MethodAffiliate(_)
            | Const::BuiltinTypeIndex(_)
            | Const::EtsImplements(_)
            | Const::LitNull(_)
            | Const::String(_)
            | Const::BigInt(_)
            | Const::MethodRef { .. } => {}
        }
    }

    /// Visit every [`FuncId`] referenced directly by this constant.
    pub fn for_each_func_id<F: FnMut(FuncId)>(&self, mut f: F) {
        match self {
            Const::MethodRef { func, .. } => f(*func),
            Const::Undefined
            | Const::Hole
            | Const::Null
            | Const::Bool(_)
            | Const::Int8(_)
            | Const::Int32(_)
            | Const::Float32(_)
            | Const::Number(_)
            | Const::Int64(_)
            | Const::UInt64(_)
            | Const::Accessor(_)
            | Const::MethodAffiliate(_)
            | Const::BuiltinTypeIndex(_)
            | Const::EtsImplements(_)
            | Const::LitNull(_)
            | Const::String(_)
            | Const::BigInt(_)
            | Const::ArrayLiteral(_)
            | Const::TypedArrayLiteral { .. }
            | Const::ObjectLiteral { .. }
            | Const::LiteralBufferRef(_) => {}
        }
    }

    /// Visit each mutable [`FuncId`] referenced directly by this constant in
    /// exact [`Const::for_each_func_id`] order.
    pub fn for_each_func_id_mut<'a, F: FnMut(&'a mut FuncId)>(&'a mut self, mut f: F) {
        match self {
            Const::MethodRef { func, .. } => f(func),
            Const::Undefined
            | Const::Hole
            | Const::Null
            | Const::Bool(_)
            | Const::Int8(_)
            | Const::Int32(_)
            | Const::Float32(_)
            | Const::Number(_)
            | Const::Int64(_)
            | Const::UInt64(_)
            | Const::Accessor(_)
            | Const::MethodAffiliate(_)
            | Const::BuiltinTypeIndex(_)
            | Const::EtsImplements(_)
            | Const::LitNull(_)
            | Const::String(_)
            | Const::BigInt(_)
            | Const::ArrayLiteral(_)
            | Const::TypedArrayLiteral { .. }
            | Const::ObjectLiteral { .. }
            | Const::LiteralBufferRef(_) => {}
        }
    }
}

impl StaticTy {
    /// Visit every [`Sym`] referenced by this static type.
    #[inline]
    pub fn for_each_sym<F: FnMut(Sym)>(&self, mut _f: F) {
        match self {
            StaticTy::U1
            | StaticTy::I8
            | StaticTy::U8
            | StaticTy::I16
            | StaticTy::U16
            | StaticTy::I32
            | StaticTy::U32
            | StaticTy::I64
            | StaticTy::U64
            | StaticTy::F32
            | StaticTy::F64
            | StaticTy::Reference(_)
            | StaticTy::Void => {}
        }
    }

    /// Visit each mutable [`Sym`] referenced by this static type.
    #[inline]
    pub fn for_each_sym_mut<'a, F: FnMut(&'a mut Sym)>(&'a mut self, mut _f: F) {
        match self {
            StaticTy::U1
            | StaticTy::I8
            | StaticTy::U8
            | StaticTy::I16
            | StaticTy::U16
            | StaticTy::I32
            | StaticTy::U32
            | StaticTy::I64
            | StaticTy::U64
            | StaticTy::F32
            | StaticTy::F64
            | StaticTy::Reference(_)
            | StaticTy::Void => {}
        }
    }

    /// Visit every [`ClassId`] referenced by this static type.
    #[inline]
    pub fn for_each_class_id<F: FnMut(ClassId)>(&self, mut f: F) {
        match self {
            StaticTy::Reference(cid) => f(*cid),
            StaticTy::U1
            | StaticTy::I8
            | StaticTy::U8
            | StaticTy::I16
            | StaticTy::U16
            | StaticTy::I32
            | StaticTy::U32
            | StaticTy::I64
            | StaticTy::U64
            | StaticTy::F32
            | StaticTy::F64
            | StaticTy::Void => {}
        }
    }

    /// Visit each mutable [`ClassId`] referenced by this static type.
    #[inline]
    pub fn for_each_class_id_mut<'a, F: FnMut(&'a mut ClassId)>(&'a mut self, mut f: F) {
        match self {
            StaticTy::Reference(cid) => f(cid),
            StaticTy::U1
            | StaticTy::I8
            | StaticTy::U8
            | StaticTy::I16
            | StaticTy::U16
            | StaticTy::I32
            | StaticTy::U32
            | StaticTy::I64
            | StaticTy::U64
            | StaticTy::F32
            | StaticTy::F64
            | StaticTy::Void => {}
        }
    }
}

impl Ty {
    /// Visit every [`Sym`] inside this type iteratively on a heap workstack.
    pub fn for_each_sym<F: FnMut(Sym)>(&self, mut f: F) {
        match self {
            Ty::Any | Ty::Never | Ty::DynPrim(_) | Ty::Unknown => {}
            Ty::Static(s) => s.for_each_sym(&mut f),
            Ty::Union(xs) => {
                let mut stack: Vec<std::slice::Iter<'_, Ty>> = vec![xs.iter()];
                while let Some(iter) = stack.last_mut() {
                    let Some(item) = iter.next() else {
                        stack.pop();
                        continue;
                    };
                    match item {
                        Ty::Any | Ty::Never | Ty::DynPrim(_) | Ty::Unknown => {}
                        Ty::Static(s) => s.for_each_sym(&mut f),
                        Ty::Union(sub) => {
                            if !sub.is_empty() {
                                stack.push(sub.iter());
                            }
                        }
                    }
                }
            }
        }
    }

    /// Visit each mutable [`Sym`] inside this type iteratively on a heap workstack.
    pub fn for_each_sym_mut<'a, F: FnMut(&'a mut Sym)>(&'a mut self, mut f: F) {
        match self {
            Ty::Any | Ty::Never | Ty::DynPrim(_) | Ty::Unknown => {}
            Ty::Static(s) => s.for_each_sym_mut(&mut f),
            Ty::Union(xs) => {
                let mut stack: Vec<std::slice::IterMut<'a, Ty>> = vec![xs.iter_mut()];
                while let Some(iter) = stack.last_mut() {
                    let Some(item) = iter.next() else {
                        stack.pop();
                        continue;
                    };
                    match item {
                        Ty::Any | Ty::Never | Ty::DynPrim(_) | Ty::Unknown => {}
                        Ty::Static(s) => s.for_each_sym_mut(&mut f),
                        Ty::Union(sub) => {
                            if !sub.is_empty() {
                                stack.push(sub.iter_mut());
                            }
                        }
                    }
                }
            }
        }
    }

    /// Visit every [`ClassId`] inside this type iteratively in left-to-right
    /// pre-order on a heap workstack.
    pub fn for_each_class_id<F: FnMut(ClassId)>(&self, mut f: F) {
        match self {
            Ty::Any | Ty::Never | Ty::DynPrim(_) | Ty::Unknown => {}
            Ty::Static(s) => s.for_each_class_id(&mut f),
            Ty::Union(xs) => {
                let mut stack: Vec<std::slice::Iter<'_, Ty>> = vec![xs.iter()];
                while let Some(iter) = stack.last_mut() {
                    let Some(item) = iter.next() else {
                        stack.pop();
                        continue;
                    };
                    match item {
                        Ty::Any | Ty::Never | Ty::DynPrim(_) | Ty::Unknown => {}
                        Ty::Static(s) => s.for_each_class_id(&mut f),
                        Ty::Union(sub) => {
                            if !sub.is_empty() {
                                stack.push(sub.iter());
                            }
                        }
                    }
                }
            }
        }
    }

    /// Visit each mutable [`ClassId`] inside this type iteratively in
    /// left-to-right pre-order on a heap workstack.
    pub fn for_each_class_id_mut<'a, F: FnMut(&'a mut ClassId)>(&'a mut self, mut f: F) {
        match self {
            Ty::Any | Ty::Never | Ty::DynPrim(_) | Ty::Unknown => {}
            Ty::Static(s) => s.for_each_class_id_mut(&mut f),
            Ty::Union(xs) => {
                let mut stack: Vec<std::slice::IterMut<'a, Ty>> = vec![xs.iter_mut()];
                while let Some(iter) = stack.last_mut() {
                    let Some(item) = iter.next() else {
                        stack.pop();
                        continue;
                    };
                    match item {
                        Ty::Any | Ty::Never | Ty::DynPrim(_) | Ty::Unknown => {}
                        Ty::Static(s) => s.for_each_class_id_mut(&mut f),
                        Ty::Union(sub) => {
                            if !sub.is_empty() {
                                stack.push(sub.iter_mut());
                            }
                        }
                    }
                }
            }
        }
    }
}

impl Signature {
    /// Visit every [`Sym`] referenced in `return_ty` and `param_tys`.
    pub fn for_each_sym<F: FnMut(Sym)>(&self, mut f: F) {
        let Signature {
            return_ty,
            param_tys,
        } = self;
        if let Some(ret) = return_ty {
            ret.for_each_sym(&mut f);
        }
        for pty in param_tys {
            pty.for_each_sym(&mut f);
        }
    }

    /// Visit each mutable [`Sym`] referenced in `return_ty` and `param_tys`.
    pub fn for_each_sym_mut<'a, F: FnMut(&'a mut Sym)>(&'a mut self, mut f: F) {
        let Signature {
            return_ty,
            param_tys,
        } = self;
        if let Some(ret) = return_ty {
            ret.for_each_sym_mut(&mut f);
        }
        for pty in param_tys {
            pty.for_each_sym_mut(&mut f);
        }
    }

    /// Visit every [`ClassId`] referenced in `return_ty` and `param_tys`.
    pub fn for_each_class_id<F: FnMut(ClassId)>(&self, mut f: F) {
        let Signature {
            return_ty,
            param_tys,
        } = self;
        if let Some(ret) = return_ty {
            ret.for_each_class_id(&mut f);
        }
        for pty in param_tys {
            pty.for_each_class_id(&mut f);
        }
    }

    /// Visit each mutable [`ClassId`] referenced in `return_ty` and `param_tys`.
    pub fn for_each_class_id_mut<'a, F: FnMut(&'a mut ClassId)>(&'a mut self, mut f: F) {
        let Signature {
            return_ty,
            param_tys,
        } = self;
        if let Some(ret) = return_ty {
            ret.for_each_class_id_mut(&mut f);
        }
        for pty in param_tys {
            pty.for_each_class_id_mut(&mut f);
        }
    }
}

impl ImportDecl {
    /// Visit every [`Sym`] in this import declaration.
    pub fn for_each_sym<F: FnMut(Sym)>(&self, mut f: F) {
        match self {
            ImportDecl::Regular {
                local_name,
                import_name,
                module_request,
            } => {
                f(*local_name);
                f(*import_name);
                f(*module_request);
            }
            ImportDecl::Namespace {
                local_name,
                module_request,
            } => {
                f(*local_name);
                f(*module_request);
            }
        }
    }

    /// Visit each mutable [`Sym`] in this import declaration.
    pub fn for_each_sym_mut<'a, F: FnMut(&'a mut Sym)>(&'a mut self, mut f: F) {
        match self {
            ImportDecl::Regular {
                local_name,
                import_name,
                module_request,
            } => {
                f(local_name);
                f(import_name);
                f(module_request);
            }
            ImportDecl::Namespace {
                local_name,
                module_request,
            } => {
                f(local_name);
                f(module_request);
            }
        }
    }
}

impl ExportDecl {
    /// Visit every [`Sym`] in this export declaration.
    pub fn for_each_sym<F: FnMut(Sym)>(&self, mut f: F) {
        match self {
            ExportDecl::Local {
                local_name,
                export_name,
            } => {
                f(*local_name);
                f(*export_name);
            }
            ExportDecl::Indirect {
                export_name,
                import_name,
                module_request,
            } => {
                f(*export_name);
                f(*import_name);
                f(*module_request);
            }
            ExportDecl::Star { module_request } => f(*module_request),
        }
    }

    /// Visit each mutable [`Sym`] in this export declaration.
    pub fn for_each_sym_mut<'a, F: FnMut(&'a mut Sym)>(&'a mut self, mut f: F) {
        match self {
            ExportDecl::Local {
                local_name,
                export_name,
            } => {
                f(local_name);
                f(export_name);
            }
            ExportDecl::Indirect {
                export_name,
                import_name,
                module_request,
            } => {
                f(export_name);
                f(import_name);
                f(module_request);
            }
            ExportDecl::Star { module_request } => f(module_request),
        }
    }
}

impl ModuleRequest {
    /// Visit the specifier [`Sym`] of this module request.
    #[inline]
    pub fn for_each_sym<F: FnMut(Sym)>(&self, mut f: F) {
        let ModuleRequest { specifier, lazy: _ } = self;
        f(*specifier);
    }

    /// Visit the mutable specifier [`Sym`] of this module request.
    #[inline]
    pub fn for_each_sym_mut<'a, F: FnMut(&'a mut Sym)>(&'a mut self, mut f: F) {
        let ModuleRequest { specifier, lazy: _ } = self;
        f(specifier);
    }
}

impl EsModule {
    /// Visit every [`Sym`] across `imports`, `exports`, and `module_requests`.
    pub fn for_each_sym<F: FnMut(Sym)>(&self, mut f: F) {
        let EsModule {
            imports,
            exports,
            module_requests,
        } = self;
        for imp in imports {
            imp.for_each_sym(&mut f);
        }
        for exp in exports {
            exp.for_each_sym(&mut f);
        }
        for req in module_requests {
            req.for_each_sym(&mut f);
        }
    }

    /// Visit each mutable [`Sym`] across `imports`, `exports`, and `module_requests`.
    pub fn for_each_sym_mut<'a, F: FnMut(&'a mut Sym)>(&'a mut self, mut f: F) {
        let EsModule {
            imports,
            exports,
            module_requests,
        } = self;
        for imp in imports {
            imp.for_each_sym_mut(&mut f);
        }
        for exp in exports {
            exp.for_each_sym_mut(&mut f);
        }
        for req in module_requests {
            req.for_each_sym_mut(&mut f);
        }
    }
}

// ============================================================================
// Unified `IdRemapper` trait + ready-to-use `FragmentRemapper`
// ============================================================================

/// Policy trait for remapping arena and table IDs across IR fragments or modules.
///
/// Every method defaults to the identity mapping so callers (such as parallel
/// per-function lifting in `abcd-lift` or function cloning in `abcd-opt`) only
/// override the ID spaces that actually move.
pub trait IdRemapper {
    /// Remap a [`Sym`].
    #[inline]
    fn remap_sym(&mut self, id: Sym) -> Sym {
        id
    }

    /// Remap a [`ConstId`].
    #[inline]
    fn remap_const(&mut self, id: ConstId) -> ConstId {
        id
    }

    /// Remap a [`ClassId`].
    #[inline]
    fn remap_class(&mut self, id: ClassId) -> ClassId {
        id
    }

    /// Remap a [`FieldId`] belonging to `pre_remap_class` (the owning class ID
    /// before [`Self::remap_class`] is applied).
    #[inline]
    fn remap_field(&mut self, _pre_remap_class: ClassId, id: FieldId) -> FieldId {
        id
    }

    /// Remap a [`FuncId`].
    #[inline]
    fn remap_func(&mut self, id: FuncId) -> FuncId {
        id
    }

    /// Remap a [`BlockId`].
    #[inline]
    fn remap_block(&mut self, id: BlockId) -> BlockId {
        id
    }

    /// Remap an [`InstId`].
    #[inline]
    fn remap_inst(&mut self, id: InstId) -> InstId {
        id
    }

    /// Remap a [`ValueId`].
    #[inline]
    fn remap_value(&mut self, id: ValueId) -> ValueId {
        id
    }
}

/// Zero-allocation slice + arena-offset [`IdRemapper`] for merging a locally
/// lifted or cloned function fragment into a module's global arenas (`#84`).
///
/// Optional remap slices leave out-of-bounds or `None` tables unchanged;
/// `block_offset`, `inst_offset`, and `value_offset` are added to local arena
/// indices via `wrapping_add` (callers validate total arena sizes beforehand).
#[derive(Clone, Copy, Debug, Default)]
pub struct FragmentRemapper<'a> {
    /// Optional local-to-global [`Sym`] table (`sym_map[local.index()]`).
    pub sym_map: Option<&'a [Sym]>,
    /// Optional local-to-global [`ConstId`] table (`const_map[local.index()]`).
    pub const_map: Option<&'a [ConstId]>,
    /// Optional local-to-global [`ClassId`] table.
    pub class_map: Option<&'a [ClassId]>,
    /// Optional local-to-global [`FuncId`] table.
    pub func_map: Option<&'a [FuncId]>,
    /// Base offset added to every [`BlockId`].
    pub block_offset: u32,
    /// Base offset added to every [`InstId`].
    pub inst_offset: u32,
    /// Base offset added to every [`ValueId`].
    pub value_offset: u32,
}

impl IdRemapper for FragmentRemapper<'_> {
    #[inline]
    fn remap_sym(&mut self, id: Sym) -> Sym {
        self.sym_map
            .and_then(|m| m.get(id.index()).copied())
            .unwrap_or(id)
    }

    #[inline]
    fn remap_const(&mut self, id: ConstId) -> ConstId {
        self.const_map
            .and_then(|m| m.get(id.index()).copied())
            .unwrap_or(id)
    }

    #[inline]
    fn remap_class(&mut self, id: ClassId) -> ClassId {
        self.class_map
            .and_then(|m| m.get(id.index()).copied())
            .unwrap_or(id)
    }

    #[inline]
    fn remap_func(&mut self, id: FuncId) -> FuncId {
        self.func_map
            .and_then(|m| m.get(id.index()).copied())
            .unwrap_or(id)
    }

    #[inline]
    fn remap_block(&mut self, id: BlockId) -> BlockId {
        BlockId::new(id.raw().wrapping_add(self.block_offset))
    }

    #[inline]
    fn remap_inst(&mut self, id: InstId) -> InstId {
        InstId::new(id.raw().wrapping_add(self.inst_offset))
    }

    #[inline]
    fn remap_value(&mut self, id: ValueId) -> ValueId {
        ValueId::new(id.raw().wrapping_add(self.value_offset))
    }
}

impl Const {
    /// Remap all [`Sym`], [`ConstId`], and [`FuncId`] references inside this [`Const`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        self.for_each_sym_mut(|s| *s = remapper.remap_sym(*s));
        self.for_each_const_id_mut(|c| *c = remapper.remap_const(*c));
        self.for_each_func_id_mut(|f| *f = remapper.remap_func(*f));
    }
}

impl StaticTy {
    /// Remap all [`Sym`] and [`ClassId`] references inside this [`StaticTy`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        self.for_each_sym_mut(|s| *s = remapper.remap_sym(*s));
        self.for_each_class_id_mut(|c| *c = remapper.remap_class(*c));
    }
}

impl Ty {
    /// Remap all [`Sym`] and [`ClassId`] references inside this [`Ty`] iteratively.
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        self.for_each_sym_mut(|s| *s = remapper.remap_sym(*s));
        self.for_each_class_id_mut(|c| *c = remapper.remap_class(*c));
    }
}

impl Signature {
    /// Remap all [`Sym`] and [`ClassId`] references inside this [`Signature`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        self.for_each_sym_mut(|s| *s = remapper.remap_sym(*s));
        self.for_each_class_id_mut(|c| *c = remapper.remap_class(*c));
    }
}

impl Op {
    /// Remap all SSA operands, [`BlockId`], [`ConstId`], [`FuncId`], [`ClassId`],
    /// and [`Sym`] payloads directly carried by this [`Op`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        self.for_each_operand_mut(|v| *v = remapper.remap_value(*v));
        self.for_each_block_id_mut(|b| *b = remapper.remap_block(*b));
        self.for_each_const_id_mut(|c| *c = remapper.remap_const(*c));
        self.for_each_func_id_mut(|f| *f = remapper.remap_func(*f));
        self.for_each_class_id_mut(|c| *c = remapper.remap_class(*c));
        self.for_each_sym_mut(|s| *s = remapper.remap_sym(*s));
    }
}

impl ValueDef {
    /// Remap the defining [`InstId`], [`ConstId`], or [`BlockId`] of this [`ValueDef`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        match self {
            ValueDef::Param(_) => {}
            ValueDef::Inst(iid) => *iid = remapper.remap_inst(*iid),
            ValueDef::Const(cid) => *cid = remapper.remap_const(*cid),
            ValueDef::ExceptionParam(bid) => *bid = remapper.remap_block(*bid),
        }
    }
}

impl Value {
    /// Remap both `def` and `ty` of this [`Value`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let Value { def, ty } = self;
        def.remap_ids(remapper);
        ty.remap_ids(remapper);
    }
}

impl Inst {
    /// Remap `op`, `result`, and owning `block` of this [`Inst`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let Inst {
            op,
            result,
            block,
            loc: _,
        } = self;
        op.remap_ids(remapper);
        if let Some(res) = result {
            *res = remapper.remap_value(*res);
        }
        *block = remapper.remap_block(*block);
    }
}

impl Edge {
    /// Remap the predecessor [`BlockId`] of this CFG [`Edge`].
    #[inline]
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let Edge { from, kind: _ } = self;
        *from = remapper.remap_block(*from);
    }
}

impl Block {
    /// Remap all [`InstId`]s and incoming predecessor [`Edge`]s in this [`Block`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let Block { insts, preds } = self;
        for iid in insts {
            *iid = remapper.remap_inst(*iid);
        }
        for edge in preds {
            edge.remap_ids(remapper);
        }
    }
}

impl Catch {
    /// Remap `handler`, `exception`, and `type_class` of this [`Catch`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let Catch {
            handler,
            exception,
            type_class,
        } = self;
        *handler = remapper.remap_block(*handler);
        *exception = remapper.remap_value(*exception);
        if let Some(tc) = type_class {
            *tc = remapper.remap_class(*tc);
        }
    }
}

impl TryRegion {
    /// Remap all protected [`BlockId`]s and [`Catch`] entries of this [`TryRegion`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let TryRegion { protected, catches } = self;
        for bid in protected {
            *bid = remapper.remap_block(*bid);
        }
        for catch in catches {
            catch.remap_ids(remapper);
        }
    }
}

impl LineEntry {
    /// Remap the [`InstId`] of this [`LineEntry`].
    #[inline]
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let LineEntry { inst, line: _ } = self;
        *inst = remapper.remap_inst(*inst);
    }
}

impl ColumnEntry {
    /// Remap the [`InstId`] of this [`ColumnEntry`].
    #[inline]
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let ColumnEntry { inst, column: _ } = self;
        *inst = remapper.remap_inst(*inst);
    }
}

impl LocalScope {
    /// Remap `start` and `end` [`InstId`]s of this [`LocalScope`].
    #[inline]
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let LocalScope { start, end } = self;
        *start = remapper.remap_inst(*start);
        *end = remapper.remap_inst(*end);
    }
}

impl LocalName {
    /// Remap `name`, `ty`, and `scope` of this [`LocalName`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let LocalName { name, ty, scope } = self;
        *name = remapper.remap_sym(*name);
        if let Some(t) = ty {
            t.remap_ids(remapper);
        }
        if let Some(sc) = scope {
            sc.remap_ids(remapper);
        }
    }
}

impl DebugData {
    /// Remap all [`Sym`], [`InstId`], [`ClassId`], and [`ConstId`] references in [`DebugData`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let DebugData {
            source_file,
            source_code: _,
            line_table,
            column_table,
            local_names,
            param_names,
            scope_names,
        } = self;
        if let Some(sf) = source_file {
            *sf = remapper.remap_sym(*sf);
        }
        for le in line_table {
            le.remap_ids(remapper);
        }
        for ce in column_table {
            ce.remap_ids(remapper);
        }
        for ln in local_names {
            ln.remap_ids(remapper);
        }
        for pn in param_names {
            *pn = remapper.remap_sym(*pn);
        }
        if let Some(sn) = scope_names {
            *sn = remapper.remap_const(*sn);
        }
    }
}

impl AnnValue {
    /// Remap [`ConstId`], [`ClassId`], [`FieldId`], and [`Sym`] payloads of this [`AnnValue`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        match self {
            AnnValue::Const(cid) => *cid = remapper.remap_const(*cid),
            AnnValue::Class(cid) => *cid = remapper.remap_class(*cid),
            AnnValue::Field(cid, fid) => {
                let pre_cls = *cid;
                *cid = remapper.remap_class(pre_cls);
                *fid = remapper.remap_field(pre_cls, *fid);
            }
            AnnValue::Name(sym) => *sym = remapper.remap_sym(*sym),
        }
    }
}

impl Annotation {
    /// Remap annotation `class` and all `(element_name, value)` pairs.
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let Annotation { class, elements } = self;
        *class = remapper.remap_class(*class);
        for (name, val) in elements {
            *name = remapper.remap_sym(*name);
            val.remap_ids(remapper);
        }
    }
}

impl FieldData {
    /// Remap `name`, `ty`, `initial_value`, and `annotations` of this [`FieldData`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let FieldData {
            name,
            ty,
            modifiers: _,
            initial_value,
            annotations,
        } = self;
        *name = remapper.remap_sym(*name);
        ty.remap_ids(remapper);
        if let Some(iv) = initial_value {
            *iv = remapper.remap_const(*iv);
        }
        for ann in annotations {
            ann.remap_ids(remapper);
        }
    }
}

impl ImportDecl {
    /// Remap all [`Sym`] bindings and module specifiers in this [`ImportDecl`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        self.for_each_sym_mut(|s| *s = remapper.remap_sym(*s));
    }
}

impl ExportDecl {
    /// Remap all [`Sym`] bindings and module specifiers in this [`ExportDecl`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        self.for_each_sym_mut(|s| *s = remapper.remap_sym(*s));
    }
}

impl ModuleRequest {
    /// Remap the specifier [`Sym`] in this [`ModuleRequest`].
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        self.for_each_sym_mut(|s| *s = remapper.remap_sym(*s));
    }
}

impl EsModule {
    /// Remap all [`Sym`]s in `imports`, `exports`, and `module_requests`.
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        self.for_each_sym_mut(|s| *s = remapper.remap_sym(*s));
    }
}

impl ClassData {
    /// Remap every ID reference inside this [`ClassData`] (`descriptor`, `name`,
    /// `super_class`, `interfaces`, `fields`, `methods`, `annotations`,
    /// `source_file`, `es_module`, and `scope_names`).
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let ClassData {
            descriptor,
            name,
            modifiers: _,
            source_lang: _,
            super_class,
            interfaces,
            fields,
            methods,
            annotations,
            source_file,
            es_module,
            scope_names,
        } = self;
        *descriptor = remapper.remap_sym(*descriptor);
        *name = remapper.remap_sym(*name);
        if let Some(sc) = super_class {
            *sc = remapper.remap_class(*sc);
        }
        for iface in interfaces {
            *iface = remapper.remap_class(*iface);
        }
        for field in fields {
            field.remap_ids(remapper);
        }
        for method in methods {
            *method = remapper.remap_func(*method);
        }
        for ann in annotations {
            ann.remap_ids(remapper);
        }
        if let Some(sf) = source_file {
            *sf = remapper.remap_sym(*sf);
        }
        if let Some(esm) = es_module {
            esm.remap_ids(remapper);
        }
        if let Some(sn) = scope_names {
            *sn = remapper.remap_const(*sn);
        }
    }
}

impl FunctionData {
    /// Remap every ID reference inside this [`FunctionData`] (`class_id`, `name`,
    /// `sig`, `params`, `frame_init_consts`, `blocks`, `try_regions`, `debug`,
    /// and `annotations`).
    pub fn remap_ids<R: IdRemapper>(&mut self, remapper: &mut R) {
        let FunctionData {
            class_id,
            name,
            sig,
            kind: _,
            modifiers: _,
            is_external: _,
            params,
            frame_init_consts,
            blocks,
            try_regions,
            debug,
            annotations,
        } = self;
        *class_id = remapper.remap_class(*class_id);
        *name = remapper.remap_sym(*name);
        if let Some(s) = sig {
            s.remap_ids(remapper);
        }
        for p in params {
            *p = remapper.remap_value(*p);
        }
        for fic in frame_init_consts {
            *fic = remapper.remap_value(*fic);
        }
        for bb in blocks {
            *bb = remapper.remap_block(*bb);
        }
        for region in try_regions {
            region.remap_ids(remapper);
        }
        if let Some(dbg) = debug {
            dbg.remap_ids(remapper);
        }
        for ann in annotations {
            ann.remap_ids(remapper);
        }
    }
}

/// Remap every non-table arena/entity record in `module` (`classes`, `functions`,
/// `imports`, `exports`, `module_requests`, `insts`, `blocks`, and `values`).
///
/// `module.sym` and `module.consts` are append-only identity pools and are left
/// untouched (callers rebuild or merge pools separately before remapping body
/// references).
pub fn remap_module_body<R: IdRemapper>(module: &mut Module, remapper: &mut R) {
    let Module {
        dialect: _,
        sym: _,
        consts: _,
        classes,
        functions,
        imports,
        exports,
        module_requests,
        insts,
        blocks,
        values,
    } = module;
    for cls in classes {
        cls.remap_ids(remapper);
    }
    for func in functions {
        func.remap_ids(remapper);
    }
    for imp in imports {
        imp.remap_ids(remapper);
    }
    for exp in exports {
        exp.remap_ids(remapper);
    }
    for req in module_requests {
        req.remap_ids(remapper);
    }
    for inst in insts {
        inst.remap_ids(remapper);
    }
    for blk in blocks {
        blk.remap_ids(remapper);
    }
    for val in values {
        val.remap_ids(remapper);
    }
}

// ============================================================================
// Exhaustive structural `Module` equivalence (`#84` Part 2a)
// ============================================================================

fn check_eq<T: PartialEq + std::fmt::Debug>(path: &str, a: &T, b: &T) -> Result<(), String> {
    if a == b {
        Ok(())
    } else {
        Err(format!("{path} mismatch: {a:?} != {b:?}"))
    }
}

fn check_slice_eq<T: PartialEq + std::fmt::Debug>(
    label: &str,
    a: &[T],
    b: &[T],
) -> Result<(), String> {
    if a.len() != b.len() {
        return Err(format!(
            "{label}.len() mismatch: {} != {}",
            a.len(),
            b.len()
        ));
    }
    for (i, (x, y)) in a.iter().zip(b.iter()).enumerate() {
        if x != y {
            return Err(format!("{label}[{i}] mismatch: {x:?} != {y:?}"));
        }
    }
    Ok(())
}

fn check_es_module_eq(prefix: &str, a: &EsModule, b: &EsModule) -> Result<(), String> {
    let EsModule {
        imports: a_imports,
        exports: a_exports,
        module_requests: a_reqs,
    } = a;
    let EsModule {
        imports: b_imports,
        exports: b_exports,
        module_requests: b_reqs,
    } = b;
    check_slice_eq(&format!("{prefix}.imports"), a_imports, b_imports)?;
    check_slice_eq(&format!("{prefix}.exports"), a_exports, b_exports)?;
    check_slice_eq(&format!("{prefix}.module_requests"), a_reqs, b_reqs)?;
    Ok(())
}

/// Compare two [`Module`]s for 100% structural and bit-exact IR equivalence,
/// returning `Ok(())` when identical or a precise human-readable diagnostic of
/// the first mismatch (`#84`).
///
/// Transient hash-index residency ([`crate::SymbolTable::has_index`] and
/// [`crate::ConstPool::has_index`]) is intentionally ignored; every observable
/// symbol, constant, class, function, standalone/bundled ES module record,
/// block, instruction, and SSA value is checked in ID order.
pub fn modules_structurally_eq(a: &Module, b: &Module) -> Result<(), String> {
    let Module {
        dialect: a_dialect,
        sym: a_sym,
        consts: a_consts,
        classes: a_classes,
        functions: a_functions,
        imports: a_imports,
        exports: a_exports,
        module_requests: a_module_requests,
        insts: a_insts,
        blocks: a_blocks,
        values: a_values,
    } = a;
    let Module {
        dialect: b_dialect,
        sym: b_sym,
        consts: b_consts,
        classes: b_classes,
        functions: b_functions,
        imports: b_imports,
        exports: b_exports,
        module_requests: b_module_requests,
        insts: b_insts,
        blocks: b_blocks,
        values: b_values,
    } = b;

    check_eq("dialect", a_dialect, b_dialect)?;

    // 1. SymbolTable (`len`, `lossy_count`, per-ID `as_str`, `raw_mutf8`, `resolve`).
    check_eq("sym.len()", &a_sym.len(), &b_sym.len())?;
    check_eq(
        "sym.lossy_count()",
        &a_sym.lossy_count(),
        &b_sym.lossy_count(),
    )?;
    for i in 0..a_sym.len() {
        let sid = Sym::new(i as u32);
        if a_sym.as_str(sid) != b_sym.as_str(sid) {
            return Err(format!(
                "sym[{i}].as_str mismatch: {:?} != {:?}",
                a_sym.as_str(sid),
                b_sym.as_str(sid)
            ));
        }
        if a_sym.raw_mutf8(sid) != b_sym.raw_mutf8(sid) {
            return Err(format!(
                "sym[{i}].raw_mutf8 mismatch: {:?} != {:?}",
                a_sym.raw_mutf8(sid),
                b_sym.raw_mutf8(sid)
            ));
        }
        if a_sym.resolve(sid) != b_sym.resolve(sid) {
            return Err(format!(
                "sym[{i}].resolve mismatch: {:?} != {:?}",
                a_sym.resolve(sid),
                b_sym.resolve(sid)
            ));
        }
    }

    // 2. ConstPool (`len` + per-ID `Const`, including IEEE-754 bit patterns).
    check_eq("consts.len()", &a_consts.len(), &b_consts.len())?;
    for i in 0..a_consts.len() {
        let cid = ConstId::new(i as u32);
        let ca = a_consts.get(cid);
        let cb = b_consts.get(cid);
        if ca != cb {
            return Err(format!("consts[{i}] mismatch: {ca:?} != {cb:?}"));
        }
    }

    // 3. Classes (`ClassData` + `FieldData` + `EsModule`).
    check_eq("classes.len()", &a_classes.len(), &b_classes.len())?;
    for (ci, (ca, cb)) in a_classes.iter().zip(b_classes.iter()).enumerate() {
        let ClassData {
            descriptor: a_desc,
            name: a_name,
            modifiers: a_mods,
            source_lang: a_lang,
            super_class: a_super,
            interfaces: a_ifaces,
            fields: a_fields,
            methods: a_methods,
            annotations: a_anns,
            source_file: a_sf,
            es_module: a_esm,
            scope_names: a_sn,
        } = ca;
        let ClassData {
            descriptor: b_desc,
            name: b_name,
            modifiers: b_mods,
            source_lang: b_lang,
            super_class: b_super,
            interfaces: b_ifaces,
            fields: b_fields,
            methods: b_methods,
            annotations: b_anns,
            source_file: b_sf,
            es_module: b_esm,
            scope_names: b_sn,
        } = cb;
        let p = format!("classes[{ci}]");
        check_eq(&format!("{p}.descriptor"), a_desc, b_desc)?;
        check_eq(&format!("{p}.name"), a_name, b_name)?;
        check_eq(&format!("{p}.modifiers"), a_mods, b_mods)?;
        check_eq(&format!("{p}.source_lang"), a_lang, b_lang)?;
        check_eq(&format!("{p}.super_class"), a_super, b_super)?;
        check_slice_eq(&format!("{p}.interfaces"), a_ifaces, b_ifaces)?;
        check_eq(
            &format!("{p}.fields.len()"),
            &a_fields.len(),
            &b_fields.len(),
        )?;
        for (fi, (fa, fb)) in a_fields.iter().zip(b_fields.iter()).enumerate() {
            let FieldData {
                name: fa_name,
                ty: fa_ty,
                modifiers: fa_mods,
                initial_value: fa_iv,
                annotations: fa_anns,
            } = fa;
            let FieldData {
                name: fb_name,
                ty: fb_ty,
                modifiers: fb_mods,
                initial_value: fb_iv,
                annotations: fb_anns,
            } = fb;
            let fp = format!("{p}.fields[{fi}]");
            check_eq(&format!("{fp}.name"), fa_name, fb_name)?;
            check_eq(&format!("{fp}.ty"), fa_ty, fb_ty)?;
            check_eq(&format!("{fp}.modifiers"), fa_mods, fb_mods)?;
            check_eq(&format!("{fp}.initial_value"), fa_iv, fb_iv)?;
            check_slice_eq(&format!("{fp}.annotations"), fa_anns, fb_anns)?;
        }
        check_slice_eq(&format!("{p}.methods"), a_methods, b_methods)?;
        check_slice_eq(&format!("{p}.annotations"), a_anns, b_anns)?;
        check_eq(&format!("{p}.source_file"), a_sf, b_sf)?;
        match (a_esm, b_esm) {
            (None, None) => {}
            (Some(ea), Some(eb)) => check_es_module_eq(&format!("{p}.es_module"), ea, eb)?,
            _ => return Err(format!("{p}.es_module mismatch: {a_esm:?} != {b_esm:?}")),
        }
        check_eq(&format!("{p}.scope_names"), a_sn, b_sn)?;
    }

    // 4. Standalone module records (`imports`, `exports`, `module_requests`).
    check_slice_eq("imports", a_imports, b_imports)?;
    check_slice_eq("exports", a_exports, b_exports)?;
    check_slice_eq("module_requests", a_module_requests, b_module_requests)?;

    // 5. Functions (`FunctionData`, `Signature`, `TryRegion`, `DebugData`).
    check_eq("functions.len()", &a_functions.len(), &b_functions.len())?;
    for (fi, (fa, fb)) in a_functions.iter().zip(b_functions.iter()).enumerate() {
        let FunctionData {
            class_id: a_cid,
            name: a_name,
            sig: a_sig,
            kind: a_kind,
            modifiers: a_mods,
            is_external: a_ext,
            params: a_params,
            frame_init_consts: a_fic,
            blocks: a_fblocks,
            try_regions: a_tr,
            debug: a_dbg,
            annotations: a_anns,
        } = fa;
        let FunctionData {
            class_id: b_cid,
            name: b_name,
            sig: b_sig,
            kind: b_kind,
            modifiers: b_mods,
            is_external: b_ext,
            params: b_params,
            frame_init_consts: b_fic,
            blocks: b_fblocks,
            try_regions: b_tr,
            debug: b_dbg,
            annotations: b_anns,
        } = fb;
        let p = format!("functions[{fi}]");
        check_eq(&format!("{p}.class_id"), a_cid, b_cid)?;
        check_eq(&format!("{p}.name"), a_name, b_name)?;
        check_eq(&format!("{p}.sig"), a_sig, b_sig)?;
        check_eq(&format!("{p}.kind"), a_kind, b_kind)?;
        check_eq(&format!("{p}.modifiers"), a_mods, b_mods)?;
        check_eq(&format!("{p}.is_external"), a_ext, b_ext)?;
        check_slice_eq(&format!("{p}.params"), a_params, b_params)?;
        check_slice_eq(&format!("{p}.frame_init_consts"), a_fic, b_fic)?;
        check_slice_eq(&format!("{p}.blocks"), a_fblocks, b_fblocks)?;
        check_eq(&format!("{p}.try_regions.len()"), &a_tr.len(), &b_tr.len())?;
        for (ri, (ra, rb)) in a_tr.iter().zip(b_tr.iter()).enumerate() {
            let TryRegion {
                protected: ra_prot,
                catches: ra_catches,
            } = ra;
            let TryRegion {
                protected: rb_prot,
                catches: rb_catches,
            } = rb;
            let rp = format!("{p}.try_regions[{ri}]");
            check_slice_eq(&format!("{rp}.protected"), ra_prot, rb_prot)?;
            check_eq(
                &format!("{rp}.catches.len()"),
                &ra_catches.len(),
                &rb_catches.len(),
            )?;
            for (ci, (ca_catch, cb_catch)) in ra_catches.iter().zip(rb_catches.iter()).enumerate() {
                let Catch {
                    handler: ca_h,
                    exception: ca_exc,
                    type_class: ca_tc,
                } = ca_catch;
                let Catch {
                    handler: cb_h,
                    exception: cb_exc,
                    type_class: cb_tc,
                } = cb_catch;
                let cp = format!("{rp}.catches[{ci}]");
                check_eq(&format!("{cp}.handler"), ca_h, cb_h)?;
                check_eq(&format!("{cp}.exception"), ca_exc, cb_exc)?;
                check_eq(&format!("{cp}.type_class"), ca_tc, cb_tc)?;
            }
        }
        match (a_dbg, b_dbg) {
            (None, None) => {}
            (Some(da), Some(db)) => {
                let DebugData {
                    source_file: da_sf,
                    source_code: da_sc,
                    line_table: da_lt,
                    column_table: da_ct,
                    local_names: da_ln,
                    param_names: da_pn,
                    scope_names: da_sn,
                } = da;
                let DebugData {
                    source_file: db_sf,
                    source_code: db_sc,
                    line_table: db_lt,
                    column_table: db_ct,
                    local_names: db_ln,
                    param_names: db_pn,
                    scope_names: db_sn,
                } = db;
                let dp = format!("{p}.debug");
                check_eq(&format!("{dp}.source_file"), da_sf, db_sf)?;
                check_eq(&format!("{dp}.source_code"), da_sc, db_sc)?;
                check_slice_eq(&format!("{dp}.line_table"), da_lt, db_lt)?;
                check_slice_eq(&format!("{dp}.column_table"), da_ct, db_ct)?;
                check_slice_eq(&format!("{dp}.local_names"), da_ln, db_ln)?;
                check_slice_eq(&format!("{dp}.param_names"), da_pn, db_pn)?;
                check_eq(&format!("{dp}.scope_names"), da_sn, db_sn)?;
            }
            _ => return Err(format!("{p}.debug mismatch: {a_dbg:?} != {b_dbg:?}")),
        }
        check_slice_eq(&format!("{p}.annotations"), a_anns, b_anns)?;
    }

    // 6. Basic blocks (`insts` + `preds`).
    check_eq("blocks.len()", &a_blocks.len(), &b_blocks.len())?;
    for (bi, (ba, bb)) in a_blocks.iter().zip(b_blocks.iter()).enumerate() {
        let Block {
            insts: ba_insts,
            preds: ba_preds,
        } = ba;
        let Block {
            insts: bb_insts,
            preds: bb_preds,
        } = bb;
        let bp = format!("blocks[{bi}]");
        check_slice_eq(&format!("{bp}.insts"), ba_insts, bb_insts)?;
        check_slice_eq(&format!("{bp}.preds"), ba_preds, bb_preds)?;
    }

    // 7. Instructions (`op`, `result`, `block`, `loc`).
    check_eq("insts.len()", &a_insts.len(), &b_insts.len())?;
    for (ii, (ia, ib)) in a_insts.iter().zip(b_insts.iter()).enumerate() {
        let Inst {
            op: ia_op,
            result: ia_res,
            block: ia_blk,
            loc: ia_loc,
        } = ia;
        let Inst {
            op: ib_op,
            result: ib_res,
            block: ib_blk,
            loc: ib_loc,
        } = ib;
        let ip = format!("insts[{ii}]");
        check_eq(&format!("{ip}.op"), ia_op, ib_op)?;
        check_eq(&format!("{ip}.result"), ia_res, ib_res)?;
        check_eq(&format!("{ip}.block"), ia_blk, ib_blk)?;
        check_eq(&format!("{ip}.loc"), ia_loc, ib_loc)?;
    }

    // 8. SSA values (`def`, `ty`).
    check_eq("values.len()", &a_values.len(), &b_values.len())?;
    for (vi, (va, vb)) in a_values.iter().zip(b_values.iter()).enumerate() {
        let Value {
            def: va_def,
            ty: va_ty,
        } = va;
        let Value {
            def: vb_def,
            ty: vb_ty,
        } = vb;
        let vp = format!("values[{vi}]");
        check_eq(&format!("{vp}.def"), va_def, vb_def)?;
        check_eq(&format!("{vp}.ty"), va_ty, vb_ty)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests;
