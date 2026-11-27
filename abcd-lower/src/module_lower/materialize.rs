//! Iterative literal-array / typed-array shape-tree materialization and
//! per-method entity relocation (`#30`, `#50`, `#84`).

use std::collections::{HashMap, HashSet};

use abcd_file::{
    CatchBlock, EntityRef, LiteralArray, LiteralArrayIdx, LiteralValue, MethodBody, MethodCode,
    MethodIdx, StringPool, TryBlock,
};
use abcd_ir::{Const, ConstId, FuncId, LitMethodKind, Module, Sym, TypedArrayTag};
use abcd_isa::EntityKind;

use super::intern_sym;
use crate::LowerError;
use crate::layout::{LayoutResult, LoweredTryBlock};
use crate::method_body::{BaseEntityIndex, relocate_and_compact_entities_in_place};

#[derive(Clone, Copy)]
enum MatNestedWrap {
    Array,
    BufferRef { wrapper_cid: ConstId },
}

fn wrap_literal_array_value(wrap: MatNestedWrap, idx: LiteralArrayIdx) -> LiteralValue {
    match wrap {
        MatNestedWrap::Array => LiteralValue::LiteralArray(idx),
        MatNestedWrap::BufferRef { .. } => LiteralValue::LiteralBufferIndex(idx),
    }
}

pub(super) struct Materializer<'m, 'f> {
    module: &'m Module,
    strings: &'f mut StringPool,
    literal_arrays: &'f mut Vec<LiteralArray>,
    func_to_method_idx: &'m [MethodIdx],
    synth_shapes: HashMap<ConstId, LiteralArrayIdx>,
}

impl<'m, 'f> Materializer<'m, 'f> {
    pub(super) fn new(
        module: &'m Module,
        strings: &'f mut StringPool,
        literal_arrays: &'f mut Vec<LiteralArray>,
        func_to_method_idx: &'m [MethodIdx],
    ) -> Self {
        Self {
            module,
            strings,
            literal_arrays,
            func_to_method_idx,
            synth_shapes: HashMap::new(),
        }
    }

    pub(super) fn build_method_body_owned(
        &mut self,
        func_id: FuncId,
        mut result: LayoutResult,
        base_index: Option<&BaseEntityIndex>,
    ) -> Result<MethodBody, LowerError> {
        let param_count = self
            .module
            .func(func_id)
            .map(|f| f.params.len())
            .unwrap_or_default();

        let entities =
            relocate_and_compact_entities_in_place(func_id, &mut result.bytecodes, |kind, raw| {
                match kind {
                    EntityKind::StringId => {
                        let sym = Sym::new(raw);
                        if let Some(r) = base_index
                            && let Some(eref) = r.string_ref(self.module, self.strings, sym)
                        {
                            Ok(eref)
                        } else {
                            self.string_ref(sym).ok_or(LowerError::UntraceableEntity {
                                func: func_id,
                                kind,
                                raw,
                            })
                        }
                    }
                    EntityKind::MethodId => {
                        self.method_ref(FuncId::new(raw))
                            .ok_or(LowerError::UntraceableEntity {
                                func: func_id,
                                kind,
                                raw,
                            })
                    }
                    EntityKind::LiteralarrayId => {
                        let cid = ConstId::new(raw);
                        if let Some(r) = base_index
                            && let Some(eref) = r.literal_array_ref(self.module, cid)
                        {
                            Ok(eref)
                        } else {
                            self.literal_array_idx(cid)
                                .map(EntityRef::LiteralArray)
                                .ok_or(LowerError::UntraceableEntity {
                                    func: func_id,
                                    kind,
                                    raw,
                                })
                        }
                    }
                }
            })?;

        let try_blocks = self.materialize_try_blocks(&result.try_blocks, func_id)?;

        Ok(MethodBody {
            num_vregs: u32::from(result.num_regs),
            num_args: param_count as u32,
            code: MethodCode::Decoded(result.bytecodes),
            entities,
            try_blocks,
            ic_size: Some(result.ic_size),
        })
    }

    fn materialize_try_blocks(
        &mut self,
        lowered: &[LoweredTryBlock],
        func_id: FuncId,
    ) -> Result<Vec<TryBlock>, LowerError> {
        let mut out = Vec::with_capacity(lowered.len());
        for tb in lowered {
            let mut catches = Vec::with_capacity(tb.catches.len());
            for c in &tb.catches {
                let type_class = match c.type_class {
                    None => None,
                    Some(cid) => {
                        let cls = self
                            .module
                            .class(cid)
                            .ok_or(LowerError::UntraceableEntity {
                                func: func_id,
                                kind: EntityKind::StringId,
                                raw: cid.0,
                            })?;
                        let sid = intern_sym(&self.module.sym, self.strings, cls.descriptor)
                            .ok_or(LowerError::UntraceableEntity {
                                func: func_id,
                                kind: EntityKind::StringId,
                                raw: cls.descriptor.0,
                            })?;
                        Some(sid)
                    }
                };
                catches.push(CatchBlock {
                    type_class,
                    handler: c.handler,
                    len: c.len,
                });
            }
            out.push(TryBlock {
                start: tb.start,
                len: tb.len,
                catches,
            });
        }
        Ok(out)
    }

    fn string_ref(&mut self, sym: Sym) -> Option<EntityRef> {
        let sid = intern_sym(&self.module.sym, self.strings, sym)?;
        Some(EntityRef::string(sid))
    }

    fn method_idx(&self, func: FuncId) -> Option<MethodIdx> {
        self.func_to_method_idx.get(func.index()).copied()
    }

    fn method_ref(&self, func: FuncId) -> Option<EntityRef> {
        self.method_idx(func).map(EntityRef::Method)
    }

    pub(super) fn literal_array_idx(&mut self, shape: ConstId) -> Option<LiteralArrayIdx> {
        if let Some(&idx) = self.synth_shapes.get(&shape) {
            return Some(idx);
        }
        self.materialize_shape_tree(shape)
    }

    fn materialize_shape_tree(&mut self, root_cid: ConstId) -> Option<LiteralArrayIdx> {
        let module = self.module;
        let mut active: HashSet<ConstId> = HashSet::new();
        let mut actual_root = root_cid;
        let root_const = loop {
            if !active.insert(actual_root) {
                return None;
            }
            match module.consts.get(actual_root)? {
                Const::LiteralBufferRef(inner) => actual_root = *inner,
                other => break other,
            }
        };
        if let Some(&existing) = self.synth_shapes.get(&actual_root) {
            self.synth_shapes.insert(root_cid, existing);
            return Some(existing);
        }
        if let Const::TypedArrayLiteral { tag, items } = root_const {
            let lit_val = self.materialize_typed_array(*tag, items)?;
            let idx = LiteralArrayIdx(self.literal_arrays.len() as u32);
            self.literal_arrays.push(LiteralArray::new(vec![lit_val]));
            self.synth_shapes.insert(actual_root, idx);
            self.synth_shapes.insert(root_cid, idx);
            return Some(idx);
        }
        let (root_cursor, root_cap) = ShapeCursor::from_const(root_const)?;
        let mut stack = vec![ShapeFrame {
            cid: actual_root,
            parent_wrap: None,
            cursor: root_cursor,
            values: Vec::with_capacity(root_cap),
        }];

        'outer: while let Some(mut frame) = stack.pop() {
            while let Some(child_cid) = frame.cursor.next_id() {
                let elem = module.consts.get(child_cid)?;
                if let Const::TypedArrayLiteral { tag, items } = elem {
                    frame
                        .values
                        .push(self.materialize_typed_array(*tag, items)?);
                    continue;
                }
                let nested = match elem {
                    Const::ArrayLiteral(_) | Const::ObjectLiteral { .. } => {
                        Some((child_cid, elem, MatNestedWrap::Array))
                    }
                    Const::LiteralBufferRef(inner_cid) => {
                        if active.contains(&child_cid) {
                            return None;
                        }
                        let inner_elem = module.consts.get(*inner_cid)?;
                        if let Const::TypedArrayLiteral { tag, items } = inner_elem {
                            let child_idx = if let Some(&cached) = self.synth_shapes.get(inner_cid)
                            {
                                cached
                            } else {
                                let lit_val = self.materialize_typed_array(*tag, items)?;
                                let idx = LiteralArrayIdx(self.literal_arrays.len() as u32);
                                self.literal_arrays.push(LiteralArray::new(vec![lit_val]));
                                self.synth_shapes.insert(*inner_cid, idx);
                                idx
                            };
                            frame
                                .values
                                .push(LiteralValue::LiteralBufferIndex(child_idx));
                            continue;
                        }
                        if !matches!(
                            inner_elem,
                            Const::ArrayLiteral(_) | Const::ObjectLiteral { .. }
                        ) {
                            return None;
                        }
                        Some((
                            *inner_cid,
                            inner_elem,
                            MatNestedWrap::BufferRef {
                                wrapper_cid: child_cid,
                            },
                        ))
                    }
                    _ => None,
                };

                if let Some((target_cid, target_elem, wrap)) = nested {
                    if active.contains(&target_cid) {
                        return None;
                    }
                    if let Some(&child_idx) = self.synth_shapes.get(&target_cid) {
                        frame.values.push(wrap_literal_array_value(wrap, child_idx));
                        continue;
                    }
                    let (child_cursor, child_cap) = ShapeCursor::from_const(target_elem)?;
                    if let MatNestedWrap::BufferRef { wrapper_cid } = wrap {
                        active.insert(wrapper_cid);
                    }
                    active.insert(target_cid);
                    stack.push(frame);
                    stack.push(ShapeFrame {
                        cid: target_cid,
                        parent_wrap: Some(wrap),
                        cursor: child_cursor,
                        values: Vec::with_capacity(child_cap),
                    });
                    continue 'outer;
                }
                frame.values.push(self.materialize_scalar_elem(elem)?);
            }

            active.remove(&frame.cid);
            if let Some(MatNestedWrap::BufferRef { wrapper_cid }) = frame.parent_wrap {
                active.remove(&wrapper_cid);
            }
            let idx = LiteralArrayIdx(self.literal_arrays.len() as u32);
            self.literal_arrays.push(LiteralArray::new(frame.values));
            self.synth_shapes.insert(frame.cid, idx);
            if let Some(parent) = stack.last_mut() {
                let wrap = frame.parent_wrap.unwrap_or(MatNestedWrap::Array);
                parent.values.push(wrap_literal_array_value(wrap, idx));
            } else {
                self.synth_shapes.insert(root_cid, idx);
                return Some(idx);
            }
        }
        None
    }

    fn materialize_scalar_elem(&mut self, c: &Const) -> Option<LiteralValue> {
        Some(match c {
            Const::Bool(b) => LiteralValue::Bool(*b),
            Const::Int8(n) => LiteralValue::Integer8(*n),
            Const::Int32(n) => LiteralValue::Integer(*n),
            Const::Float32(bits) => LiteralValue::Float(f32::from_bits(*bits)),
            Const::Number(bits) => LiteralValue::Double(f64::from_bits(*bits)),
            Const::Accessor(n) => LiteralValue::Accessor(*n),
            Const::MethodAffiliate(n) => LiteralValue::MethodAffiliate(*n),
            Const::BuiltinTypeIndex(n) => LiteralValue::BuiltinTypeIndex(*n),
            Const::LitNull(n) => LiteralValue::NullValue(*n),
            Const::Null | Const::Undefined | Const::Hole => LiteralValue::NullValue(0),
            Const::String(sym) | Const::BigInt(sym) => {
                let sid = intern_sym(&self.module.sym, self.strings, *sym)?;
                LiteralValue::String(sid)
            }
            Const::EtsImplements(sym) => {
                let sid = intern_sym(&self.module.sym, self.strings, *sym)?;
                LiteralValue::EtsImplements(sid)
            }
            Const::MethodRef { func, kind } => {
                let midx = self.method_idx(*func)?;
                match kind {
                    LitMethodKind::Method => LiteralValue::Method(midx),
                    LitMethodKind::GeneratorMethod => LiteralValue::GeneratorMethod(midx),
                    LitMethodKind::AsyncGeneratorMethod => LiteralValue::AsyncGeneratorMethod(midx),
                    LitMethodKind::Getter => LiteralValue::Getter(midx),
                    LitMethodKind::Setter => LiteralValue::Setter(midx),
                }
            }
            Const::Int64(_)
            | Const::UInt64(_)
            | Const::ArrayLiteral(_)
            | Const::TypedArrayLiteral { .. }
            | Const::ObjectLiteral { .. }
            | Const::LiteralBufferRef(_) => return None,
        })
    }

    fn materialize_typed_array(
        &mut self,
        tag: TypedArrayTag,
        items: &[ConstId],
    ) -> Option<LiteralValue> {
        let module = self.module;
        match tag {
            TypedArrayTag::U1 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let b = match module.consts.get(cid)? {
                        Const::Bool(b) => *b,
                        Const::Int8(n) if *n <= 1 => *n != 0,
                        Const::Int32(n) if *n <= 1 => *n != 0,
                        _ => return None,
                    };
                    out.push(b);
                }
                Some(LiteralValue::ArrayU1(out))
            }
            TypedArrayTag::U8 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int8(n) => *n,
                        Const::Int32(n) => u8::try_from(*n).ok()?,
                        Const::UInt64(n) => u8::try_from(*n).ok()?,
                        Const::Int64(n) => u8::try_from(*n).ok()?,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayU8(out))
            }
            TypedArrayTag::I8 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int8(n) => *n as i8,
                        Const::Int32(n) => i8::try_from(*n as i32).ok()?,
                        Const::Int64(n) => i8::try_from(*n).ok()?,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayI8(out))
            }
            TypedArrayTag::U16 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int8(n) => u16::from(*n),
                        Const::Int32(n) => u16::try_from(*n).ok()?,
                        Const::UInt64(n) => u16::try_from(*n).ok()?,
                        Const::Int64(n) => u16::try_from(*n).ok()?,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayU16(out))
            }
            TypedArrayTag::I16 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int8(n) => i16::from(*n as i8),
                        Const::Int32(n) => i16::try_from(*n as i32).ok()?,
                        Const::Int64(n) => i16::try_from(*n).ok()?,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayI16(out))
            }
            TypedArrayTag::U32 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int8(n) => u32::from(*n),
                        Const::Int32(n) => *n,
                        Const::UInt64(n) => u32::try_from(*n).ok()?,
                        Const::Int64(n) => u32::try_from(*n).ok()?,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayU32(out))
            }
            TypedArrayTag::I32 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int8(n) => i32::from(*n as i8),
                        Const::Int32(n) => *n as i32,
                        Const::Int64(n) => i32::try_from(*n).ok()?,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayI32(out))
            }
            TypedArrayTag::U64 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::UInt64(n) => *n,
                        Const::Int64(n) => u64::try_from(*n).ok()?,
                        Const::Int32(n) => u64::from(*n),
                        Const::Int8(n) => u64::from(*n),
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayU64(out))
            }
            TypedArrayTag::I64 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Int64(n) => *n,
                        Const::UInt64(n) => i64::try_from(*n).ok()?,
                        Const::Int32(n) => i64::from(*n as i32),
                        Const::Int8(n) => i64::from(*n as i8),
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayI64(out))
            }
            TypedArrayTag::F32 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Float32(b) => f32::from_bits(*b),
                        Const::Number(b) => f64::from_bits(*b) as f32,
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayF32(out))
            }
            TypedArrayTag::F64 => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let v = match module.consts.get(cid)? {
                        Const::Number(b) => f64::from_bits(*b),
                        Const::Float32(b) => f64::from(f32::from_bits(*b)),
                        _ => return None,
                    };
                    out.push(v);
                }
                Some(LiteralValue::ArrayF64(out))
            }
            TypedArrayTag::String => {
                let mut out = Vec::with_capacity(items.len());
                for &cid in items {
                    let Const::String(sym) = module.consts.get(cid)? else {
                        return None;
                    };
                    let sid = intern_sym(&module.sym, self.strings, *sym)?;
                    out.push(sid);
                }
                Some(LiteralValue::ArrayString(out))
            }
        }
    }
}

enum ShapeCursor<'t> {
    Array {
        items: &'t [ConstId],
        next: usize,
    },
    Object {
        keys: &'t [ConstId],
        values: &'t [ConstId],
        next: usize,
    },
}

impl<'t> ShapeCursor<'t> {
    fn from_const(tree: &'t Const) -> Option<(Self, usize)> {
        match tree {
            Const::ArrayLiteral(items) => Some((Self::Array { items, next: 0 }, items.len())),
            Const::ObjectLiteral { keys, values } => {
                if keys.len() != values.len() {
                    return None;
                }
                Some((
                    Self::Object {
                        keys,
                        values,
                        next: 0,
                    },
                    keys.len() * 2,
                ))
            }
            _ => None,
        }
    }

    fn next_id(&mut self) -> Option<ConstId> {
        match self {
            Self::Array { items, next } => {
                let id = *items.get(*next)?;
                *next += 1;
                Some(id)
            }
            Self::Object { keys, values, next } => {
                let pair_idx = *next / 2;
                let id = if *next % 2 == 0 {
                    *keys.get(pair_idx)?
                } else {
                    *values.get(pair_idx)?
                };
                *next += 1;
                Some(id)
            }
        }
    }
}

struct ShapeFrame<'t> {
    cid: ConstId,
    parent_wrap: Option<MatNestedWrap>,
    cursor: ShapeCursor<'t>,
    values: Vec<LiteralValue>,
}
