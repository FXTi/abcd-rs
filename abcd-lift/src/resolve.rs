//! Entity resolution: bytecode `EntityId` → [`Sym`] / [`FuncId`] /
//! [`ConstId`], and literal arrays → lossless typed [`Const`] trees (`#50`,
//! `#57` `R3-H9`).
//!
//! Method references resolve via dense [`MethodIdx`] slots in `MethodBody::entities`
//! to a [`FuncId`] — never name-keyed, never raw offsets. Strings are
//! content-keyed symbols, and literal arrays become lossless [`Const`] trees
//! on an explicit heap workstack.

use abcd_file::{EntityRef, File, LiteralValue, MethodBody, MethodIdx};
use abcd_ir::module::FunctionKind;
use abcd_ir::op::MemberAttrs;
use abcd_ir::{Const, ConstId, FuncId, LitMethodKind, Sym, TypedArrayTag};
use abcd_isa::{EntityId, EntityKind};

use crate::{LiftBackend, LiftError, Lifter};

/// Wrapper shape produced when finishing an expanded literal-array buffer (`#57` `R3-H9`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum LitWrap {
    /// Plain [`Const::ArrayLiteral`] (`LiteralTag::LITERALARRAY` or top-level buffer).
    PlainArray,
    /// [`Const::LiteralBufferRef`] wrapping a pooled [`Const::ArrayLiteral`]
    /// (`LiteralTag::LITERALBUFFERINDEX`).
    BufferRef,
}

/// Resolve an [`EntityId`] through the owning method's typed [`EntityRef`]
/// table to a symbol (string-pool entities).
pub(crate) fn resolve_sym<'f, B: LiftBackend<'f>>(
    lf: &mut B,
    body: &MethodBody,
    id: EntityId,
    kind: EntityKind,
) -> Result<Sym, LiftError> {
    let Some(entity) = body.entities.get(&(kind, id.0)) else {
        return Err(LiftError::UnresolvedEntity(id.0));
    };
    let file_sid = match *entity {
        EntityRef::String { id: sid, .. } => sid,
        _ => return Err(LiftError::UnresolvedEntity(id.0)),
    };
    lf.backend_sym_of_file_sid(file_sid)
        .ok_or(LiftError::UnresolvedEntity(id.0))
}

/// Resolve a method-reference [`EntityId`] to its display name and its
/// function-table index.
pub(crate) fn resolve_method<'f, B: LiftBackend<'f>>(
    lf: &B,
    body: &MethodBody,
    id: EntityId,
) -> Result<(Sym, FuncId), LiftError> {
    let Some(entity) = body.entities.get(&(EntityKind::MethodId, id.0)) else {
        return Err(LiftError::UnresolvedEntity(id.0));
    };
    match *entity {
        EntityRef::Method(midx) => {
            let func_id = func_of_idx(lf, midx).map_err(|_| LiftError::UnresolvedEntity(id.0))?;
            let name = lf
                .backend_method_name(midx)
                .ok_or(LiftError::UnresolvedEntity(id.0))?;
            Ok((name, func_id))
        }
        _ => Err(LiftError::UnresolvedEntity(id.0)),
    }
}

/// Resolve a dense [`MethodIdx`] to its [`FuncId`].
pub(crate) fn func_of_idx<'f, B: LiftBackend<'f>>(
    lf: &B,
    idx: MethodIdx,
) -> Result<FuncId, LiftError> {
    if idx.index() < lf.backend_method_count() {
        Ok(FuncId::new(idx.0))
    } else {
        Err(LiftError::UnresolvedEntity(idx.0))
    }
}

/// Resolve a literal-array [`EntityId`] to its decoded table index.
fn literal_table_index(body: &MethodBody, id: EntityId) -> Result<u32, LiftError> {
    match body.entities.get(&(EntityKind::LiteralarrayId, id.0)) {
        Some(EntityRef::LiteralArray(idx)) => Ok(idx.0),
        _ => Err(LiftError::UnresolvedEntity(id.0)),
    }
}

/// Resolve a literal-array [`EntityId`] to its pooled shape constant.
pub(crate) fn resolve_literal_const<'f, B: LiftBackend<'f>>(
    lf: &mut B,
    body: &MethodBody,
    id: EntityId,
) -> Result<ConstId, LiftError> {
    let idx = literal_table_index(body, id)?;
    lf.backend_resolve_lit_array(idx, LitWrap::PlainArray)
}

/// Parse the per-member attribute payloads (B2 — [`MemberAttrs`]) out of
/// a class member buffer (the literal array behind
/// `defineclasswithbuffer` / `callruntime.definesendableclass`).
///
/// Vendor-grounded member form (arkcompiler_ets_runtime-master): each
/// member is the literal-entry triple `string:<name>`,
/// `method|getter|setter|generator_method:<ref>`,
/// `method_affiliate:<length>` — the runtime collapse keeps (name,
/// value) pairs where the method-kind tag sets the materialized
/// function's `FunctionKind` and the affiliate materializes it
/// (`ecmascript/jspandafile/literal_data_extractor.cpp:588-624`). The
/// trailing `i32` is the count of NON-STATIC members ("hidden in the
/// last index of Literal buffer",
/// `ecmascript/jspandafile/class_info_extractor.cpp:36-42`); pairs
/// at-or-past that count install on the class object (static) —
/// `class_info_extractor.cpp:78` and `extractBegin = nonStaticNum * 2`.
///
/// The result parallels the pooled buffer's `MethodRef` sequence (the
/// same member order). A buffer outside this grounded form (accessor
/// payloads, data-valued members, nested arrays, a missing/mismatched
/// trailing count) yields an EMPTY vector — the documented conservative
/// fallback: consumers treat the attributes as unknown, never guessed.
pub(crate) fn class_member_attrs<'f, B: LiftBackend<'f>>(
    lf: &B,
    body: &MethodBody,
    id: EntityId,
    is_sendable: bool,
) -> Result<Vec<MemberAttrs>, LiftError> {
    let idx = literal_table_index(body, id)?;
    class_member_attrs_for_index(lf.file(), idx, is_sendable)
}

/// Parse the per-member attribute payloads ([`MemberAttrs`]) out of the
/// decoded literal array at `table_idx` (shared by entity-relocated modern /
/// decoded-legacy class buffers and direct-table-index `deprecated.*` tests).
pub fn class_member_attrs_for_index(
    file: &File,
    table_idx: u32,
    is_sendable: bool,
) -> Result<Vec<MemberAttrs>, LiftError> {
    let Some(arr) = file.literal_arrays.get(table_idx as usize) else {
        return Err(LiftError::LiteralArrayOutOfRange(table_idx));
    };
    let raw_values = &arr.values;
    // Sendable class buffers (`callruntime.definesendableclass`) append a
    // trailing `lit_offset` (`LiteralValue::LiteralArray` after decode, or
    // `LiteralValue::LiteralBufferIndex`) pointing to the field-type layout
    // literal array after the `i32` non-static member count
    // (`ClassInfoExtractor::BuildSendableClassInfoExtractor`). Strip that
    // single trailing slot only for sendable classes so `defineclasswithbuffer`
    // keeps rejecting unexpected nested arrays.
    let values = match (is_sendable, raw_values.last()) {
        (true, Some(LiteralValue::LiteralArray(_) | LiteralValue::LiteralBufferIndex(_))) => {
            &raw_values[..raw_values.len() - 1]
        }
        _ => raw_values.as_slice(),
    };
    let conservative = Vec::new();
    let mut kinds: Vec<FunctionKind> = Vec::new();
    let mut have_name = false;
    let mut pending_kind: Option<FunctionKind> = None;
    let mut non_static: Option<usize> = None;
    for (pos, v) in values.iter().enumerate() {
        let last = pos + 1 == values.len();
        match v {
            LiteralValue::String(_) => {
                if have_name || pending_kind.is_some() {
                    return Ok(conservative);
                }
                have_name = true;
            }
            LiteralValue::Method(_)
            | LiteralValue::GeneratorMethod(_)
            | LiteralValue::AsyncGeneratorMethod(_)
            | LiteralValue::Getter(_)
            | LiteralValue::Setter(_) => {
                if !have_name || pending_kind.is_some() {
                    return Ok(conservative);
                }
                pending_kind = Some(match v {
                    LiteralValue::Method(_) => FunctionKind::Function,
                    LiteralValue::GeneratorMethod(_) => FunctionKind::Generator,
                    LiteralValue::AsyncGeneratorMethod(_) => FunctionKind::AsyncGenerator,
                    LiteralValue::Getter(_) => FunctionKind::Getter,
                    LiteralValue::Setter(_) => FunctionKind::Setter,
                    _ => unreachable!("matched above"),
                });
            }
            LiteralValue::MethodAffiliate(_) => {
                let Some(kind) = pending_kind.take() else {
                    return Ok(conservative);
                };
                if !have_name {
                    return Ok(conservative);
                }
                have_name = false;
                kinds.push(kind);
            }
            // The trailing non-static member count (the vendor's "last
            // index" slot). Any other position/shape is ungrounded.
            LiteralValue::Integer(n) if last && !have_name && pending_kind.is_none() => {
                let Ok(count) = usize::try_from(*n) else {
                    return Ok(conservative);
                };
                non_static = Some(count);
            }
            _ => return Ok(conservative),
        }
    }
    if have_name || pending_kind.is_some() {
        return Ok(conservative);
    }
    let Some(non_static) = non_static else {
        return Ok(conservative);
    };
    if non_static > kinds.len() {
        return Ok(conservative);
    }
    Ok(kinds
        .into_iter()
        .enumerate()
        .map(|(i, kind)| MemberAttrs {
            is_static: i >= non_static,
            kind,
        })
        .collect())
}

/// Convert the literal array at `table_idx` into a pooled [`Const::ArrayLiteral`]
/// [`ConstId`] iteratively (memoized, cycle-guarded, O(1) native stack).
pub fn const_for_literal_array(lf: &mut Lifter, table_idx: u32) -> Result<ConstId, LiftError> {
    const_for_literal_array_with_wrap(lf, table_idx, LitWrap::PlainArray)
}

/// Convert the literal array at `table_idx` under `root_wrap` into a pooled
/// [`ConstId`] iteratively (memoized per `(table_idx, wrap)`, cycle-guarded,
/// O(1) native stack).
pub(crate) fn const_for_literal_array_with_wrap(
    lf: &mut Lifter,
    table_idx: u32,
    root_wrap: LitWrap,
) -> Result<ConstId, LiftError> {
    let first = match enter_literal_array(lf, table_idx, root_wrap)? {
        Ok(cached) => return Ok(cached),
        Err(frame) => frame,
    };
    let mut stack = vec![first];

    while let Some(next_elem) = stack.last().map(|f| f.next_elem) {
        let top_idx = stack.len() - 1;
        let values = stack[top_idx].values;
        if next_elem < values.len() {
            let v = &values[next_elem];
            stack[top_idx].next_elem += 1;
            let step = match step_literal_value(lf, v) {
                Ok(s) => s,
                Err(e) => {
                    for f in &stack {
                        lf.lit_active.remove(&f.table_idx);
                    }
                    return Err(e);
                }
            };
            match step {
                LitStep::Ready(c) => {
                    let cid = lf.module.consts.intern(c);
                    if let Some(parent) = stack.last_mut() {
                        parent.consts.push(cid);
                    }
                }
                LitStep::Nested { child_idx, wrap } => {
                    match enter_literal_array(lf, child_idx, wrap) {
                        Ok(Ok(cached)) => {
                            if let Some(parent) = stack.last_mut() {
                                parent.consts.push(cached);
                            }
                        }
                        Ok(Err(child_frame)) => stack.push(child_frame),
                        Err(e) => {
                            for f in &stack {
                                lf.lit_active.remove(&f.table_idx);
                            }
                            return Err(e);
                        }
                    }
                }
            }
        } else {
            let Some(finished) = stack.pop() else {
                break;
            };
            lf.lit_active.remove(&finished.table_idx);
            let cid = finish_literal_frame(lf, finished.table_idx, finished.wrap, finished.consts);
            if let Some(parent) = stack.last_mut() {
                parent.consts.push(cid);
            } else {
                return Ok(cid);
            }
        }
    }

    unreachable!("literal-array stack always returns when popping the root frame")
}

/// Pool and memoize a finished literal-array frame under its [`LitWrap`] shape,
/// keeping plain `ArrayLiteral` entries distinct from `LiteralBufferRef`
/// wrappers (`#57` `R3-H9`).
fn finish_literal_frame(
    lf: &mut Lifter,
    table_idx: u32,
    wrap: LitWrap,
    consts: Vec<ConstId>,
) -> ConstId {
    let cid = match wrap {
        LitWrap::PlainArray => lf.const_shape(Const::ArrayLiteral(consts)),
        LitWrap::BufferRef => {
            let arr_cid = lf.const_shape(Const::ArrayLiteral(consts));
            lf.lit_cache
                .insert((table_idx, LitWrap::PlainArray), arr_cid);
            lf.const_shape(Const::LiteralBufferRef(arr_cid))
        }
    };
    lf.lit_cache.insert((table_idx, wrap), cid);
    cid
}

/// Step outcome when converting one [`LiteralValue`] without native
/// call-stack recursion.
enum LitStep {
    /// Immediate scalar, string, or method-ref constant.
    Ready(Const),
    /// Nested literal-array reference at `child_idx` to expand on the
    /// explicit work stack under `wrap`.
    Nested { child_idx: u32, wrap: LitWrap },
}

/// Active frame on the iterative literal-array conversion stack.
struct LitFrame<'f> {
    table_idx: u32,
    wrap: LitWrap,
    values: &'f [LiteralValue],
    next_elem: usize,
    consts: Vec<ConstId>,
}

/// Look up `(table_idx, wrap)` in the memo cache or validate and activate a
/// new [`LitFrame`] for iterative expansion.
fn enter_literal_array<'f>(
    lf: &mut Lifter<'f>,
    table_idx: u32,
    wrap: LitWrap,
) -> Result<Result<ConstId, LitFrame<'f>>, LiftError> {
    if let Some(&cid) = lf.lit_cache.get(&(table_idx, wrap)) {
        return Ok(Ok(cid));
    }
    if matches!(wrap, LitWrap::BufferRef)
        && let Some(&arr_cid) = lf.lit_cache.get(&(table_idx, LitWrap::PlainArray))
    {
        let buf_cid = lf.const_shape(Const::LiteralBufferRef(arr_cid));
        lf.lit_cache
            .insert((table_idx, LitWrap::BufferRef), buf_cid);
        return Ok(Ok(buf_cid));
    }
    let file = lf.file;
    let Some(arr) = file.literal_arrays.get(table_idx as usize) else {
        return Err(LiftError::LiteralArrayOutOfRange(table_idx));
    };
    if !lf.lit_active.insert(table_idx) {
        return Err(LiftError::LiteralArrayCycle(table_idx));
    }
    Ok(Err(LitFrame {
        table_idx,
        wrap,
        values: &arr.values,
        next_elem: 0,
        consts: Vec::with_capacity(arr.values.len()),
    }))
}

/// Convert one literal value inside an annotation `LiteralArray` element to a
/// pooled [`ConstId`], degrading any unresolvable/cyclic element to
/// [`Const::Null`].
pub(crate) fn const_for_literal_value_or_null<'f, B: LiftBackend<'f>>(
    lf: &mut B,
    v: &LiteralValue,
) -> ConstId {
    match step_literal_value(lf, v) {
        Ok(LitStep::Ready(c)) => lf.backend_const_scalar(c),
        Ok(LitStep::Nested { child_idx, wrap }) => {
            lf.backend_try_lit_array_or_null(child_idx, wrap)
        }
        Err(_) => lf.backend_const_scalar(Const::Null),
    }
}

/// Classify a single [`LiteralValue`] into its lossless [`Const`] or a nested
/// literal-array expansion without recursing (`#57` `R3-H9`).
fn step_literal_value<'f, B: LiftBackend<'f>>(
    lf: &mut B,
    v: &LiteralValue,
) -> Result<LitStep, LiftError> {
    Ok(match v {
        LiteralValue::Bool(b) => LitStep::Ready(Const::Bool(*b)),
        LiteralValue::Integer8(n) => LitStep::Ready(Const::Int8(*n)),
        LiteralValue::Integer(n) => LitStep::Ready(Const::Int32(*n)),
        LiteralValue::Float(f) => LitStep::Ready(Const::float32(*f)),
        LiteralValue::Double(d) => LitStep::Ready(Const::number(*d)),
        LiteralValue::String(sid) => {
            let sym = lf
                .backend_sym_of_file_sid(*sid)
                .ok_or(LiftError::UnresolvedEntity(sid.index() as u32))?;
            LitStep::Ready(Const::String(sym))
        }
        LiteralValue::EtsImplements(sid) => {
            let sym = lf
                .backend_sym_of_file_sid(*sid)
                .ok_or(LiftError::UnresolvedEntity(sid.index() as u32))?;
            LitStep::Ready(Const::EtsImplements(sym))
        }
        LiteralValue::Method(idx) => LitStep::Ready(Const::method_ref_with_kind(
            func_of_idx(lf, *idx)?,
            LitMethodKind::Method,
        )),
        LiteralValue::GeneratorMethod(idx) => LitStep::Ready(Const::method_ref_with_kind(
            func_of_idx(lf, *idx)?,
            LitMethodKind::GeneratorMethod,
        )),
        LiteralValue::AsyncGeneratorMethod(idx) => LitStep::Ready(Const::method_ref_with_kind(
            func_of_idx(lf, *idx)?,
            LitMethodKind::AsyncGeneratorMethod,
        )),
        LiteralValue::Getter(idx) => LitStep::Ready(Const::method_ref_with_kind(
            func_of_idx(lf, *idx)?,
            LitMethodKind::Getter,
        )),
        LiteralValue::Setter(idx) => LitStep::Ready(Const::method_ref_with_kind(
            func_of_idx(lf, *idx)?,
            LitMethodKind::Setter,
        )),
        LiteralValue::Accessor(n) => LitStep::Ready(Const::Accessor(*n)),
        LiteralValue::MethodAffiliate(n) => LitStep::Ready(Const::MethodAffiliate(*n)),
        LiteralValue::BuiltinTypeIndex(n) => LitStep::Ready(Const::BuiltinTypeIndex(*n)),
        LiteralValue::NullValue(n) => LitStep::Ready(Const::LitNull(*n)),
        LiteralValue::LiteralArray(idx) => LitStep::Nested {
            child_idx: idx.0,
            wrap: LitWrap::PlainArray,
        },
        LiteralValue::LiteralBufferIndex(idx) => LitStep::Nested {
            child_idx: idx.0,
            wrap: LitWrap::BufferRef,
        },
        LiteralValue::ArrayU1(elems) => {
            let items = elems
                .iter()
                .map(|&x| lf.backend_const_scalar(Const::Bool(x)))
                .collect();
            LitStep::Ready(Const::TypedArrayLiteral {
                tag: TypedArrayTag::U1,
                items,
            })
        }
        LiteralValue::ArrayU8(elems) => {
            let items = elems
                .iter()
                .map(|&x| lf.backend_const_scalar(Const::Int8(x)))
                .collect();
            LitStep::Ready(Const::TypedArrayLiteral {
                tag: TypedArrayTag::U8,
                items,
            })
        }
        LiteralValue::ArrayI8(elems) => {
            let items = elems
                .iter()
                .map(|&x| lf.backend_const_scalar(Const::Int8(x as u8)))
                .collect();
            LitStep::Ready(Const::TypedArrayLiteral {
                tag: TypedArrayTag::I8,
                items,
            })
        }
        LiteralValue::ArrayU16(elems) => {
            let items = elems
                .iter()
                .map(|&x| lf.backend_const_scalar(Const::Int32(u32::from(x))))
                .collect();
            LitStep::Ready(Const::TypedArrayLiteral {
                tag: TypedArrayTag::U16,
                items,
            })
        }
        LiteralValue::ArrayI16(elems) => {
            let items = elems
                .iter()
                .map(|&x| lf.backend_const_scalar(Const::Int32(i32::from(x) as u32)))
                .collect();
            LitStep::Ready(Const::TypedArrayLiteral {
                tag: TypedArrayTag::I16,
                items,
            })
        }
        LiteralValue::ArrayU32(elems) => {
            let items = elems
                .iter()
                .map(|&x| lf.backend_const_scalar(Const::Int32(x)))
                .collect();
            LitStep::Ready(Const::TypedArrayLiteral {
                tag: TypedArrayTag::U32,
                items,
            })
        }
        LiteralValue::ArrayI32(elems) => {
            let items = elems
                .iter()
                .map(|&x| lf.backend_const_scalar(Const::Int32(x as u32)))
                .collect();
            LitStep::Ready(Const::TypedArrayLiteral {
                tag: TypedArrayTag::I32,
                items,
            })
        }
        LiteralValue::ArrayU64(elems) => {
            let items = elems
                .iter()
                .map(|&x| lf.backend_const_scalar(Const::UInt64(x)))
                .collect();
            LitStep::Ready(Const::TypedArrayLiteral {
                tag: TypedArrayTag::U64,
                items,
            })
        }
        LiteralValue::ArrayI64(elems) => {
            let items = elems
                .iter()
                .map(|&x| lf.backend_const_scalar(Const::Int64(x)))
                .collect();
            LitStep::Ready(Const::TypedArrayLiteral {
                tag: TypedArrayTag::I64,
                items,
            })
        }
        LiteralValue::ArrayF32(elems) => {
            let items = elems
                .iter()
                .map(|&x| lf.backend_const_scalar(Const::float32(x)))
                .collect();
            LitStep::Ready(Const::TypedArrayLiteral {
                tag: TypedArrayTag::F32,
                items,
            })
        }
        LiteralValue::ArrayF64(elems) => {
            let items = elems
                .iter()
                .map(|&x| lf.backend_const_scalar(Const::number(x)))
                .collect();
            LitStep::Ready(Const::TypedArrayLiteral {
                tag: TypedArrayTag::F64,
                items,
            })
        }
        LiteralValue::ArrayString(sids) => {
            let mut items = Vec::with_capacity(sids.len());
            for &sid in sids {
                let sym = lf
                    .backend_sym_of_file_sid(sid)
                    .ok_or(LiftError::UnresolvedEntity(sid.index() as u32))?;
                items.push(lf.backend_const_scalar(Const::String(sym)));
            }
            LitStep::Ready(Const::TypedArrayLiteral {
                tag: TypedArrayTag::String,
                items,
            })
        }
    })
}
