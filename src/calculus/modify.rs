// SPDX-License-Identifier: CC0-1.0

//! Modification: computing the candidate descriptor `T'` an `insert` / `replace` / `delete`
//! produces, and admitting it.
//!
//! A modification operation targets an ast path. The candidate `T'` is computed functionally from
//! the current descriptor and the operation's arguments, then re-run through admission. The
//! deposit binds to `T'` only if admission passes; a modification yielding an ill-formed term is
//! rejected even though the current descriptor authorized the underlying request. This is what
//! keeps the witness-monotonicity invariant true across the whole sequence of terms a deposit's
//! history produces.

use crate::prelude::*;
use crate::MiniscriptKey;

use super::admission::{admit, AdmissionError};
use super::ast::{BTerm, Descriptor, Scheme};
use super::capability::CapabilitySet;
use super::host::Operation;
use super::limits::MAX_DEPTH;

/// A modification that cannot be applied to the term structure.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ModifyError {
    /// The path does not address an existing position.
    PathOutOfRange,
    /// `insert`/`delete` targeted a position that is not a variadic container child.
    NotAContainer,
    /// `insert`/`delete` was given an empty path (there is no parent to modify).
    EmptyPath,
    /// The operation type is not a modification.
    NotAModification(String),
    /// A required operation argument was absent.
    MissingArg(&'static str),
    /// The path exceeded [`MAX_DEPTH`](super::limits::MAX_DEPTH), so navigating it would recurse
    /// further than the calculus permits.
    PathTooDeep,
}

/// A modification rejected at admission time.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ModificationRejected {
    /// The candidate could not be constructed from the term and arguments.
    Malformed(ModifyError),
    /// The candidate was constructed but failed admission (polarity, capability, var-resolution).
    Inadmissible(AdmissionError),
}

/// Replace the subterm at `path` with `new`.
pub fn replace_at<Pk: MiniscriptKey>(
    t: &BTerm<Pk>,
    path: &[usize],
    new: BTerm<Pk>,
) -> Result<BTerm<Pk>, ModifyError> {
    if path.len() > MAX_DEPTH {
        return Err(ModifyError::PathTooDeep);
    }
    update_at(t, path, move |_| Ok(new))
}

/// Delete the subterm at `path` from its (variadic) parent.
pub fn delete_at<Pk: MiniscriptKey>(
    t: &BTerm<Pk>,
    path: &[usize],
) -> Result<BTerm<Pk>, ModifyError> {
    if path.len() > MAX_DEPTH {
        return Err(ModifyError::PathTooDeep);
    }
    let (idx, parent) = path.split_last().ok_or(ModifyError::EmptyPath)?;
    let idx = *idx;
    update_at(t, parent, move |c| remove_child(c, idx))
}

/// Insert `new` at position `path` (the last index is the position in the parent container).
pub fn insert_at<Pk: MiniscriptKey>(
    t: &BTerm<Pk>,
    path: &[usize],
    new: BTerm<Pk>,
) -> Result<BTerm<Pk>, ModifyError> {
    if path.len() > MAX_DEPTH {
        return Err(ModifyError::PathTooDeep);
    }
    let (idx, parent) = path.split_last().ok_or(ModifyError::EmptyPath)?;
    let idx = *idx;
    update_at(t, parent, move |c| insert_child(c, idx, new))
}

/// Apply `f` to the subterm at `path`, rebuilding the ancestors.
fn update_at<Pk, F>(t: &BTerm<Pk>, path: &[usize], f: F) -> Result<BTerm<Pk>, ModifyError>
where
    Pk: MiniscriptKey,
    F: FnOnce(&BTerm<Pk>) -> Result<BTerm<Pk>, ModifyError>,
{
    match path.split_first() {
        None => f(t),
        Some((i, rest)) => map_child(t, *i, move |c| update_at(c, rest, f)),
    }
}

/// Rebuild `t` with its `i`-th boolean child replaced by `f(child)`.
fn map_child<Pk, F>(t: &BTerm<Pk>, i: usize, f: F) -> Result<BTerm<Pk>, ModifyError>
where
    Pk: MiniscriptKey,
    F: FnOnce(&BTerm<Pk>) -> Result<BTerm<Pk>, ModifyError>,
{
    match t {
        BTerm::And(bs) => Ok(BTerm::And(replace_in_vec(bs, i, f)?)),
        BTerm::Or(bs) => Ok(BTerm::Or(replace_in_vec(bs, i, f)?)),
        BTerm::Thresh(k, bs) => Ok(BTerm::Thresh(*k, replace_in_vec(bs, i, f)?)),
        BTerm::Not(b) if i == 0 => Ok(BTerm::Not(Box::new(f(b)?))),
        BTerm::If(c, t1, e) => match i {
            0 => Ok(BTerm::If(Box::new(f(c)?), t1.clone(), e.clone())),
            1 => Ok(BTerm::If(c.clone(), Box::new(f(t1)?), e.clone())),
            2 => Ok(BTerm::If(c.clone(), t1.clone(), Box::new(f(e)?))),
            _ => Err(ModifyError::PathOutOfRange),
        },
        BTerm::Match { scrutinee, arms, default } => {
            if i < arms.len() {
                let mut arms2 = arms.clone();
                let body = f(&arms[i].1)?;
                arms2[i] = (arms[i].0.clone(), body);
                Ok(BTerm::Match { scrutinee: scrutinee.clone(), arms: arms2, default: default.clone() })
            } else if i == arms.len() {
                Ok(BTerm::Match {
                    scrutinee: scrutinee.clone(),
                    arms: arms.clone(),
                    default: Box::new(f(default)?),
                })
            } else {
                Err(ModifyError::PathOutOfRange)
            }
        }
        _ => Err(ModifyError::PathOutOfRange),
    }
}

fn replace_in_vec<Pk, F>(bs: &[BTerm<Pk>], i: usize, f: F) -> Result<Vec<BTerm<Pk>>, ModifyError>
where
    Pk: MiniscriptKey,
    F: FnOnce(&BTerm<Pk>) -> Result<BTerm<Pk>, ModifyError>,
{
    if i >= bs.len() {
        return Err(ModifyError::PathOutOfRange);
    }
    let mut out = bs.to_vec();
    out[i] = f(&bs[i])?;
    Ok(out)
}

fn remove_child<Pk: MiniscriptKey>(t: &BTerm<Pk>, idx: usize) -> Result<BTerm<Pk>, ModifyError> {
    let rm = |bs: &[BTerm<Pk>]| -> Result<Vec<BTerm<Pk>>, ModifyError> {
        if idx >= bs.len() {
            return Err(ModifyError::PathOutOfRange);
        }
        let mut out = bs.to_vec();
        out.remove(idx);
        Ok(out)
    };
    match t {
        BTerm::And(bs) => Ok(BTerm::And(rm(bs)?)),
        BTerm::Or(bs) => Ok(BTerm::Or(rm(bs)?)),
        BTerm::Thresh(k, bs) => Ok(BTerm::Thresh(*k, rm(bs)?)),
        BTerm::Match { scrutinee, arms, default } if idx < arms.len() => {
            let mut arms2 = arms.clone();
            arms2.remove(idx);
            Ok(BTerm::Match { scrutinee: scrutinee.clone(), arms: arms2, default: default.clone() })
        }
        _ => Err(ModifyError::NotAContainer),
    }
}

fn insert_child<Pk: MiniscriptKey>(
    t: &BTerm<Pk>,
    idx: usize,
    new: BTerm<Pk>,
) -> Result<BTerm<Pk>, ModifyError> {
    let ins = |bs: &[BTerm<Pk>]| -> Result<Vec<BTerm<Pk>>, ModifyError> {
        if idx > bs.len() {
            return Err(ModifyError::PathOutOfRange);
        }
        let mut out = bs.to_vec();
        out.insert(idx, new);
        Ok(out)
    };
    match t {
        BTerm::And(bs) => Ok(BTerm::And(ins(bs)?)),
        BTerm::Or(bs) => Ok(BTerm::Or(ins(bs)?)),
        BTerm::Thresh(k, bs) => Ok(BTerm::Thresh(*k, ins(bs)?)),
        // Inserting into a `match` would require a branch tag; not supported in v1.
        _ => Err(ModifyError::NotAContainer),
    }
}

/// Compute the candidate descriptor an `insert`/`replace`/`delete` operation would produce.
///
/// Paths are *descriptor-rooted* (see [`Descriptor::node_at`](super::ast::Descriptor::node_at)):
/// the leading index selects which structural slot the operation addresses, and the rest navigates
/// inside it. For `wsh(body)` the only slot is `[0]` (the body root); for `tr(K, body)`, `[0]`
/// addresses the internal key and `[1, …]` addresses positions in the body. Internal-key rotation
/// is `replace` at `[0]` of a `tr` descriptor, with the new key supplied as the `key` argument.
pub fn candidate<Pk, O>(current: &Descriptor<Pk>, op: &O) -> Result<Descriptor<Pk>, ModifyError>
where
    Pk: MiniscriptKey,
    O: Operation<Pk>,
{
    let path = op.path().ok_or(ModifyError::MissingArg("path"))?;
    let op_type = op.op_type();
    let (head, rest) = path.split_first().ok_or(ModifyError::EmptyPath)?;
    match &current.scheme {
        Scheme::Wsh { body } => {
            // wsh's only structural slot is the body, at `[0]`.
            if *head != 0 {
                return Err(ModifyError::PathOutOfRange);
            }
            let new_body = apply_body_op(body, op_type.as_str(), rest, op)?;
            Ok(Descriptor {
                constants: current.constants.clone(),
                scheme: Scheme::Wsh { body: new_body },
            })
        }
        Scheme::Tr { internal_key, body } => match *head {
            0 => {
                // Path addresses the internal key. The descriptor's shape is fixed by the scheme,
                // so insert and delete aren't meaningful here (no siblings of K, no descriptor
                // without K); only `replace` rotates the key.
                if !rest.is_empty() {
                    return Err(ModifyError::PathOutOfRange);
                }
                if op_type.as_str() != "replace" {
                    return Err(ModifyError::NotAModification(format!(
                        "internal-key rotation requires `replace`, got `{}`",
                        op_type.as_str()
                    )));
                }
                let new_key = match op.arg("key") {
                    Some(super::value::Value::Key(k)) => k,
                    _ => return Err(ModifyError::MissingArg("key")),
                };
                Ok(Descriptor {
                    constants: current.constants.clone(),
                    scheme: Scheme::Tr { internal_key: new_key, body: body.clone() },
                })
            }
            1 => {
                // Path addresses the body. `tr(K)` (no body) cannot satisfy this — there is
                // nothing at `[1, …]` to address.
                let body = body.as_ref().ok_or(ModifyError::MissingArg("body"))?;
                let new_body = apply_body_op(body, op_type.as_str(), rest, op)?;
                Ok(Descriptor {
                    constants: current.constants.clone(),
                    scheme: Scheme::Tr {
                        internal_key: internal_key.clone(),
                        body: Some(new_body),
                    },
                })
            }
            _ => Err(ModifyError::PathOutOfRange),
        },
    }
}

/// Apply a body-level `insert`/`replace`/`delete` at the body-rooted sub-path.
fn apply_body_op<Pk, O>(
    body: &BTerm<Pk>,
    op_type: &str,
    body_path: &[usize],
    op: &O,
) -> Result<BTerm<Pk>, ModifyError>
where
    Pk: MiniscriptKey,
    O: Operation<Pk>,
{
    match op_type {
        "replace" => {
            let sub = op.subtree().ok_or(ModifyError::MissingArg("subtree"))?;
            replace_at(body, body_path, sub)
        }
        "insert" => {
            let sub = op.subtree().ok_or(ModifyError::MissingArg("subtree"))?;
            insert_at(body, body_path, sub)
        }
        "delete" => delete_at(body, body_path),
        other => Err(ModifyError::NotAModification(other.to_string())),
    }
}

/// Compute the candidate descriptor and re-run admission on it. Returns the new descriptor only if
/// it is well-formed; otherwise the modification is rejected and the deposit keeps its current
/// descriptor.
pub fn admit_modification<Pk, O>(
    current: &Descriptor<Pk>,
    op: &O,
    caps: &CapabilitySet,
) -> Result<Descriptor<Pk>, ModificationRejected>
where
    Pk: MiniscriptKey,
    O: Operation<Pk>,
{
    let cand = candidate(current, op).map_err(ModificationRejected::Malformed)?;
    admit(&cand, caps).map_err(ModificationRejected::Inadmissible)?;
    Ok(cand)
}
