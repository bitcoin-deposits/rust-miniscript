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
use super::ast::{BTerm, Descriptor};
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
pub fn candidate<Pk, O>(current: &Descriptor<Pk>, op: &O) -> Result<Descriptor<Pk>, ModifyError>
where
    Pk: MiniscriptKey,
    O: Operation<Pk>,
{
    let path = op.path().ok_or(ModifyError::MissingArg("path"))?;
    let body = match op.op_type().as_str() {
        "replace" => {
            let sub = op.subtree().ok_or(ModifyError::MissingArg("subtree"))?;
            replace_at(&current.body, &path, sub)?
        }
        "insert" => {
            let sub = op.subtree().ok_or(ModifyError::MissingArg("subtree"))?;
            insert_at(&current.body, &path, sub)?
        }
        "delete" => delete_at(&current.body, &path)?,
        other => return Err(ModifyError::NotAModification(other.to_string())),
    };
    Ok(Descriptor { constants: current.constants.clone(), body })
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
