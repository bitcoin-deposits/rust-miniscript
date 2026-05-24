// SPDX-License-Identifier: CC0-1.0

//! Admission: the static checks a descriptor must pass before the protocol will evaluate against
//! it, at deposit-open and after each modification.
//!
//! Two checks, both linear and independent of any operation, witness, or state:
//!
//! 1. **Polarity** — every proof obligation occurs in positive position. This is what guarantees
//!    witness-monotonicity (see `PAPER.md` §3.1). Negation poisons rather than flips parity, so a
//!    proof obligation under any `not`, or in an `if` condition, is rejected. The `match`
//!    scrutinee and all `cmp`/`state`/value-function arguments are sort `V` and cannot contain a
//!    proof obligation, so only `not` and the `if` condition are non-vacuous.
//! 2. **Capability** — every value function, state predicate, and obligation form is in the
//!    operator's declared set.
//!
//! A third, var-resolution, is folded in: every `with(...)` reference must resolve. This makes the
//! `UnresolvedVar` evaluation error unreachable post-admission, so evaluation of an admitted
//! descriptor is total.

use crate::prelude::*;

use super::ast::{BTerm, Descriptor, Obligation, VTerm};
use super::capability::CapabilitySet;
use super::limits::MAX_DEPTH;
use super::registry::{StatePred, ValueFn};
use crate::MiniscriptKey;

/// A reason a descriptor was not admitted.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AdmissionError {
    /// A proof obligation appears in a non-positive position (under `not`, or in an `if`
    /// condition).
    NegativeProof,
    /// A value function used by the descriptor is not in the operator's capability set.
    UncapableValueFn(ValueFn),
    /// A state predicate used by the descriptor is not in the operator's capability set.
    UncapableStatePred(StatePred),
    /// A proof-obligation form used by the descriptor is not in the operator's capability set.
    UncapableObligation(super::capability::ObligationKind),
    /// A `with(...)` reference that does not resolve to a bound constant.
    UnresolvedVar(String),
    /// The descriptor's term exceeds [`MAX_DEPTH`](super::limits::MAX_DEPTH). Admitted descriptors
    /// are therefore bounded by `MAX_DEPTH`, which downstream evaluators rely on.
    TooDeep,
}

/// Run all admission checks on a descriptor against an operator's capability set.
pub fn admit<Pk: MiniscriptKey>(
    d: &Descriptor<Pk>,
    caps: &CapabilitySet,
) -> Result<(), AdmissionError> {
    // `tr(K)` has no body and is trivially admissible (the key isn't a tree). For wsh and tr-with-
    // body, the body is checked the same way.
    if let Some(body) = d.body() {
        if !body.has_depth_at_most(MAX_DEPTH) {
            return Err(AdmissionError::TooDeep);
        }
        check_polarity(body, true)?;
        check_b(body, caps, &d.constants)?;
    }
    Ok(())
}

/// Check the polarity rule alone: every `prove` occurs in positive position.
///
/// `positive` is the polarity of the context enclosing `t`.
pub fn check_polarity<Pk: MiniscriptKey>(
    t: &BTerm<Pk>,
    positive: bool,
) -> Result<(), AdmissionError> {
    match t {
        BTerm::Prove(_) => {
            if positive {
                Ok(())
            } else {
                Err(AdmissionError::NegativeProof)
            }
        }
        BTerm::Not(b) => check_polarity(b, false),
        BTerm::If(c, then_, els) => {
            check_polarity(c, false)?;
            check_polarity(then_, positive)?;
            check_polarity(els, positive)
        }
        BTerm::And(bs) | BTerm::Or(bs) => {
            for b in bs {
                check_polarity(b, positive)?;
            }
            Ok(())
        }
        BTerm::Thresh(_, bs) => {
            for b in bs {
                check_polarity(b, positive)?;
            }
            Ok(())
        }
        BTerm::Match { arms, default, .. } => {
            for (_, b) in arms {
                check_polarity(b, positive)?;
            }
            check_polarity(default, positive)
        }
        // Sort V holds no obligations; constants hold none.
        BTerm::Const(_) | BTerm::Cmp(_, _, _) | BTerm::State(_, _) => Ok(()),
    }
}

fn check_b<Pk: MiniscriptKey>(
    t: &BTerm<Pk>,
    caps: &CapabilitySet,
    env: &BTreeMap<String, super::value::Value<Pk>>,
) -> Result<(), AdmissionError> {
    match t {
        BTerm::Const(_) => Ok(()),
        BTerm::And(bs) | BTerm::Or(bs) | BTerm::Thresh(_, bs) => {
            for b in bs {
                check_b(b, caps, env)?;
            }
            Ok(())
        }
        BTerm::Not(b) => check_b(b, caps, env),
        BTerm::If(c, t1, e) => {
            check_b(c, caps, env)?;
            check_b(t1, caps, env)?;
            check_b(e, caps, env)
        }
        BTerm::Match { scrutinee, arms, default } => {
            check_v(scrutinee, caps, env)?;
            for (_, b) in arms {
                check_b(b, caps, env)?;
            }
            check_b(default, caps, env)
        }
        BTerm::Cmp(_, a, b) => {
            check_v(a, caps, env)?;
            check_v(b, caps, env)
        }
        BTerm::State(p, args) => {
            if !caps.state_preds.contains(p) {
                return Err(AdmissionError::UncapableStatePred(*p));
            }
            for a in args {
                check_v(a, caps, env)?;
            }
            Ok(())
        }
        BTerm::Prove(o) => check_o(o, caps, env),
    }
}

fn check_v<Pk: MiniscriptKey>(
    t: &VTerm<Pk>,
    caps: &CapabilitySet,
    env: &BTreeMap<String, super::value::Value<Pk>>,
) -> Result<(), AdmissionError> {
    match t {
        VTerm::Lit(_) => Ok(()),
        VTerm::Var(name) => {
            if env.contains_key(name) {
                Ok(())
            } else {
                Err(AdmissionError::UnresolvedVar(name.clone()))
            }
        }
        VTerm::Op(f, args) => {
            if !caps.value_fns.contains(f) {
                return Err(AdmissionError::UncapableValueFn(*f));
            }
            for a in args {
                check_v(a, caps, env)?;
            }
            Ok(())
        }
    }
}

fn check_o<Pk: MiniscriptKey>(
    o: &Obligation<Pk>,
    caps: &CapabilitySet,
    env: &BTreeMap<String, super::value::Value<Pk>>,
) -> Result<(), AdmissionError> {
    if !caps.obligations.contains(&o.kind()) {
        return Err(AdmissionError::UncapableObligation(o.kind()));
    }
    match o {
        Obligation::Pk(v)
        | Obligation::PkH(v)
        | Obligation::PkAny(v)
        | Obligation::Multi(_, v)
        | Obligation::Hashlock(v)
        | Obligation::Attest(v, _) => check_v(v, caps, env),
    }
}
