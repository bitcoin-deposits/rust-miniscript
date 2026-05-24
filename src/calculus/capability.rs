// SPDX-License-Identifier: CC0-1.0

//! Operator capability declarations.
//!
//! An operator advertises which extended primitives it implements. A descriptor may be admitted
//! only if every value function, state predicate, and proof-obligation form it uses is in the
//! operator's set. The boolean connectives (`and`/`or`/`thresh`/`not`/`if`/`match`/`cmp`) are the
//! always-on calculus core and are never gated.

use crate::prelude::*;

use super::ast::Obligation;
use super::registry::{StatePred, ValueFn};

/// The form of a proof obligation, independent of its arguments. The unit of capability
/// declaration for obligations.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum ObligationKind {
    /// `pk`.
    Pk,
    /// `pk_h`.
    PkH,
    /// `pk_any`.
    PkAny,
    /// `pk_threshold`.
    Multi,
    /// `hashlock`.
    Hashlock,
    /// `attest`.
    Attest,
}

impl<Pk: crate::MiniscriptKey> Obligation<Pk> {
    /// The capability-relevant form of this obligation.
    pub fn kind(&self) -> ObligationKind {
        match self {
            Obligation::Pk(_) => ObligationKind::Pk,
            Obligation::PkH(_) => ObligationKind::PkH,
            Obligation::PkAny(_) => ObligationKind::PkAny,
            Obligation::Multi(_, _) => ObligationKind::Multi,
            Obligation::Hashlock(_) => ObligationKind::Hashlock,
            Obligation::Attest(_, _) => ObligationKind::Attest,
        }
    }
}

/// Every value function, for building unrestricted capability sets.
const ALL_VALUE_FNS: [ValueFn; 21] = [
    ValueFn::Add,
    ValueFn::Sub,
    ValueFn::Mul,
    ValueFn::Div,
    ValueFn::Min,
    ValueFn::Max,
    ValueFn::Pct,
    ValueFn::Bps,
    ValueFn::OperationType,
    ValueFn::OperationArg,
    ValueFn::OperationPath,
    ValueFn::OperationSubtree,
    ValueFn::BlocksSinceActivity,
    ValueFn::BlocksSinceOpen,
    ValueFn::DepositBalance,
    ValueFn::RollingWindow,
    ValueFn::CumulativeSpentVia,
    ValueFn::AstRef,
    ValueFn::AstShapeAt,
    ValueFn::Path,
    ValueFn::BlocksSinceReceived,
];

const ALL_STATE_PREDS: [StatePred; 16] = [
    StatePred::Older,
    StatePred::After,
    StatePred::AmountAtMost,
    StatePred::AmountInRange,
    StatePred::AmountAtMostPct,
    StatePred::DestinationIs,
    StatePred::DestinationIn,
    StatePred::BalanceAtLeast,
    StatePred::BalanceAtMost,
    StatePred::BlocksSinceActivityAtLeast,
    StatePred::BlocksSinceOpenBelow,
    StatePred::RollingAmountBelow,
    StatePred::RollingAmountBelowPct,
    StatePred::SubtreeAt,
    StatePred::BlocksSinceOpenAtLeast,
    StatePred::BlocksSinceReceivedAtLeast,
];

const ALL_OBLIGATIONS: [ObligationKind; 6] = [
    ObligationKind::Pk,
    ObligationKind::PkH,
    ObligationKind::PkAny,
    ObligationKind::Multi,
    ObligationKind::Hashlock,
    ObligationKind::Attest,
];

/// A declared capability set.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CapabilitySet {
    /// Supported value functions.
    pub value_fns: BTreeSet<ValueFn>,
    /// Supported state predicates.
    pub state_preds: BTreeSet<StatePred>,
    /// Supported proof-obligation forms.
    pub obligations: BTreeSet<ObligationKind>,
}

impl CapabilitySet {
    /// The empty capability set (only the always-on boolean core is usable).
    pub fn empty() -> Self {
        CapabilitySet {
            value_fns: BTreeSet::new(),
            state_preds: BTreeSet::new(),
            obligations: BTreeSet::new(),
        }
    }

    /// The protocol-mandated minimum every operator must implement: the miniscript-equivalent
    /// core (`pk`, `pk_h`, the four hashlocks, `older`, `after`).
    pub fn minimum() -> Self {
        let mut c = Self::empty();
        c.obligations.insert(ObligationKind::Pk);
        c.obligations.insert(ObligationKind::PkH);
        c.obligations.insert(ObligationKind::Hashlock);
        c.state_preds.insert(StatePred::Older);
        c.state_preds.insert(StatePred::After);
        c
    }

    /// A capability set containing every declared primitive. Useful in tests and for operators
    /// that advertise the full surface.
    pub fn everything() -> Self {
        CapabilitySet {
            value_fns: ALL_VALUE_FNS.iter().copied().collect(),
            state_preds: ALL_STATE_PREDS.iter().copied().collect(),
            obligations: ALL_OBLIGATIONS.iter().copied().collect(),
        }
    }

    /// Add a value function.
    pub fn with_value_fn(mut self, f: ValueFn) -> Self {
        self.value_fns.insert(f);
        self
    }

    /// Add a state predicate.
    pub fn with_state_pred(mut self, p: StatePred) -> Self {
        self.state_preds.insert(p);
        self
    }

    /// Add a proof-obligation form.
    pub fn with_obligation(mut self, o: ObligationKind) -> Self {
        self.obligations.insert(o);
        self
    }
}
