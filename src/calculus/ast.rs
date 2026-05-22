// SPDX-License-Identifier: CC0-1.0

//! The sort-indexed term calculus.
//!
//! The three sorts of the calculus are three separate Rust types: [`BTerm`] (sort `B`, the
//! authorization decisions), [`VTerm`] (sort `V`, values), and [`Obligation`] (sort `O`, proof
//! obligations injected into `B` by [`BTerm::Prove`]). Because `cmp`, `state`, and the `match`
//! scrutinee hold [`VTerm`] children — which cannot contain a [`BTerm::Prove`] — the sort
//! discipline that "`prove` never appears in a value position" is enforced by construction. The
//! only remaining placement constraint, the polarity rule, is checked by [`super::admission`].

use crate::prelude::*;
use crate::MiniscriptKey;

use super::registry::{CmpOp, StatePred, Symbol, ValueFn};
use super::schema::Schema;
use super::value::Value;

/// A term of sort `B`: an authorization decision.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum BTerm<Pk: MiniscriptKey> {
    /// A boolean constant: `true` (trivially satisfied) or `false` (unsatisfiable).
    Const(bool),
    /// Conjunction. Holds when every child holds.
    And(Vec<BTerm<Pk>>),
    /// Disjunction. Holds when some child holds.
    Or(Vec<BTerm<Pk>>),
    /// Threshold. Holds when at least `k` children hold.
    Thresh(usize, Vec<BTerm<Pk>>),
    /// Negation. The argument may not contain a proof obligation (polarity rule).
    Not(Box<BTerm<Pk>>),
    /// Conditional. The condition may not contain a proof obligation (polarity rule).
    If(Box<BTerm<Pk>>, Box<BTerm<Pk>>, Box<BTerm<Pk>>),
    /// Multi-way dispatch on a value, with a mandatory default branch.
    Match {
        /// The value matched against branch tags.
        scrutinee: VTerm<Pk>,
        /// Tagged branches.
        arms: Vec<(Symbol, BTerm<Pk>)>,
        /// The `else` branch, taken when no tag matches.
        default: Box<BTerm<Pk>>,
    },
    /// Comparison of two values.
    Cmp(CmpOp, VTerm<Pk>, VTerm<Pk>),
    /// A state predicate applied to value arguments.
    State(StatePred, Vec<VTerm<Pk>>),
    /// A proof obligation, discharged by the witness.
    Prove(Obligation<Pk>),
}

/// A term of sort `V`: a value expression. Evaluates by total functions of the operation and
/// ledger state, never the witness.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum VTerm<Pk: MiniscriptKey> {
    /// A literal value.
    Lit(Value<Pk>),
    /// A reference to a `with(...)` constant, resolved at admission.
    Var(String),
    /// A value function applied to value arguments.
    Op(ValueFn, Vec<VTerm<Pk>>),
}

/// A term of sort `O`: a proof obligation. The only construct whose evaluation depends on the
/// witness.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Obligation<Pk: MiniscriptKey> {
    /// Signed by a key.
    Pk(VTerm<Pk>),
    /// Signed by a key whose hash is given (the witness reveals the key).
    PkH(VTerm<Pk>),
    /// Signed by at least one key in a list.
    PkAny(VTerm<Pk>),
    /// Signed by at least `k` distinct keys in a list.
    PkThreshold(usize, VTerm<Pk>),
    /// A preimage of a hash is revealed.
    Hashlock(VTerm<Pk>),
    /// An oracle attestation matching a schema is supplied.
    Attest(VTerm<Pk>, Schema),
}

/// A complete descriptor: a `with(...)` constant environment together with a body of sort `B`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Descriptor<Pk: MiniscriptKey> {
    /// Named constants, bound once at deposit-open.
    pub constants: BTreeMap<String, Value<Pk>>,
    /// The authorization term.
    pub body: BTerm<Pk>,
}
