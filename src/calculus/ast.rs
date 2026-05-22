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

impl<Pk: MiniscriptKey> BTerm<Pk> {
    /// The head constructor of this term, as a symbol (`and`, `or`, `pk`, ...). For `state` and
    /// `prove`, the predicate or obligation name; for `cmp`, `"cmp"`; for constants, `"true"` /
    /// `"false"`.
    pub fn shape(&self) -> &'static str {
        match self {
            BTerm::Const(true) => "true",
            BTerm::Const(false) => "false",
            BTerm::And(_) => "and",
            BTerm::Or(_) => "or",
            BTerm::Thresh(_, _) => "thresh",
            BTerm::Not(_) => "not",
            BTerm::If(_, _, _) => "if",
            BTerm::Match { .. } => "match",
            BTerm::Cmp(_, _, _) => "cmp",
            BTerm::State(p, _) => p.name(),
            BTerm::Prove(o) => o.shape(),
        }
    }

    /// The `B`-sorted children of this term, in path-index order. Value-sorted children (the
    /// `match` scrutinee, `cmp`/`state` arguments) are not addressable by path.
    pub fn children(&self) -> Vec<&BTerm<Pk>> {
        match self {
            BTerm::Const(_) | BTerm::Cmp(_, _, _) | BTerm::State(_, _) | BTerm::Prove(_) => vec![],
            BTerm::And(bs) | BTerm::Or(bs) | BTerm::Thresh(_, bs) => bs.iter().collect(),
            BTerm::Not(b) => vec![b],
            BTerm::If(c, t, e) => vec![c, t, e],
            BTerm::Match { arms, default, .. } => {
                let mut v: Vec<&BTerm<Pk>> = arms.iter().map(|(_, b)| b).collect();
                v.push(default);
                v
            }
        }
    }

    /// The subterm at `path`, navigating by child index. `[]` is this term.
    pub fn subterm_at(&self, path: &[usize]) -> Option<&BTerm<Pk>> {
        match path.split_first() {
            None => Some(self),
            Some((i, rest)) => self.children().get(*i).and_then(|c| c.subterm_at(rest)),
        }
    }

    /// The depth of this term's ast (a leaf has depth 1).
    pub fn depth(&self) -> usize {
        1 + self.children().iter().map(|c| c.depth()).max().unwrap_or(0)
    }
}

impl<Pk: MiniscriptKey> Obligation<Pk> {
    /// The head constructor name of this obligation.
    pub fn shape(&self) -> &'static str {
        match self {
            Obligation::Pk(_) => "pk",
            Obligation::PkH(_) => "pk_h",
            Obligation::PkAny(_) => "pk_any",
            Obligation::PkThreshold(_, _) => "pk_threshold",
            Obligation::Hashlock(_) => "hashlock",
            Obligation::Attest(_, _) => "attest",
        }
    }
}

/// A complete descriptor: a `with(...)` constant environment together with a body of sort `B`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Descriptor<Pk: MiniscriptKey> {
    /// Named constants, bound once at deposit-open.
    pub constants: BTreeMap<String, Value<Pk>>,
    /// The authorization term.
    pub body: BTerm<Pk>,
}
