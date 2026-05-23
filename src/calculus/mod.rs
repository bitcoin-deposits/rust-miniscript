// SPDX-License-Identifier: CC0-1.0

//! # dep-16: a monotone term calculus for ledger-based deposit authorization
//!
//! This module implements the authorization calculus in which a deposit's authorization
//! condition is a closed term, evaluated against an operation, a ledger-state snapshot, and a
//! witness, to produce accept or reject. It does **not** compile to Bitcoin Script; the
//! evaluator here is the only evaluator.
//!
//! The design and proofs are in `PAPER.md`; the implementation plan is in `PLAN.md`. The
//! calculus has three sorts — [`ast::BTerm`], [`ast::VTerm`], [`ast::Obligation`] — represented
//! as distinct Rust types so that the sort discipline is enforced by construction. The single
//! placement rule (proof obligations occur only in positive position) is checked by
//! [`admission`], and witness-monotonicity follows.
//!
//! This module is gated behind the `dep16` feature and is experimental.

#[cfg(test)]
mod tests;

#[cfg(all(test, feature = "std"))]
mod secp_tests;

pub mod admission;
pub mod ast;
pub mod capability;
pub mod encode;
pub mod eval;
pub mod fraud;
pub mod host;
pub mod limits;
pub mod modify;
pub mod parse;
pub mod registry;
pub mod schema;
#[cfg(feature = "std")]
pub mod secp;
pub mod signature;
pub mod snapshot;
pub mod value;
pub mod witness;

pub use self::admission::{admit, check_polarity, AdmissionError};
pub use self::ast::{BTerm, Descriptor, Obligation, VTerm};
pub use self::capability::{CapabilitySet, ObligationKind};
pub use self::encode::{
    decode_descriptor, decode_fraud_proof, decode_operation, decode_snapshot, decode_witness,
    descriptor_id, encode_descriptor, encode_fraud_proof, encode_snapshot, encode_witness,
    operation_preimage, operation_sighash, snapshot_id, tagged_hash, CanonicalKey, DecodeError,
};
pub use self::eval::{eval_b, evaluate, Env, EvalError};
pub use self::fraud::{replay, FraudProof, ReplayOutcome};
pub use self::host::{LedgerState, Operation, OperationData};
pub use self::limits::MAX_DEPTH;
pub use self::modify::{admit_modification, candidate, ModificationRejected, ModifyError};
pub use self::parse::{parse, ParseError};
pub use self::registry::{CmpOp, StatePred, Symbol, ValueFn};
pub use self::schema::Schema;
#[cfg(feature = "std")]
pub use self::secp::{EcdsaVerifier, SchnorrVerifier};
pub use self::signature::{Signature, Verifier};
pub use self::snapshot::Snapshot;
pub use self::value::{HashValue, Value};
pub use self::witness::Witness;
