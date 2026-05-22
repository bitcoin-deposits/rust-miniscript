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

pub mod ast;
pub mod eval;
pub mod host;
pub mod parse;
pub mod registry;
pub mod schema;
pub mod value;
pub mod witness;

pub use self::ast::{BTerm, Descriptor, Obligation, VTerm};
pub use self::eval::{eval_b, Env, EvalError};
pub use self::host::{LedgerState, Operation};
pub use self::parse::{parse, ParseError};
pub use self::registry::{CmpOp, StatePred, Symbol, ValueFn};
pub use self::schema::Schema;
pub use self::value::{HashValue, Value};
pub use self::witness::Witness;
