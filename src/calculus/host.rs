// SPDX-License-Identifier: CC0-1.0

//! The host interface: the operation under authorization and the ledger-state snapshot.
//!
//! These are the analog of miniscript's `Satisfier`, but they *read* the environment rather than
//! produce a witness. The evaluator is generic over them, so the L2 supplies real implementations
//! and tests supply mocks. Crucially, neither trait exposes the witness — value functions and
//! state predicates are constant in the witness by construction, which is the m-constancy
//! invariant the witness-monotonicity theorem depends on.

use crate::prelude::*;
use crate::MiniscriptKey;

use super::ast::BTerm;
use super::registry::Symbol;
use super::value::Value;

/// The operation currently being authorized.
pub trait Operation<Pk: MiniscriptKey> {
    /// The operation's type, as a symbol (`spend`, `insert`, ...).
    fn op_type(&self) -> Symbol;

    /// A named argument of the operation (`amount`, `destination`, ...), if present.
    fn arg(&self, name: &str) -> Option<Value<Pk>>;

    /// The ast path targeted by a modification operation, if this is one.
    fn path(&self) -> Option<Vec<usize>>;

    /// The subtree introduced by an `insert` or `replace`, if this is one.
    fn subtree(&self) -> Option<BTerm<Pk>>;
}

/// A snapshot of the deposit's ledger state at the time of authorization. All quantities are
/// modeled as bounded integers ([`i128`]) for uniformity with the value sublanguage.
pub trait LedgerState {
    /// Blocks since the deposit's last authorized operation.
    fn blocks_since_activity(&self) -> i128;

    /// Blocks since the deposit was opened.
    fn blocks_since_open(&self) -> i128;

    /// The deposit's current balance.
    fn balance(&self) -> i128;

    /// Cumulative value of `field` over the last `period` blocks. `field` is one of
    /// `amount_out`, `amount_in`, `transfer_count`.
    fn rolling_window(&self, field: &str, period: i128) -> i128;

    /// Lifetime spend authorized via the descriptor path `path`.
    fn cumulative_spent_via(&self, path: &[usize]) -> i128;

    /// The current block height (for `older`/`after` and signature expiry).
    fn current_height(&self) -> i128;
}
