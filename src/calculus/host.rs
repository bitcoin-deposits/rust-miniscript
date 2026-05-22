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
///
/// The components that a signature commits to — deposit id, type, arguments, nonce, expiry — are
/// exposed individually; the calculus builds the canonical signing preimage from them (via
/// [`encode::operation_preimage`](super::encode::operation_preimage)) so that no operation
/// implementation can diverge on the encoding.
pub trait Operation<Pk: MiniscriptKey> {
    /// The operation's type, as a symbol (`spend`, `insert`, ...).
    fn op_type(&self) -> Symbol;

    /// A named argument of the operation (`amount`, `destination`, ...), if present.
    fn arg(&self, name: &str) -> Option<Value<Pk>>;

    /// All named arguments of the operation. Used to build the canonical signing preimage; order
    /// is irrelevant (the encoder sorts by name).
    fn args(&self) -> Vec<(String, Value<Pk>)>;

    /// The ast path targeted by a modification operation, if this is one.
    fn path(&self) -> Option<Vec<usize>>;

    /// The subtree introduced by an `insert` or `replace`, if this is one.
    fn subtree(&self) -> Option<BTerm<Pk>>;

    /// The deposit's id: the 32-byte domain separator that makes signatures non-replayable across
    /// deposits.
    fn deposit_id(&self) -> [u8; 32];

    /// The operation's nonce (replay protection; enforced by the protocol, not the descriptor).
    fn nonce(&self) -> u64;

    /// The block height after which a signature over this operation is invalid (enforced by the
    /// protocol, not the descriptor).
    fn expiry(&self) -> u32;
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
