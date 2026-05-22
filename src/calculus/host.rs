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
/// The components a signature commits to — deposit id, type, arguments, nonce, expiry — are all
/// exposed, and the calculus builds the canonical signing preimage from them (via
/// [`encode::operation_preimage`](super::encode::operation_preimage)) so that no implementation
/// can diverge on the encoding. A modification operation's target and content are *named
/// arguments* (`path`, `subtree`), so they are committed to by the signature like any other
/// argument; [`path`](Operation::path) and [`subtree`](Operation::subtree) read them back.
pub trait Operation<Pk: MiniscriptKey> {
    /// The operation's type, as a symbol (`spend`, `insert`, ...).
    fn op_type(&self) -> Symbol;

    /// All named arguments of the operation. This is the single source of truth for the
    /// operation's content; order is irrelevant (the encoder sorts by name).
    fn args(&self) -> Vec<(String, Value<Pk>)>;

    /// The deposit's id: the 32-byte domain separator that makes signatures non-replayable across
    /// deposits.
    fn deposit_id(&self) -> [u8; 32];

    /// The operation's nonce (replay protection; enforced by the protocol, not the descriptor).
    fn nonce(&self) -> u64;

    /// The block height after which a signature over this operation is invalid (enforced by the
    /// protocol, not the descriptor).
    fn expiry(&self) -> u32;

    /// A named argument of the operation, if present.
    fn arg(&self, name: &str) -> Option<Value<Pk>> {
        self.args().into_iter().find(|(n, _)| n == name).map(|(_, v)| v)
    }

    /// The ast path targeted by a modification operation: the `path` argument, if present.
    fn path(&self) -> Option<Vec<usize>> {
        match self.arg("path") {
            Some(Value::Path(p)) => Some(p),
            _ => None,
        }
    }

    /// The subtree introduced by an `insert`/`replace`: the `subtree` argument, if present.
    fn subtree(&self) -> Option<BTerm<Pk>> {
        match self.arg("subtree") {
            Some(Value::Subtree(b)) => Some(*b),
            _ => None,
        }
    }
}

/// A concrete, transmittable operation: the canonical fields, nothing more. Implements
/// [`Operation`] and is what a fraud proof carries and what [`decode_operation`] produces.
///
/// [`decode_operation`]: super::encode::decode_operation
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct OperationData<Pk: MiniscriptKey> {
    /// The operation type.
    pub op_type: Symbol,
    /// Named arguments (sorted by name; a `BTreeMap` keeps them canonical).
    pub args: BTreeMap<String, Value<Pk>>,
    /// The deposit's 32-byte id.
    pub deposit_id: [u8; 32],
    /// Replay-protection nonce.
    pub nonce: u64,
    /// Expiry block height.
    pub expiry: u32,
}

impl<Pk: MiniscriptKey> Operation<Pk> for OperationData<Pk> {
    fn op_type(&self) -> Symbol { self.op_type.clone() }
    fn args(&self) -> Vec<(String, Value<Pk>)> {
        self.args.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }
    fn deposit_id(&self) -> [u8; 32] { self.deposit_id }
    fn nonce(&self) -> u64 { self.nonce }
    fn expiry(&self) -> u32 { self.expiry }
}

/// A snapshot of the deposit's ledger state at the time of authorization. All quantities are
/// modeled as bounded integers ([`i128`]) for uniformity with the value sublanguage.
pub trait LedgerState {
    /// Blocks since the deposit's last authorized operation.
    fn blocks_since_activity(&self) -> i128;

    /// Blocks since the deposit was opened.
    fn blocks_since_open(&self) -> i128;

    /// Blocks since the deposit's last incoming payment was accepted.
    fn blocks_since_received(&self) -> i128;

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
