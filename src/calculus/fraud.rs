// SPDX-License-Identifier: CC0-1.0

//! Fraud-proof replay.
//!
//! Every operation produces the same fraud-proof shape: the descriptor in effect, the operation,
//! the ledger snapshot, the witness, and the operator's claimed verdict. A verifier replays the
//! evaluation and compares. Because evaluation is a strict, total fold of fixed inputs with no
//! search, replay is deterministic, so a disagreement is an unambiguous operator fault. One shape
//! covers every operation type.

use crate::MiniscriptKey;

use super::ast::Descriptor;
use super::encode::{decode_fraud_proof, encode_fraud_proof, CanonicalKey, DecodeError};
use super::eval::{evaluate, EvalError};
use super::host::{LedgerState, Operation, OperationData};
use super::signature::Verifier;
use super::snapshot::Snapshot;
use super::witness::Witness;

/// The result of replaying an operation's authorization.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ReplayOutcome {
    /// The operator's verdict matches the replayed evaluation.
    Consistent,
    /// The operator's verdict disagrees with the replayed evaluation: a provable fault.
    OperatorFault {
        /// The verdict the replayed evaluation produced.
        computed: bool,
        /// The verdict the operator claimed.
        claimed: bool,
    },
}

/// Replay an operation's authorization and compare to the operator's claimed verdict.
pub fn replay<Pk, O, L, V>(
    descriptor: &Descriptor<Pk>,
    op: &O,
    state: &L,
    witness: &Witness<Pk>,
    verifier: &V,
    claimed: bool,
) -> Result<ReplayOutcome, EvalError>
where
    Pk: MiniscriptKey + CanonicalKey,
    O: Operation<Pk>,
    L: LedgerState,
    V: Verifier<Pk>,
{
    let computed = evaluate(descriptor, op, state, witness, verifier)?;
    Ok(if computed == claimed {
        ReplayOutcome::Consistent
    } else {
        ReplayOutcome::OperatorFault { computed, claimed }
    })
}

/// A self-contained fraud proof: everything needed to replay one operation's authorization. This
/// is the wire object — it encodes to canonical bytes and decodes with full canonical rejection,
/// and [`adjudicate`](FraudProof::adjudicate) replays it to a verdict.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FraudProof<Pk: MiniscriptKey> {
    /// The descriptor in effect at the time of the operation.
    pub descriptor: Descriptor<Pk>,
    /// The operation that was authorized.
    pub operation: OperationData<Pk>,
    /// The ledger-state snapshot the operation was evaluated against.
    pub snapshot: Snapshot,
    /// The witness supplied with the operation.
    pub witness: Witness<Pk>,
    /// The operator's claimed verdict.
    pub claimed: bool,
}

impl<Pk: MiniscriptKey + CanonicalKey> FraudProof<Pk> {
    /// The canonical byte encoding of this fraud proof.
    pub fn encode(&self) -> Vec<u8> { encode_fraud_proof(self) }

    /// Decode a fraud proof from canonical bytes, rejecting any non-canonical input.
    pub fn decode(buf: &[u8]) -> Result<Self, DecodeError> { decode_fraud_proof(buf) }

    /// Replay the bundled operation and compare to the claimed verdict.
    pub fn adjudicate<V: Verifier<Pk>>(&self, verifier: &V) -> Result<ReplayOutcome, EvalError> {
        replay(&self.descriptor, &self.operation, &self.snapshot, &self.witness, verifier, self.claimed)
    }
}
