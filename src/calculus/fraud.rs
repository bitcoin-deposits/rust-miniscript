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
use super::eval::{evaluate, EvalError};
use super::host::{LedgerState, Operation};
use super::signature::Verifier;
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
    Pk: MiniscriptKey,
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
