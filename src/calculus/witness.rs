// SPDX-License-Identifier: CC0-1.0

//! The witness: a keyed bundle of the data supplied to authorize an operation.
//!
//! Proof obligations are discharged by *lookup*, not by positional consumption of a stack, and
//! the bundle carries no branch-selector data. A branch is open iff its leaves find their witness
//! items and its state predicates hold.
//!
//! This Phase-1 representation models signatures as mere presence of a key (no cryptography yet);
//! real signature verification over the canonical operation encoding arrives in a later phase.
//! The shape — keyed by key / hash / oracle key — is the final shape.

use crate::prelude::*;
use crate::MiniscriptKey;

use super::value::HashValue;

/// The authorizing witness for an operation.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Witness<Pk: MiniscriptKey> {
    /// Keys that have signed the operation.
    pub signers: BTreeSet<Pk>,
    /// Hash preimages revealed by the witness.
    pub preimages: BTreeSet<HashValue>,
    /// Oracle keys that have supplied a (schema-satisfying) attestation.
    pub attestors: BTreeSet<Pk>,
}

impl<Pk: MiniscriptKey> Witness<Pk> {
    /// An empty witness.
    pub fn empty() -> Self {
        Witness { signers: BTreeSet::new(), preimages: BTreeSet::new(), attestors: BTreeSet::new() }
    }

    /// A witness signed by the given keys.
    pub fn signed_by(keys: impl IntoIterator<Item = Pk>) -> Self {
        Witness { signers: keys.into_iter().collect(), ..Witness::empty() }
    }

    /// Whether `key` has signed.
    pub fn has_signature(&self, key: &Pk) -> bool { self.signers.contains(key) }
}
