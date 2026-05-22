// SPDX-License-Identifier: CC0-1.0

//! The witness: a keyed bundle of the data supplied to authorize an operation.
//!
//! Proof obligations are discharged by *lookup*, not by positional consumption of a stack, and the
//! bundle carries no branch-selector data. A branch is open iff its leaves find their witness items
//! and its state predicates hold.
//!
//! Signatures are keyed by public key, preimages by the hash they satisfy, attestations by oracle
//! key. A single signature by `K` therefore discharges every `pk(K)` in the descriptor at once,
//! since it commits to the operation rather than to any branch.

use crate::prelude::*;
use crate::MiniscriptKey;

use super::signature::Signature;
use super::value::HashValue;

/// The authorizing witness for an operation.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Witness<Pk: MiniscriptKey> {
    /// Signatures over the operation, keyed by signing key.
    pub signatures: BTreeMap<Pk, Signature>,
    /// Revealed preimages, keyed by the hash they satisfy.
    pub preimages: BTreeMap<HashValue, Vec<u8>>,
    /// Oracle keys that have supplied a schema-satisfying attestation.
    pub attestations: BTreeSet<Pk>,
}

impl<Pk: MiniscriptKey> Witness<Pk> {
    /// An empty witness.
    pub fn empty() -> Self {
        Witness {
            signatures: BTreeMap::new(),
            preimages: BTreeMap::new(),
            attestations: BTreeSet::new(),
        }
    }

    /// Add a signature by `key`.
    pub fn with_signature(mut self, key: Pk, sig: Signature) -> Self {
        self.signatures.insert(key, sig);
        self
    }

    /// Add a revealed preimage that satisfies `hash`.
    pub fn with_preimage(mut self, hash: HashValue, preimage: Vec<u8>) -> Self {
        self.preimages.insert(hash, preimage);
        self
    }

    /// Add an attestation by an oracle `key`.
    pub fn with_attestation(mut self, key: Pk) -> Self {
        self.attestations.insert(key);
        self
    }
}
