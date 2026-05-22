// SPDX-License-Identifier: CC0-1.0

//! Signatures and the verification host.
//!
//! Signatures are opaque bytes; verification is delegated to a host-supplied [`Verifier`], exactly
//! as miniscript's interpreter delegates to a `verify_sig` closure. This keeps the calculus
//! generic over the key type — a real deployment plugs in secp256k1 over the canonical operation
//! encoding, while tests can use string keys with a mock scheme. A signature binds to the
//! operation's signing message, so a signature for one operation does not authorize another.

use crate::prelude::*;
use crate::MiniscriptKey;

use super::value::HashValue;

/// An opaque signature or attestation, as supplied in the witness.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Signature(pub Vec<u8>);

/// The verification host: answers whether a signature is valid and whether a key matches a hash.
///
/// `verify_signature` is the only cryptographic primitive the evaluator needs for `pk` /
/// `pk_any` / `pk_threshold`; `key_hashes_to` additionally supports `pk_h`, which commits to a key
/// by its hash and requires the witness to reveal the key.
pub trait Verifier<Pk: MiniscriptKey> {
    /// Whether `sig` is a valid signature by `key` over `message`.
    fn verify_signature(&self, key: &Pk, sig: &Signature, message: &[u8]) -> bool;

    /// Whether `key` hashes to `keyhash` (used by `pk_h`).
    fn key_hashes_to(&self, key: &Pk, keyhash: &HashValue) -> bool;
}
