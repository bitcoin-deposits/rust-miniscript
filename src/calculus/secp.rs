// SPDX-License-Identifier: CC0-1.0

//! A concrete ECDSA verification host over `bitcoin::PublicKey`.
//!
//! This is the production [`Verifier`](super::signature::Verifier) the calculus is generic over:
//! signatures are compact ECDSA over `sha256(message)`, where `message` is the operation's
//! canonical signing bytes, and `pk_h` matches a key by its hash160. The calculus needs no
//! changes to use it — the mock scheme in tests and this scheme are interchangeable behind the
//! trait.
//!
//! Requires the `std` feature (for the secp256k1 context).

use bitcoin::hashes::Hash as _;
use bitcoin::secp256k1::{ecdsa, All, Message, Secp256k1, SecretKey};
use bitcoin::PublicKey;

use super::encode::operation_sighash;
use super::signature::{Signature, Verifier};
use super::value::HashValue;

/// An ECDSA verifier (and signer) backed by a secp256k1 context.
pub struct EcdsaVerifier {
    secp: Secp256k1<All>,
}

impl Default for EcdsaVerifier {
    fn default() -> Self { Self::new() }
}

impl EcdsaVerifier {
    /// Construct a new verifier with its own secp256k1 context.
    pub fn new() -> Self { EcdsaVerifier { secp: Secp256k1::new() } }

    /// The 32-byte digest a signature commits to: the dep-17 operation sighash over the canonical
    /// operation preimage that `message` carries.
    fn digest(message: &[u8]) -> Message {
        Message::from_digest(operation_sighash(message))
    }

    /// Produce a signature by `sk` over `message`, in the compact encoding this verifier expects.
    /// Intended for constructing witnesses (in tooling and tests).
    pub fn sign(&self, sk: &SecretKey, message: &[u8]) -> Signature {
        let sig = self.secp.sign_ecdsa(&Self::digest(message), sk);
        Signature(sig.serialize_compact().to_vec())
    }
}

impl Verifier<PublicKey> for EcdsaVerifier {
    fn verify_signature(&self, key: &PublicKey, sig: &Signature, message: &[u8]) -> bool {
        let sig = match ecdsa::Signature::from_compact(&sig.0) {
            Ok(s) => s,
            Err(_) => return false,
        };
        self.secp.verify_ecdsa(&Self::digest(message), &sig, &key.inner).is_ok()
    }

    fn key_hashes_to(&self, key: &PublicKey, keyhash: &HashValue) -> bool {
        match keyhash {
            HashValue::Hash160(d) => key.pubkey_hash().to_byte_array() == *d,
            _ => false,
        }
    }
}
