// SPDX-License-Identifier: CC0-1.0

//! Real-cryptography tests: actual secp256k1 keypairs and ECDSA signatures, verified through
//! [`EcdsaVerifier`](super::secp::EcdsaVerifier). The descriptors and evaluator are unchanged from
//! the mock-backed tests; only the key type and verifier differ.

use crate::prelude::*;

use bitcoin::secp256k1::{PublicKey as SecpPub, Secp256k1, SecretKey};
use bitcoin::PublicKey;

use super::ast::{BTerm, Descriptor, Obligation, VTerm};
use super::eval::evaluate;
use super::parse::parse;
use super::registry::Symbol;
use super::secp::EcdsaVerifier;
use super::signature::{Signature, Verifier};
use super::value::{HashValue, Value};
use super::witness::Witness;

type Pk = PublicKey;

/// A deterministic keypair from a single seed byte.
fn keypair(seed: u8) -> (SecretKey, PublicKey) {
    let ctx = Secp256k1::new();
    let sk = SecretKey::from_slice(&[seed; 32]).expect("valid secret key");
    let pk = PublicKey::new(SecpPub::from_secret_key(&ctx, &sk));
    (sk, pk)
}

/// A minimal operation over real keys.
struct Op {
    ty: &'static str,
    amount: i128,
}

impl super::host::Operation<Pk> for Op {
    fn op_type(&self) -> Symbol { Symbol::new(self.ty) }
    fn args(&self) -> Vec<(String, Value<Pk>)> {
        vec![("amount".to_string(), Value::Int(self.amount))]
    }
    fn deposit_id(&self) -> [u8; 32] { [0u8; 32] }
    fn nonce(&self) -> u64 { 0 }
    fn expiry(&self) -> u32 { u32::MAX }
}

struct NoLedger;
impl super::host::LedgerState for NoLedger {
    fn blocks_since_activity(&self) -> i128 { 0 }
    fn blocks_since_open(&self) -> i128 { 0 }
    fn blocks_since_received(&self) -> i128 { 0 }
    fn balance(&self) -> i128 { 0 }
    fn rolling_window(&self, _f: &str, _p: i128) -> i128 { 0 }
    fn cumulative_spent_via(&self, _p: &[usize]) -> i128 { 0 }
    fn current_height(&self) -> i128 { 0 }
}

#[test]
fn real_signature_authorizes_and_binds_to_the_operation() {
    let v = EcdsaVerifier::new();
    let (sk, pk) = keypair(0x11);
    let d = parse::<Pk>(&format!("prove(pk({}))", pk)).unwrap();

    let op = Op { ty: "spend", amount: 100 };
    let other = Op { ty: "spend", amount: 200 };

    // A real signature over this operation's message.
    let sig = v.sign(&sk, &super::encode::operation_preimage(&op));
    let w = Witness::empty().with_signature(pk, sig);

    // Authorizes the operation it signed...
    assert!(evaluate(&d, &op, &NoLedger, &w, &v).unwrap());
    // ...but not a different one (the digest, hence the signature, differs).
    assert!(!evaluate(&d, &other, &NoLedger, &w, &v).unwrap());
}

#[test]
fn signature_by_the_wrong_key_is_rejected() {
    let v = EcdsaVerifier::new();
    let (_sk_a, pk_a) = keypair(0x11);
    let (sk_b, _pk_b) = keypair(0x22);
    let d = parse::<Pk>(&format!("prove(pk({}))", pk_a)).unwrap();

    let op = Op { ty: "spend", amount: 100 };
    // A valid signature, but by the wrong key, placed under the expected key.
    let sig_b = v.sign(&sk_b, &super::encode::operation_preimage(&op));
    let w = Witness::empty().with_signature(pk_a, sig_b);
    assert!(!evaluate(&d, &op, &NoLedger, &w, &v).unwrap());
}

#[test]
fn garbage_signature_is_rejected() {
    let v = EcdsaVerifier::new();
    let (_sk, pk) = keypair(0x11);
    let d = parse::<Pk>(&format!("prove(pk({}))", pk)).unwrap();
    let op = Op { ty: "spend", amount: 100 };
    let w = Witness::empty().with_signature(pk, Signature(vec![0u8; 64]));
    assert!(!evaluate(&d, &op, &NoLedger, &w, &v).unwrap());
}

#[test]
fn real_threshold_signing() {
    let v = EcdsaVerifier::new();
    let (sk1, pk1) = keypair(0x01);
    let (sk2, pk2) = keypair(0x02);
    let (_sk3, pk3) = keypair(0x03);
    let d = parse::<Pk>(&format!("prove(pk_threshold(2, [{}, {}, {}]))", pk1, pk2, pk3)).unwrap();

    let op = Op { ty: "spend", amount: 100 };
    let msg = super::encode::operation_preimage(&op);

    // Two of three sign: authorized.
    let w2 = Witness::empty()
        .with_signature(pk1, v.sign(&sk1, &msg))
        .with_signature(pk2, v.sign(&sk2, &msg));
    assert!(evaluate(&d, &op, &NoLedger, &w2, &v).unwrap());

    // One of three: rejected.
    let w1 = Witness::empty().with_signature(pk1, v.sign(&sk1, &msg));
    assert!(!evaluate(&d, &op, &NoLedger, &w1, &v).unwrap());
}

#[test]
fn real_pk_h_matches_hash160_of_the_key() {
    let v = EcdsaVerifier::new();
    let (sk, pk) = keypair(0x11);
    let (sk_other, pk_other) = keypair(0x22);

    // pk_h commits to the hash160 of the key; the witness reveals the key (here, via its signature
    // entry) and the verifier matches by hash.
    use bitcoin::hashes::Hash as _;
    let keyhash = HashValue::Hash160(pk.pubkey_hash().to_byte_array());
    let body = BTerm::Prove(Obligation::PkH(VTerm::Lit(Value::Hash(keyhash))));
    let d = Descriptor::wsh(BTreeMap::new(), body);

    let op = Op { ty: "spend", amount: 100 };
    let msg = super::encode::operation_preimage(&op);

    // The matching key signs: authorized.
    let w = Witness::empty().with_signature(pk, v.sign(&sk, &msg));
    assert!(evaluate(&d, &op, &NoLedger, &w, &v).unwrap());

    // A different key signs: its hash does not match, so rejected.
    let w_other = Witness::empty().with_signature(pk_other, v.sign(&sk_other, &msg));
    assert!(!evaluate(&d, &op, &NoLedger, &w_other, &v).unwrap());
}

#[test]
fn descriptor_with_real_keys_round_trips_through_the_codec() {
    use super::encode::{decode_descriptor, encode_descriptor};
    let (_sk, pk) = keypair(0x11);
    let d = parse::<Pk>(&format!("prove(pk({}))", pk)).unwrap();
    let bytes = encode_descriptor(&d);
    // The 33-byte compressed key survives the encode/decode round-trip.
    let back = decode_descriptor::<Pk>(&bytes).expect("decode");
    assert_eq!(d, back);
}

mod schnorr {
    use super::*;
    use bitcoin::secp256k1::{Keypair, XOnlyPublicKey};
    use crate::calculus::secp::SchnorrVerifier;

    type XPk = XOnlyPublicKey;

    /// A deterministic x-only keypair from a seed byte.
    fn xkeypair(seed: u8) -> (SecretKey, XPk) {
        let ctx = Secp256k1::new();
        let sk = SecretKey::from_slice(&[seed; 32]).unwrap();
        let (xpk, _parity) = Keypair::from_secret_key(&ctx, &sk).x_only_public_key();
        (sk, xpk)
    }

    struct XOp;
    impl super::super::host::Operation<XPk> for XOp {
        fn op_type(&self) -> Symbol { Symbol::new("spend") }
        fn args(&self) -> Vec<(String, Value<XPk>)> {
            vec![("amount".to_string(), Value::Int(100))]
        }
        fn deposit_id(&self) -> [u8; 32] { [0u8; 32] }
        fn nonce(&self) -> u64 { 0 }
        fn expiry(&self) -> u32 { u32::MAX }
    }

    #[test]
    fn real_schnorr_authorizes_and_rejects() {
        let v = SchnorrVerifier::new();
        let (sk, xpk) = xkeypair(0x33);
        let d = parse::<XPk>(&format!("prove(pk({}))", xpk)).unwrap();
        let op = XOp;
        let msg = super::super::encode::operation_preimage(&op);

        // A real Schnorr signature authorizes.
        let w = Witness::empty().with_signature(xpk, v.sign(&sk, &msg));
        assert!(evaluate(&d, &op, &NoLedger, &w, &v).unwrap());

        // A signature by a different key, placed under the expected key, is rejected.
        let (sk_other, _) = xkeypair(0x44);
        let w_bad = Witness::empty().with_signature(xpk, v.sign(&sk_other, &msg));
        assert!(!evaluate(&d, &op, &NoLedger, &w_bad, &v).unwrap());
    }

    #[test]
    fn schnorr_descriptor_round_trips_through_the_codec() {
        use super::super::encode::{decode_descriptor, encode_descriptor};
        let (_sk, xpk) = xkeypair(0x33);
        let d = parse::<XPk>(&format!("prove(pk({}))", xpk)).unwrap();
        let back = decode_descriptor::<XPk>(&encode_descriptor(&d)).unwrap();
        assert_eq!(d, back);
    }
}

#[test]
fn high_s_ecdsa_signature_is_rejected() {
    // ECDSA admits two valid (r, s) pairs for the same (key, message): (r, s) and (r, N - s).
    // We reject high-s to close that malleability. Verify by flipping a valid low-s signature.
    let v = EcdsaVerifier::new();
    let (sk, pk) = keypair(0x11);
    let op = Op { ty: "spend", amount: 100 };
    let msg = super::encode::operation_preimage(&op);

    // A signature this verifier produces is low-s.
    let low = v.sign(&sk, &msg);
    assert!(v.verify_signature(&pk, &low, &msg));

    // Flip s to N - s (still a valid ECDSA signature mathematically) and confirm rejection.
    let mut bytes = [0u8; 64];
    bytes.copy_from_slice(&low.0);
    let s = bitcoin::secp256k1::SecretKey::from_slice(&bytes[32..64]).unwrap();
    let s_high = s.negate();
    bytes[32..64].copy_from_slice(&s_high.secret_bytes());
    let high = Signature(bytes.to_vec());

    assert!(!v.verify_signature(&pk, &high, &msg), "high-s signature must be rejected");
}
