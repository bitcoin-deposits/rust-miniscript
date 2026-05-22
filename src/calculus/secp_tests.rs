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
use super::signature::Signature;
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
    fn arg(&self, name: &str) -> Option<Value<Pk>> {
        match name {
            "amount" => Some(Value::Int(self.amount)),
            _ => None,
        }
    }
    fn path(&self) -> Option<Vec<usize>> { None }
    fn subtree(&self) -> Option<BTerm<Pk>> { None }
    fn signing_message(&self) -> Vec<u8> {
        format!("op={};amount={}", self.ty, self.amount).into_bytes()
    }
}

struct NoLedger;
impl super::host::LedgerState for NoLedger {
    fn blocks_since_activity(&self) -> i128 { 0 }
    fn blocks_since_open(&self) -> i128 { 0 }
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
    let sig = v.sign(&sk, &super::host::Operation::signing_message(&op));
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
    let sig_b = v.sign(&sk_b, &super::host::Operation::signing_message(&op));
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
    let msg = super::host::Operation::signing_message(&op);

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
    let d = Descriptor { constants: BTreeMap::new(), body };

    let op = Op { ty: "spend", amount: 100 };
    let msg = super::host::Operation::signing_message(&op);

    // The matching key signs: authorized.
    let w = Witness::empty().with_signature(pk, v.sign(&sk, &msg));
    assert!(evaluate(&d, &op, &NoLedger, &w, &v).unwrap());

    // A different key signs: its hash does not match, so rejected.
    let w_other = Witness::empty().with_signature(pk_other, v.sign(&sk_other, &msg));
    assert!(!evaluate(&d, &op, &NoLedger, &w_other, &v).unwrap());
}
