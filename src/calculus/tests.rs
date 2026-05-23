// SPDX-License-Identifier: CC0-1.0

//! Integration tests: parse a worked example, then evaluate it to verdicts against a mock host.

use crate::prelude::*;

use super::encode::{operation_preimage, CanonicalKey};
use super::eval::{eval_b, evaluate};
use super::host::{LedgerState, Operation};
use super::parse::parse;
use super::registry::Symbol;
use super::signature::{Signature, Verifier};
use super::value::{HashValue, Value};
use super::witness::Witness;

type Pk = String;

impl CanonicalKey for String {
    fn to_canonical_bytes(&self) -> Vec<u8> { self.as_bytes().to_vec() }
    fn from_canonical_bytes(bytes: &[u8]) -> Option<Self> { String::from_utf8(bytes.to_vec()).ok() }
}

/// The mock signature scheme used throughout the tests: a valid signature by `key` over `msg` is
/// the bytes `key | "|" | msg`. This binds a signature to both the key and the exact operation
/// message, so a signature for one operation does not verify against another.
fn mock_sig(key: &str, msg: &[u8]) -> Signature {
    let mut bytes = key.as_bytes().to_vec();
    bytes.push(b'|');
    bytes.extend_from_slice(msg);
    Signature(bytes)
}

/// A verifier for the mock scheme. `key_hashes_to` matches a key against the hash160 of its bytes.
struct MockVerifier;

impl Verifier<Pk> for MockVerifier {
    fn verify_signature(&self, key: &Pk, sig: &Signature, message: &[u8]) -> bool {
        *sig == mock_sig(key, message)
    }
    fn key_hashes_to(&self, key: &Pk, keyhash: &HashValue) -> bool {
        use bitcoin::hashes::{hash160, Hash as _};
        match keyhash {
            HashValue::Hash160(d) => hash160::Hash::hash(key.as_bytes()).to_byte_array() == *d,
            _ => false,
        }
    }
}

/// Build a witness signing `op` with each of `signers` under the mock scheme. The message signed
/// is the real dep-17 canonical operation preimage.
fn witness_signed_by(op: &MockOp, signers: &[&str]) -> Witness<Pk> {
    let msg = operation_preimage(op);
    let mut w = Witness::empty();
    for s in signers {
        w = w.with_signature(s.to_string(), mock_sig(s, &msg));
    }
    w
}

/// A mock operation: a type tag, named arguments (modification target/content live here too), and
/// a nonce.
struct MockOp {
    ty: &'static str,
    args: BTreeMap<String, Value<Pk>>,
    nonce: u64,
}

impl MockOp {
    fn spend(amount: i128, destination: &str) -> Self {
        let mut args = BTreeMap::new();
        args.insert("amount".to_string(), Value::Int(amount));
        args.insert("destination".to_string(), Value::Key(destination.to_string()));
        MockOp { ty: "spend", args, nonce: 0 }
    }
    fn of_type(ty: &'static str) -> Self {
        MockOp { ty, args: BTreeMap::new(), nonce: 0 }
    }
    fn replace(path: Vec<usize>, subtree: super::ast::BTerm<Pk>) -> Self {
        let mut args = BTreeMap::new();
        args.insert("path".to_string(), Value::Path(path));
        args.insert("subtree".to_string(), Value::Subtree(Box::new(subtree)));
        MockOp { ty: "replace", args, nonce: 0 }
    }
    fn with_nonce(mut self, nonce: u64) -> Self {
        self.nonce = nonce;
        self
    }
}

impl Operation<Pk> for MockOp {
    fn op_type(&self) -> Symbol { Symbol::new(self.ty) }
    fn args(&self) -> Vec<(String, Value<Pk>)> {
        self.args.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }
    fn deposit_id(&self) -> [u8; 32] { [0u8; 32] }
    fn nonce(&self) -> u64 { self.nonce }
    fn expiry(&self) -> u32 { u32::MAX }
}

/// A mock ledger snapshot.
struct MockLedger {
    balance: i128,
    since_activity: i128,
    since_open: i128,
    since_received: i128,
    rolling_out: i128,
    cumulative: i128,
    height: i128,
}

impl Default for MockLedger {
    fn default() -> Self {
        MockLedger {
            balance: 1000,
            since_activity: 0,
            since_open: 0,
            since_received: 0,
            rolling_out: 0,
            cumulative: 0,
            height: 0,
        }
    }
}

impl LedgerState for MockLedger {
    fn blocks_since_activity(&self) -> i128 { self.since_activity }
    fn blocks_since_open(&self) -> i128 { self.since_open }
    fn blocks_since_received(&self) -> i128 { self.since_received }
    fn balance(&self) -> i128 { self.balance }
    fn rolling_window(&self, field: &str, _period: i128) -> i128 {
        if field == "amount_out" {
            self.rolling_out
        } else {
            0
        }
    }
    fn cumulative_spent_via(&self, _path: &[usize]) -> i128 { self.cumulative }
    fn current_height(&self) -> i128 { self.height }
}

const ALLOWANCE: &str = "
    with(
      user = K1,
      delegate = K2,
      guardians = [K3, K4, K5],
      recovery_to = D1,
      in match(operation_type(),
        branch(spend,
          or(
            prove(pk(user)),
            and(
              prove(pk(delegate)),
              amount_at_most_pct(10),
              rolling_amount_below_pct(30, 4320)
            ),
            and(
              prove(pk_threshold(2, guardians)),
              blocks_since_activity_at_least(4320),
              destination_is(recovery_to)
            )
          )
        ),
        branch(insert, prove(pk(user))),
        branch(replace, prove(pk(user))),
        branch(delete, prove(pk(user))),
        branch(else, false)
      )
    )";

fn decide(src: &str, op: &MockOp, st: &MockLedger, signers: &[&str]) -> bool {
    let d = parse::<Pk>(src).expect("parse");
    let w = witness_signed_by(op, signers);
    evaluate(&d, op, st, &w, &MockVerifier).expect("eval")
}

#[test]
fn user_can_spend_anything() {
    let op = MockOp::spend(999, "anywhere");
    assert!(decide(ALLOWANCE, &op, &MockLedger::default(), &["K1"]));
}

#[test]
fn delegate_within_allowance_accepted() {
    // amount 100 == 10% of 1000; rolling 50 <= 30% of 1000 (300).
    let op = MockOp::spend(100, "anywhere");
    let st = MockLedger { rolling_out: 50, ..MockLedger::default() };
    assert!(decide(ALLOWANCE, &op, &st, &["K2"]));
}

#[test]
fn delegate_over_per_op_cap_rejected() {
    let op = MockOp::spend(200, "anywhere"); // 200 > 10% of 1000
    assert!(!decide(ALLOWANCE, &op, &MockLedger::default(), &["K2"]));
}

#[test]
fn delegate_over_rolling_cap_rejected() {
    let op = MockOp::spend(100, "anywhere");
    let st = MockLedger { rolling_out: 400, ..MockLedger::default() }; // 400 > 30% of 1000
    assert!(!decide(ALLOWANCE, &op, &st, &["K2"]));
}

#[test]
fn guardians_recover_after_inactivity() {
    let op = MockOp::spend(500, "D1");
    let st = MockLedger { since_activity: 5000, ..MockLedger::default() }; // > 4320
    assert!(decide(ALLOWANCE, &op, &st, &["K3", "K4"])); // 2-of-3
}

#[test]
fn guardians_blocked_before_inactivity_window() {
    let op = MockOp::spend(500, "D1");
    let st = MockLedger { since_activity: 100, ..MockLedger::default() }; // < 4320
    assert!(!decide(ALLOWANCE, &op, &st, &["K3", "K4"]));
}

#[test]
fn guardians_blocked_to_wrong_destination() {
    let op = MockOp::spend(500, "elsewhere");
    let st = MockLedger { since_activity: 5000, ..MockLedger::default() };
    assert!(!decide(ALLOWANCE, &op, &st, &["K3", "K4"]));
}

#[test]
fn one_guardian_is_not_enough() {
    let op = MockOp::spend(500, "D1");
    let st = MockLedger { since_activity: 5000, ..MockLedger::default() };
    assert!(!decide(ALLOWANCE, &op, &st, &["K3"])); // need 2-of-3
}

#[test]
fn user_can_modify() {
    let op = MockOp::of_type("insert");
    assert!(decide(ALLOWANCE, &op, &MockLedger::default(), &["K1"]));
}

#[test]
fn delegate_cannot_modify() {
    let op = MockOp::of_type("insert");
    assert!(!decide(ALLOWANCE, &op, &MockLedger::default(), &["K2"]));
}

#[test]
fn unknown_operation_type_denied_by_else() {
    let op = MockOp::of_type("accept");
    assert!(!decide(ALLOWANCE, &op, &MockLedger::default(), &["K1"]));
}

// ----------------------------------------------------------------------------------------------
// Phase 2: admission
// ----------------------------------------------------------------------------------------------

mod admission_tests {
    use super::*;
    use crate::calculus::admission::{admit, check_polarity, AdmissionError};
    use crate::calculus::ast::{BTerm, Descriptor, Obligation, VTerm};
    use crate::calculus::capability::CapabilitySet;
    use crate::calculus::registry::StatePred;

    fn pk(k: &str) -> BTerm<Pk> {
        BTerm::Prove(Obligation::Pk(VTerm::Lit(Value::Key(k.to_string()))))
    }
    fn always_true() -> BTerm<Pk> {
        BTerm::State(StatePred::BalanceAtLeast, vec![VTerm::Lit(Value::Int(0))])
    }

    #[test]
    fn rejects_proof_under_not() {
        assert_eq!(check_polarity(&BTerm::Not(Box::new(pk("A"))), true), Err(AdmissionError::NegativeProof));
    }

    #[test]
    fn rejects_proof_in_if_condition() {
        let t = BTerm::If(Box::new(pk("A")), Box::new(BTerm::Const(true)), Box::new(BTerm::Const(false)));
        assert_eq!(check_polarity(&t, true), Err(AdmissionError::NegativeProof));
    }

    #[test]
    fn rejects_proof_nested_under_not_in_or() {
        // or(pk(A), not(pk(B))) — the second arm is negative.
        let t = BTerm::Or(vec![pk("A"), BTerm::Not(Box::new(pk("B")))]);
        assert_eq!(check_polarity(&t, true), Err(AdmissionError::NegativeProof));
    }

    #[test]
    fn accepts_proofs_in_positive_positions() {
        // and(pk(A), or(pk(B), pk(C))), and proofs in if branches with an m-constant condition.
        let t = BTerm::And(vec![
            pk("A"),
            BTerm::Or(vec![pk("B"), pk("C")]),
            BTerm::If(Box::new(always_true()), Box::new(pk("D")), Box::new(pk("E"))),
        ]);
        assert_eq!(check_polarity(&t, true), Ok(()));
    }

    #[test]
    fn negation_of_state_is_fine() {
        // not(state(...)) is admissible — state predicates are m-constant.
        assert_eq!(check_polarity(&BTerm::Not(Box::new(always_true())), true), Ok(()));
    }

    #[test]
    fn capability_gates_state_predicates() {
        // A descriptor using amount_at_most_pct is admitted only if the operator declares it.
        let body: BTerm<Pk> = BTerm::State(StatePred::AmountAtMostPct, vec![VTerm::Lit(Value::Int(10))]);
        let d = Descriptor { constants: BTreeMap::new(), body };
        assert!(admit(&d, &CapabilitySet::everything()).is_ok());
        assert_eq!(
            admit(&d, &CapabilitySet::minimum()),
            Err(AdmissionError::UncapableStatePred(StatePred::AmountAtMostPct)),
        );
    }

    #[test]
    fn unresolved_constant_is_rejected() {
        // pk(missing) where `missing` is not bound by with(...).
        let body: BTerm<Pk> = BTerm::Prove(Obligation::Pk(VTerm::Var("missing".to_string())));
        let d = Descriptor { constants: BTreeMap::new(), body };
        assert_eq!(
            admit(&d, &CapabilitySet::everything()),
            Err(AdmissionError::UnresolvedVar("missing".to_string())),
        );
    }

    #[test]
    fn worked_allowance_example_is_admitted() {
        let d = parse::<Pk>(ALLOWANCE).unwrap();
        assert!(admit(&d, &CapabilitySet::everything()).is_ok());
    }
}

// ----------------------------------------------------------------------------------------------
// Phase 2: the witness-monotonicity property (PAPER.md Theorem 3.1)
//
// Generate adversarial terms (proof obligations placed freely, including under `not` and in `if`
// conditions), admit them, and assert that every admitted term is monotone in the witness:
// accept(m) ⟹ accept(m') whenever m ⊆ m'. A polarity-checker or evaluator bug that let a
// non-monotone term through admission would surface here as a counterexample.
// ----------------------------------------------------------------------------------------------

mod monotonicity {
    use super::*;
    use crate::calculus::admission::admit;
    use crate::calculus::ast::{BTerm, Descriptor, Obligation, VTerm};
    use crate::calculus::capability::CapabilitySet;
    use crate::calculus::registry::StatePred;

    const KEYS: [&str; 4] = ["A", "B", "C", "D"];

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            self.0 >> 33
        }
        fn below(&mut self, n: u64) -> u64 { self.next() % n }
    }

    fn leaf(rng: &mut Rng) -> BTerm<Pk> {
        match rng.below(4) {
            0 => BTerm::Prove(Obligation::Pk(VTerm::Lit(Value::Key(
                KEYS[rng.below(4) as usize].to_string(),
            )))),
            1 => BTerm::Const(true),
            2 => BTerm::Const(false),
            // An m-constant state leaf (balance >= 0 is always true under the mock ledger).
            _ => BTerm::State(StatePred::BalanceAtLeast, vec![VTerm::Lit(Value::Int(0))]),
        }
    }

    fn gen(d: u32, rng: &mut Rng) -> BTerm<Pk> {
        if d == 0 {
            return leaf(rng);
        }
        match rng.below(7) {
            0 => BTerm::And(gen_list(d, rng)),
            1 => BTerm::Or(gen_list(d, rng)),
            2 => BTerm::Thresh(rng.below(4) as usize, gen_list(d, rng)),
            3 => BTerm::Not(Box::new(gen(d - 1, rng))),
            4 => BTerm::If(
                Box::new(gen(d - 1, rng)),
                Box::new(gen(d - 1, rng)),
                Box::new(gen(d - 1, rng)),
            ),
            _ => leaf(rng),
        }
    }

    fn gen_list(d: u32, rng: &mut Rng) -> Vec<BTerm<Pk>> {
        let n = 2 + rng.below(2);
        (0..n).map(|_| gen(d - 1, rng)).collect()
    }

    fn accept(term: &BTerm<Pk>, mask: u8) -> bool {
        let op = MockOp::spend(1, "x");
        let st = MockLedger::default();
        let signers: Vec<&str> = (0..4).filter(|i| mask & (1 << i) != 0).map(|i| KEYS[i]).collect();
        let w = super::witness_signed_by(&op, &signers);
        let env = BTreeMap::new();
        eval_b(term, &env, term, &op, &st, &w, &super::MockVerifier).expect("generated terms never error")
    }

    #[test]
    fn admitted_terms_are_witness_monotone() {
        let caps = CapabilitySet::everything();
        let mut rng = Rng(0x9E3779B97F4A7C15);
        let mut admitted = 0u32;
        let mut rejected = 0u32;

        for _ in 0..500 {
            let body = gen(4, &mut rng);
            let d = Descriptor { constants: BTreeMap::new(), body };
            if admit(&d, &caps).is_err() {
                rejected += 1;
                continue;
            }
            admitted += 1;
            // For every pair m ⊆ m', accept(m) ⟹ accept(m').
            for m in 0u8..16 {
                if !accept(&d.body, m) {
                    continue;
                }
                for m2 in 0u8..16 {
                    if m & m2 == m {
                        assert!(
                            accept(&d.body, m2),
                            "monotonicity violated: accepts {:04b} but not superset {:04b}\nterm: {:?}",
                            m, m2, d.body,
                        );
                    }
                }
            }
        }

        // The test must actually exercise both paths to be meaningful.
        assert!(admitted > 50, "too few admitted terms ({}); test is near-vacuous", admitted);
        assert!(rejected > 0, "generator produced no negative-position proofs to reject");
    }
}

// ----------------------------------------------------------------------------------------------
// Phase 3: real signatures, hashlocks, pk_h
// ----------------------------------------------------------------------------------------------

mod proofs {
    use super::*;
    use crate::calculus::ast::{BTerm, Descriptor, Obligation, VTerm};
    use bitcoin::hashes::{hash160, sha256, Hash as _};

    #[test]
    fn signature_binds_to_the_operation() {
        let d = parse::<Pk>(
            "with(user = K1, in match(operation_type(), branch(spend, prove(pk(user))), branch(else, false)))",
        )
        .unwrap();
        let op_a = MockOp::spend(100, "alice");
        let op_b = MockOp::spend(999, "bob");
        let st = MockLedger::default();
        // The witness signs op_a's message.
        let w = witness_signed_by(&op_a, &["K1"]);

        // It authorizes the operation it was signed for...
        assert!(evaluate(&d, &op_a, &st, &w, &MockVerifier).unwrap());
        // ...but not a different operation, even with the same key present.
        assert!(!evaluate(&d, &op_b, &st, &w, &MockVerifier).unwrap());
    }

    #[test]
    fn hashlock_requires_a_matching_preimage() {
        let preimage = b"open sesame".to_vec();
        let digest = HashValue::Sha256(sha256::Hash::hash(&preimage).to_byte_array());
        let body: BTerm<Pk> =
            BTerm::Prove(Obligation::Hashlock(VTerm::Lit(Value::Hash(digest.clone()))));
        let d = Descriptor { constants: BTreeMap::new(), body };
        let op = MockOp::spend(1, "x");
        let st = MockLedger::default();

        // No preimage: rejected.
        let empty = Witness::empty();
        assert!(!evaluate(&d, &op, &st, &empty, &MockVerifier).unwrap());

        // Correct preimage revealed: accepted.
        let w = Witness::empty().with_preimage(digest.clone(), preimage);
        assert!(evaluate(&d, &op, &st, &w, &MockVerifier).unwrap());

        // Wrong preimage under the same hash key: rejected (re-hash check fails).
        let w_bad = Witness::empty().with_preimage(digest, b"wrong".to_vec());
        assert!(!evaluate(&d, &op, &st, &w_bad, &MockVerifier).unwrap());
    }

    #[test]
    fn pk_h_matches_a_revealed_key_by_hash() {
        let key = "K1";
        let keyhash = HashValue::Hash160(hash160::Hash::hash(key.as_bytes()).to_byte_array());
        let body: BTerm<Pk> =
            BTerm::Prove(Obligation::PkH(VTerm::Lit(Value::Hash(keyhash))));
        let d = Descriptor { constants: BTreeMap::new(), body };
        let op = MockOp::spend(1, "x");
        let st = MockLedger::default();

        // A signature by the key whose hash matches: accepted.
        let w = witness_signed_by(&op, &[key]);
        assert!(evaluate(&d, &op, &st, &w, &MockVerifier).unwrap());

        // A signature by a different key: rejected.
        let w_other = witness_signed_by(&op, &["K2"]);
        assert!(!evaluate(&d, &op, &st, &w_other, &MockVerifier).unwrap());
    }
}

// ----------------------------------------------------------------------------------------------
// Phase 4: ast inspection + modification + re-admission
// ----------------------------------------------------------------------------------------------

mod modification {
    use super::*;
    use crate::calculus::admission::AdmissionError;
    use crate::calculus::ast::{BTerm, Descriptor, Obligation, VTerm};
    use crate::calculus::capability::CapabilitySet;
    use crate::calculus::modify::{admit_modification, candidate, ModificationRejected};
    use crate::calculus::registry::{StatePred, ValueFn};

    const ROTATION: &str = "
        with(
          user = K1,
          guardians = [G1, G2, G3, G4],
          in match(operation_type(),
            branch(spend, prove(pk(user))),
            branch(replace,
              or(
                prove(pk(user)),
                and(
                  prove(pk_threshold(3, guardians)),
                  blocks_since_activity_at_least(8640),
                  cmp(=, operation_path(), path(0))
                )
              )
            ),
            branch(else, false)
          )
        )";

    fn pk(k: &str) -> BTerm<Pk> {
        BTerm::Prove(Obligation::Pk(VTerm::Lit(Value::Key(k.to_string()))))
    }

    #[test]
    fn guardian_rotation_authorizes_replace_at_the_user_clause() {
        let new_clause = pk("K9"); // the replacement subtree
        let op = MockOp::replace(vec![0], new_clause);
        let st = MockLedger { since_activity: 9000, ..MockLedger::default() }; // > 8640
        // 3-of-4 guardians, replacing the subtree at path [0], after inactivity: authorized.
        assert!(decide(ROTATION, &op, &st, &["G1", "G2", "G3"]));
    }

    #[test]
    fn guardian_rotation_blocked_at_a_different_path() {
        let op = MockOp::replace(vec![1], pk("K9")); // not the user clause
        let st = MockLedger { since_activity: 9000, ..MockLedger::default() };
        assert!(!decide(ROTATION, &op, &st, &["G1", "G2", "G3"]));
    }

    #[test]
    fn guardian_rotation_blocked_before_inactivity() {
        let op = MockOp::replace(vec![0], pk("K9"));
        let st = MockLedger { since_activity: 10, ..MockLedger::default() };
        assert!(!decide(ROTATION, &op, &st, &["G1", "G2", "G3"]));
    }

    // A self-modifying descriptor: the user may replace any subtree.
    fn user_can_replace() -> Descriptor<Pk> {
        let mut constants = BTreeMap::new();
        constants.insert("user".to_string(), Value::Key("K1".to_string()));
        let body = BTerm::Match {
            scrutinee: VTerm::Op(ValueFn::OperationType, vec![]),
            arms: vec![(
                crate::calculus::registry::Symbol::new("replace"),
                BTerm::Prove(Obligation::Pk(VTerm::Var("user".to_string()))),
            )],
            default: Box::new(BTerm::Const(false)),
        };
        Descriptor { constants, body }
    }

    #[test]
    fn candidate_replaces_the_targeted_subtree() {
        let d = user_can_replace();
        // Replace the replace-branch body (path [0]) with a new well-formed clause.
        let op = MockOp::replace(vec![0], pk("K2"));
        let cand = candidate(&d, &op).expect("candidate");
        // The targeted subterm is now pk(K2).
        assert_eq!(cand.body.subterm_at(&[0]), Some(&pk("K2")));
        // The new descriptor is admissible.
        assert!(admit_modification(&d, &op, &CapabilitySet::everything()).is_ok());
    }

    #[test]
    fn modification_introducing_a_negative_proof_is_rejected() {
        let d = user_can_replace();
        // Attempt to install `not(prove(pk(K2)))` — a negative-position proof obligation.
        let bad = BTerm::Not(Box::new(pk("K2")));
        let op = MockOp::replace(vec![0], bad);
        // The candidate is constructible, but admission rejects it: the modification fails and the
        // deposit keeps its current descriptor.
        match admit_modification(&d, &op, &CapabilitySet::everything()) {
            Err(ModificationRejected::Inadmissible(AdmissionError::NegativeProof)) => {}
            other => panic!("expected NegativeProof rejection, got {:?}", other),
        }
    }

    #[test]
    fn ast_inspection_reads_shape_and_subtree() {
        // root = and( prove(pk(K1)), cmp(=, ast_shape_at(path(0)), <symbol "pk">) )
        // child [0] is prove(pk(K1)), whose shape is "pk", so the comparison holds.
        let leaf = pk("K1");
        let shape_check = BTerm::Cmp(
            crate::calculus::registry::CmpOp::Eq,
            VTerm::Op(ValueFn::AstShapeAt, vec![VTerm::Op(ValueFn::Path, vec![VTerm::Lit(Value::Int(0))])]),
            VTerm::Lit(Value::Symbol(crate::calculus::registry::Symbol::new("pk"))),
        );
        let subtree_check = BTerm::State(
            StatePred::SubtreeAt,
            vec![
                VTerm::Lit(Value::Subtree(Box::new(leaf.clone()))),
                VTerm::Op(ValueFn::Path, vec![VTerm::Lit(Value::Int(0))]),
            ],
        );
        let body = BTerm::And(vec![leaf, shape_check, subtree_check]);
        let d = Descriptor { constants: BTreeMap::new(), body };
        let op = MockOp::spend(1, "x");
        let st = MockLedger::default();
        let w = witness_signed_by(&op, &["K1"]);
        // pk(K1) signed, shape at [0] is "pk", subtree at [0] equals the leaf: all hold.
        assert!(evaluate(&d, &op, &st, &w, &MockVerifier).unwrap());
    }
}

// ----------------------------------------------------------------------------------------------
// Phase 5: fraud replay + canonical encoding / determinism
// ----------------------------------------------------------------------------------------------

mod fraud_and_encoding {
    use super::*;
    use crate::calculus::encode::to_string;
    use crate::calculus::fraud::{replay, ReplayOutcome};

    #[test]
    fn replay_confirms_a_correct_verdict_and_catches_a_wrong_one() {
        let d = parse::<Pk>(ALLOWANCE).unwrap();
        let op = MockOp::spend(999, "anywhere");
        let st = MockLedger::default();
        let w = witness_signed_by(&op, &["K1"]); // user signs; true verdict is accept

        // The operator correctly claims accept.
        assert_eq!(
            replay(&d, &op, &st, &w, &MockVerifier, true).unwrap(),
            ReplayOutcome::Consistent,
        );
        // The operator wrongly claims reject: a provable fault.
        assert_eq!(
            replay(&d, &op, &st, &w, &MockVerifier, false).unwrap(),
            ReplayOutcome::OperatorFault { computed: true, claimed: false },
        );
    }

    #[test]
    fn replay_catches_an_unauthorized_acceptance() {
        let d = parse::<Pk>(ALLOWANCE).unwrap();
        let op = MockOp::spend(999, "anywhere");
        let st = MockLedger::default();
        let w = Witness::empty(); // nobody signed: true verdict is reject

        // The operator claims accept on an unsigned operation: fault.
        assert_eq!(
            replay(&d, &op, &st, &w, &MockVerifier, true).unwrap(),
            ReplayOutcome::OperatorFault { computed: false, claimed: true },
        );
    }

    #[test]
    fn canonical_encoding_round_trips_and_is_stable() {
        let d = parse::<Pk>(ALLOWANCE).unwrap();
        let printed = to_string(&d);
        // Re-parsing the canonical form yields an equal descriptor.
        let reparsed = parse::<Pk>(&printed).expect("reparse canonical form");
        assert_eq!(d, reparsed);
        // Printing is deterministic.
        assert_eq!(printed, to_string(&reparsed));
    }
}

// ----------------------------------------------------------------------------------------------
// dep-17 byte encodings
// ----------------------------------------------------------------------------------------------

mod encoding {
    use super::*;
    use crate::calculus::encode::{descriptor_id, encode_descriptor, operation_preimage, operation_sighash, tagged_hash};

    #[test]
    fn descriptor_id_is_stable_and_sensitive() {
        let d = parse::<Pk>(ALLOWANCE).unwrap();
        // Stable: the commitment depends only on the descriptor.
        assert_eq!(descriptor_id(&d), descriptor_id(&d));
        assert_eq!(encode_descriptor(&d), encode_descriptor(&d));
        // Sensitive: a structurally different descriptor commits differently.
        let other = parse::<Pk>("prove(pk(K1))").unwrap();
        assert_ne!(descriptor_id(&d), descriptor_id(&other));
    }

    #[test]
    fn signing_preimage_binds_nonce() {
        // Two operations identical but for the nonce produce different sighashes, so a signature
        // is not replayable across nonces.
        let op0 = MockOp::spend(100, "alice").with_nonce(7);
        let op1 = MockOp::spend(100, "alice").with_nonce(8);
        assert_ne!(operation_preimage(&op0), operation_preimage(&op1));
        assert_ne!(
            operation_sighash(&operation_preimage(&op0)),
            operation_sighash(&operation_preimage(&op1)),
        );
    }

    #[test]
    fn signing_preimage_binds_type_and_args() {
        let spend = MockOp::spend(100, "alice");
        let other_amount = MockOp::spend(101, "alice");
        let insert = MockOp::of_type("insert");
        assert_ne!(operation_preimage(&spend), operation_preimage(&other_amount));
        assert_ne!(operation_preimage(&spend), operation_preimage(&insert));
    }

    #[test]
    fn tagged_hash_is_domain_separated() {
        // The same message under different tags yields different digests.
        assert_ne!(tagged_hash("dep17/operation", b"x"), tagged_hash("dep17/descriptor", b"x"));
    }
}

mod codec {
    use super::*;
    use crate::calculus::encode::{decode_descriptor, encode_descriptor, DecodeError};

    fn roundtrips(src: &str) {
        let d = parse::<Pk>(src).unwrap();
        let bytes = encode_descriptor(&d);
        let back = decode_descriptor::<Pk>(&bytes).expect("decode");
        assert_eq!(d, back);
        // Encoding the decoded value reproduces the same bytes.
        assert_eq!(bytes, encode_descriptor(&back));
    }

    #[test]
    fn worked_examples_round_trip() {
        roundtrips(ALLOWANCE);
        roundtrips("prove(pk(K1))");
        roundtrips(
            "with(user = K1, guardians = [K3, K4, K5], in match(operation_type(), \
             branch(spend, prove(pk(user))), branch(replace, prove(pk_threshold(2, guardians))), \
             branch(else, false)))",
        );
    }

    #[test]
    fn trailing_bytes_are_rejected() {
        let d = parse::<Pk>("prove(pk(K1))").unwrap();
        let mut bytes = encode_descriptor(&d);
        bytes.push(0x00);
        assert_eq!(decode_descriptor::<Pk>(&bytes), Err(DecodeError::TrailingBytes));
    }

    #[test]
    fn truncated_input_is_rejected() {
        let d = parse::<Pk>("prove(pk(K1))").unwrap();
        let bytes = encode_descriptor(&d);
        let truncated = &bytes[..bytes.len() - 1];
        assert_eq!(decode_descriptor::<Pk>(truncated), Err(DecodeError::UnexpectedEof));
    }

    #[test]
    fn bad_version_is_rejected() {
        let d = parse::<Pk>("prove(pk(K1))").unwrap();
        let mut bytes = encode_descriptor(&d);
        bytes[0] = 0x02;
        assert_eq!(decode_descriptor::<Pk>(&bytes), Err(DecodeError::BadVersion(2)));
    }

    #[test]
    fn unknown_node_tag_is_rejected() {
        // version=1, 0 constants, then an out-of-range node tag (0xff).
        let bytes = [0x01u8, 0, 0, 0, 0, 0xff];
        match decode_descriptor::<Pk>(&bytes) {
            Err(DecodeError::UnknownTag("node", 0xff)) => {}
            other => panic!("expected unknown node tag, got {:?}", other),
        }
    }

    #[test]
    fn non_canonical_bool_is_rejected() {
        // version=1, 0 constants, Const node (0x00) with a bool byte of 2.
        let bytes = [0x01u8, 0, 0, 0, 0, 0x00, 0x02];
        assert_eq!(decode_descriptor::<Pk>(&bytes), Err(DecodeError::NonCanonicalBool(2)));
    }

    #[test]
    fn unsorted_constants_are_rejected() {
        // version=1, 2 constants in the wrong order ("b" before "a"), then body true.
        // each constant: u32 name-len, name, value(int tag 0x00 + 16 bytes).
        let mut bytes = vec![0x01u8];
        bytes.extend_from_slice(&2u32.to_be_bytes());
        for name in ["b", "a"] {
            bytes.extend_from_slice(&(name.len() as u32).to_be_bytes());
            bytes.extend_from_slice(name.as_bytes());
            bytes.push(0x00); // int value tag
            bytes.extend_from_slice(&0i128.to_be_bytes());
        }
        bytes.push(0x00); // body: Const
        bytes.push(0x01); // true
        assert_eq!(decode_descriptor::<Pk>(&bytes), Err(DecodeError::NonCanonicalOrder));
    }

    #[test]
    fn invalid_constant_name_is_rejected() {
        // A single constant named "Bad-Name" (uppercase + hyphen), value int 0, body true.
        let name = "Bad-Name";
        let mut bytes = vec![0x01u8];
        bytes.extend_from_slice(&1u32.to_be_bytes());
        bytes.extend_from_slice(&(name.len() as u32).to_be_bytes());
        bytes.extend_from_slice(name.as_bytes());
        bytes.push(0x00);
        bytes.extend_from_slice(&0i128.to_be_bytes());
        bytes.push(0x00);
        bytes.push(0x01);
        assert_eq!(decode_descriptor::<Pk>(&bytes), Err(DecodeError::InvalidName));
    }
}

mod hash_literals {
    use super::*;
    use crate::calculus::ast::{BTerm, Obligation};
    use crate::calculus::encode::to_string;
    use bitcoin::hashes::{sha256, Hash as _};

    #[test]
    fn hashlock_parses_evaluates_and_round_trips() {
        let preimage = b"open sesame".to_vec();
        let digest = sha256::Hash::hash(&preimage).to_byte_array();
        let hex: String = digest.iter().map(|b| format!("{:02x}", b)).collect();
        let src = format!("prove(hashlock(sha256:0x{}))", hex);

        // Parses to a hashlock obligation.
        let d = parse::<Pk>(&src).unwrap();
        assert!(matches!(d.body, BTerm::Prove(Obligation::Hashlock(_))));

        // Evaluates: revealing the preimage authorizes; absence does not.
        let op = MockOp::spend(1, "x");
        let st = MockLedger::default();
        let dv = HashValue::Sha256(digest);
        let w = Witness::empty().with_preimage(dv, preimage);
        assert!(evaluate(&d, &op, &st, &w, &MockVerifier).unwrap());
        assert!(!evaluate(&d, &op, &st, &Witness::empty(), &MockVerifier).unwrap());

        // Round-trips through the canonical source form.
        let printed = to_string(&d);
        assert_eq!(d, parse::<Pk>(&printed).unwrap());
    }

    #[test]
    fn bytes_literal_round_trips() {
        // A `with` constant bound to a raw byte string.
        let d = parse::<Pk>("with(tag = 0xdeadbeef, in cmp(=, tag, tag))").unwrap();
        assert_eq!(d.constants.get("tag"), Some(&Value::Bytes(vec![0xde, 0xad, 0xbe, 0xef])));
        assert_eq!(d, parse::<Pk>(&to_string(&d)).unwrap());
    }

    #[test]
    fn wrong_digest_length_is_rejected() {
        assert!(parse::<Pk>("prove(hashlock(sha256:0xdead))").is_err());
    }
}

mod snapshot_codec {
    use super::*;
    use crate::calculus::encode::{decode_snapshot, encode_snapshot, snapshot_id};
    use crate::calculus::snapshot::Snapshot;

    fn sample() -> Snapshot {
        let mut rolling = BTreeMap::new();
        rolling.insert(("amount_out".to_string(), 4320u32), 250i128);
        rolling.insert(("amount_in".to_string(), 4320u32), 90i128);
        let mut cumulative_spent = BTreeMap::new();
        cumulative_spent.insert(vec![0usize], 1000i128);
        cumulative_spent.insert(vec![1usize, 2usize], 50i128);
        Snapshot {
            balance: 1_000_000,
            blocks_since_activity: 12,
            blocks_since_open: 9000,
            blocks_since_received: 300,
            height: 850_000,
            rolling,
            cumulative_spent,
        }
    }

    #[test]
    fn snapshot_round_trips_and_commits_stably() {
        let s = sample();
        let bytes = encode_snapshot(&s);
        assert_eq!(decode_snapshot(&bytes).unwrap(), s);
        assert_eq!(snapshot_id(&s), snapshot_id(&s));
        assert_ne!(snapshot_id(&s), snapshot_id(&Snapshot::default()));
    }

    #[test]
    fn snapshot_drives_real_evaluation() {
        // The allowance descriptor evaluated against a concrete Snapshot rather than the mock.
        let d = parse::<Pk>(ALLOWANCE).unwrap();
        let mut s = sample();
        s.balance = 1000;
        s.blocks_since_activity = 5000; // > 4320
        // Delegate path: amount 100 = 10% of 1000, rolling amount_out below 30% (300).
        s.rolling.clear();
        s.rolling.insert(("amount_out".to_string(), 4320), 50);
        let op = MockOp::spend(100, "anywhere");
        let w = witness_signed_by(&op, &["K2"]);
        assert!(evaluate(&d, &op, &s, &w, &MockVerifier).unwrap());
    }

    #[test]
    fn unsorted_rolling_windows_are_rejected() {
        // version, balance(0), 3x u32 zero, then 2 rolling entries out of (field_id,period) order.
        let mut bytes = vec![0x01u8];
        bytes.extend_from_slice(&0i128.to_be_bytes());
        bytes.extend_from_slice(&0u32.to_be_bytes()); // since_activity
        bytes.extend_from_slice(&0u32.to_be_bytes()); // since_open
        bytes.extend_from_slice(&0u32.to_be_bytes()); // since_received
        bytes.extend_from_slice(&0u32.to_be_bytes()); // height
        bytes.extend_from_slice(&2u32.to_be_bytes()); // 2 rolling entries
        // entry (field_id=1, period=0) then (field_id=0, period=0): decreasing -> rejected.
        for field_id in [1u8, 0u8] {
            bytes.push(field_id);
            bytes.extend_from_slice(&0u32.to_be_bytes());
            bytes.extend_from_slice(&0i128.to_be_bytes());
        }
        bytes.extend_from_slice(&0u32.to_be_bytes()); // 0 cumulative entries
        assert_eq!(
            decode_snapshot(&bytes),
            Err(crate::calculus::encode::DecodeError::NonCanonicalOrder),
        );
    }
}

mod operation_codec {
    use super::*;
    use crate::calculus::ast::BTerm;
    use crate::calculus::encode::{decode_operation, operation_preimage, operation_sighash};
    use crate::calculus::host::OperationData;

    #[test]
    fn modification_signature_binds_path_and_subtree() {
        // Two replace operations differing only in the target path must not share a sighash, so a
        // signature authorizing one does not authorize the other.
        let a = MockOp::replace(vec![0], BTerm::Const(true));
        let b = MockOp::replace(vec![5], BTerm::Const(true));
        assert_ne!(operation_preimage(&a), operation_preimage(&b));
        assert_ne!(
            operation_sighash(&operation_preimage(&a)),
            operation_sighash(&operation_preimage(&b)),
        );

        // And differing only in the subtree content.
        let c = MockOp::replace(vec![0], BTerm::Const(false));
        assert_ne!(operation_preimage(&a), operation_preimage(&c));
    }

    #[test]
    fn operation_round_trips_through_the_codec() {
        let op = MockOp::spend(1234, "alice").with_nonce(42);
        let bytes = operation_preimage(&op);
        let decoded: OperationData<Pk> = decode_operation::<Pk>(&bytes).expect("decode");
        // Re-encoding the decoded operation reproduces the same canonical bytes.
        assert_eq!(operation_preimage(&decoded), bytes);
        // And the decoded fields match.
        assert_eq!(decoded.op_type.as_str(), "spend");
        assert_eq!(decoded.nonce, 42);
        assert_eq!(decoded.arg("amount"), Some(Value::Int(1234)));
    }

    #[test]
    fn a_decoded_modification_recovers_its_path_and_subtree() {
        let op = MockOp::replace(vec![1, 2], BTerm::Const(false));
        let decoded = decode_operation::<Pk>(&operation_preimage(&op)).unwrap();
        assert_eq!(decoded.path(), Some(vec![1, 2]));
        assert_eq!(decoded.subtree(), Some(BTerm::Const(false)));
    }
}

mod fraud_bundle {
    use super::*;
    use crate::calculus::fraud::{FraudProof, ReplayOutcome};
    use crate::calculus::host::OperationData;
    use crate::calculus::snapshot::Snapshot;

    fn user_spend() -> OperationData<Pk> {
        let mut args = BTreeMap::new();
        args.insert("amount".to_string(), Value::Int(100));
        args.insert("destination".to_string(), Value::Key("anywhere".to_string()));
        OperationData {
            op_type: Symbol::new("spend"),
            args,
            deposit_id: [7u8; 32],
            nonce: 1,
            expiry: 900_000,
        }
    }

    fn proof(claimed: bool) -> FraudProof<Pk> {
        let descriptor = parse::<Pk>(ALLOWANCE).unwrap();
        let operation = user_spend();
        let snapshot = Snapshot { balance: 1000, ..Snapshot::default() };
        // The user (K1) signs the operation; the true verdict is accept.
        let msg = operation_preimage(&operation);
        let witness = Witness::empty().with_signature("K1".to_string(), mock_sig("K1", &msg));
        FraudProof { descriptor, operation, snapshot, witness, claimed }
    }

    #[test]
    fn bundle_round_trips() {
        let fp = proof(true);
        let bytes = fp.encode();
        let back = FraudProof::<Pk>::decode(&bytes).expect("decode");
        assert_eq!(fp, back);
        assert_eq!(bytes, back.encode());
    }

    #[test]
    fn adjudicate_confirms_a_correct_verdict() {
        let fp = proof(true); // operator correctly claims accept
        assert_eq!(fp.adjudicate(&MockVerifier).unwrap(), ReplayOutcome::Consistent);
    }

    #[test]
    fn adjudicate_catches_a_false_claim() {
        let fp = proof(false); // operator wrongly claims reject on a validly-signed op
        assert_eq!(
            fp.adjudicate(&MockVerifier).unwrap(),
            ReplayOutcome::OperatorFault { computed: true, claimed: false },
        );
    }

    #[test]
    fn decode_through_then_adjudicate() {
        // The full verifier path: receive bytes, decode, adjudicate.
        let bytes = proof(true).encode();
        let fp = FraudProof::<Pk>::decode(&bytes).unwrap();
        assert_eq!(fp.adjudicate(&MockVerifier).unwrap(), ReplayOutcome::Consistent);
    }

    #[test]
    fn trailing_bytes_in_bundle_are_rejected() {
        let mut bytes = proof(true).encode();
        bytes.push(0x00);
        assert!(FraudProof::<Pk>::decode(&bytes).is_err());
    }
}

// ----------------------------------------------------------------------------------------------
// Wallet templates: worked descriptors for common policies.
// ----------------------------------------------------------------------------------------------

mod templates {
    use super::*;
    use crate::calculus::admission::admit;
    use crate::calculus::capability::CapabilitySet;
    use crate::calculus::modify::admit_modification;

    // ----- spending rate limit -----------------------------------------------------------------
    // A cold key spends without limit; a hot key spends only up to a per-operation cap and a
    // rolling weekly cap (1008 blocks). The rolling cap reads `amount_out` over the window.
    const RATE_LIMIT: &str = "
        with(cold = K1, hot = K2, in match(operation_type(),
          branch(spend, or(
            prove(pk(cold)),
            and(
              prove(pk(hot)),
              amount_at_most(100000),
              rolling_amount_below(500000, 1008)
            )
          )),
          branch(else, false)
        ))";

    #[test]
    fn rate_limit_admits() {
        assert!(admit(&parse::<Pk>(RATE_LIMIT).unwrap(), &CapabilitySet::everything()).is_ok());
    }

    #[test]
    fn rate_limit_behaves() {
        // Cold key: any amount, regardless of rolling usage.
        let big = MockOp::spend(1_000_000, "x");
        assert!(decide(RATE_LIMIT, &big, &MockLedger::default(), &["K1"]));

        // Hot key within both caps.
        let ok = MockOp::spend(50_000, "x");
        let st = MockLedger { rolling_out: 200_000, ..MockLedger::default() };
        assert!(decide(RATE_LIMIT, &ok, &st, &["K2"]));

        // Hot key over the per-operation cap.
        let over = MockOp::spend(150_000, "x");
        assert!(!decide(RATE_LIMIT, &over, &MockLedger::default(), &["K2"]));

        // Hot key within the per-op cap but over the rolling cap.
        let st_hot = MockLedger { rolling_out: 600_000, ..MockLedger::default() };
        assert!(!decide(RATE_LIMIT, &ok, &st_hot, &["K2"]));
    }

    // ----- inheritance -------------------------------------------------------------------------
    // The owner spends anytime; the heir can spend only after a long period of inactivity
    // (52560 blocks ~ 1 year), which resets on every authorized operation.
    const INHERITANCE: &str = "
        with(owner = K1, heir = K2, in match(operation_type(),
          branch(spend, or(
            prove(pk(owner)),
            and(prove(pk(heir)), blocks_since_activity_at_least(52560))
          )),
          branch(else, false)
        ))";

    #[test]
    fn inheritance_behaves() {
        let op = MockOp::spend(100, "x");
        // Owner spends regardless of activity.
        assert!(decide(INHERITANCE, &op, &MockLedger::default(), &["K1"]));
        // Heir blocked while the owner is recently active.
        let recent = MockLedger { since_activity: 1000, ..MockLedger::default() };
        assert!(!decide(INHERITANCE, &op, &recent, &["K2"]));
        // Heir spends after the inactivity window.
        let stale = MockLedger { since_activity: 60_000, ..MockLedger::default() };
        assert!(decide(INHERITANCE, &op, &stale, &["K2"]));
    }

    // ----- social recovery ---------------------------------------------------------------------
    // The owner spends and modifies freely. A 2-of-3 guardian quorum may, after 30 days of
    // inactivity, replace the owner's spend clause (the subterm at path [0]) — installing a new
    // key. Authority can expand here (a guardian quorum restores access), which capability
    // narrowing cannot express.
    const SOCIAL_RECOVERY: &str = "
        with(owner = K1, guardians = [G1, G2, G3], in match(operation_type(),
          branch(spend, prove(pk(owner))),
          branch(replace, or(
            prove(pk(owner)),
            and(
              prove(pk_threshold(2, guardians)),
              blocks_since_activity_at_least(4320),
              cmp(=, operation_path(), path(0))
            )
          )),
          branch(else, false)
        ))";

    fn clause(src: &str) -> super::super::ast::BTerm<Pk> { parse::<Pk>(src).unwrap().body }

    #[test]
    fn social_recovery_authorizes_and_applies() {
        let new_owner = clause("prove(pk(K9))");
        let op = MockOp::replace(vec![0], new_owner.clone());
        let stale = MockLedger { since_activity: 5000, ..MockLedger::default() };

        // Quorum is authorized to replace the owner clause after inactivity.
        assert!(decide(SOCIAL_RECOVERY, &op, &stale, &["G1", "G2"]));
        // Owner can replace anytime.
        assert!(decide(SOCIAL_RECOVERY, &op, &MockLedger::default(), &["K1"]));
        // One guardian, or before the window, is not enough.
        assert!(!decide(SOCIAL_RECOVERY, &op, &stale, &["G1"]));
        let fresh = MockLedger { since_activity: 10, ..MockLedger::default() };
        assert!(!decide(SOCIAL_RECOVERY, &op, &fresh, &["G1", "G2"]));

        // The modification produces a well-formed descriptor with the owner clause replaced.
        let d = parse::<Pk>(SOCIAL_RECOVERY).unwrap();
        let updated = admit_modification(&d, &op, &CapabilitySet::everything()).expect("admitted");
        assert_eq!(updated.body.subterm_at(&[0]), Some(&new_owner));
    }

    // ----- linear vesting ----------------------------------------------------------------------
    // The beneficiary may withdraw only up to the linearly-vested fraction of an allocation:
    // vested = allocation * min(elapsed, vesting_blocks) / vesting_blocks, and the total ever
    // withdrawn (cumulative spend on this path, plus this operation's amount) must stay within it.
    // This is the arithmetic + cumulative-spend path: a real release schedule, not just a cliff.
    const VESTING: &str = "
        with(beneficiary = K1, allocation = 1000000, vesting_blocks = 52560,
          in match(operation_type(),
            branch(spend, and(
              prove(pk(beneficiary)),
              cmp(<=,
                add(cumulative_spent_via(path(0)), operation_arg(amount)),
                div(mul(allocation, min(blocks_since_open(), vesting_blocks)), vesting_blocks)
              )
            )),
            branch(else, false)
          ))";

    #[test]
    fn linear_vesting_releases_over_time() {
        // Halfway through the schedule: 500_000 of 1_000_000 is vested.
        let half = MockLedger { since_open: 26_280, ..MockLedger::default() };

        // Nothing withdrawn yet: a draw within the vested half is allowed...
        let ok = MockOp::spend(400_000, "x");
        assert!(decide(VESTING, &ok, &half, &["K1"]));
        // ...but over the vested amount is not.
        let over = MockOp::spend(600_000, "x");
        assert!(!decide(VESTING, &over, &half, &["K1"]));

        // With most already withdrawn, only the remaining vested slice is available.
        let mostly_drawn = MockLedger { since_open: 26_280, cumulative: 450_000, ..MockLedger::default() };
        assert!(decide(VESTING, &MockOp::spend(40_000, "x"), &mostly_drawn, &["K1"]));   // 490k <= 500k
        assert!(!decide(VESTING, &MockOp::spend(100_000, "x"), &mostly_drawn, &["K1"])); // 550k > 500k

        // After the schedule completes, the whole allocation is available.
        let done = MockLedger { since_open: 60_000, ..MockLedger::default() };
        assert!(decide(VESTING, &MockOp::spend(1_000_000, "x"), &done, &["K1"]));

        // Not the beneficiary: rejected regardless of vesting.
        assert!(!decide(VESTING, &ok, &done, &["K2"]));
    }

    // ----- Liana (decaying multisig) -----------------------------------------------------------
    // The primary path is a 2-of-2; a recovery key becomes spendable only after a span of
    // inactivity. This is the Liana wallet shape, written with the idiomatic relative timelock
    // `older` — which in the ledger model gates on blocks-since-activity, so the recovery timer
    // *resets on every spend*, exactly as Bitcoin CSV does.
    const LIANA: &str = "
        with(primary_a = K1, primary_b = K2, recovery = K3, in match(operation_type(),
          branch(spend, or(
            and(prove(pk(primary_a)), prove(pk(primary_b))),
            and(prove(pk(recovery)), older(65535))
          )),
          branch(else, false)
        ))";

    #[test]
    fn liana_behaves() {
        let op = MockOp::spend(100, "x");
        // 2-of-2 primary spends anytime.
        assert!(decide(LIANA, &op, &MockLedger::default(), &["K1", "K2"]));
        // A single primary key is insufficient.
        assert!(!decide(LIANA, &op, &MockLedger::default(), &["K1"]));
        // Recovery is blocked while the wallet has been active recently.
        let active = MockLedger { since_activity: 1000, ..MockLedger::default() };
        assert!(!decide(LIANA, &op, &active, &["K3"]));
        // Recovery spends after the inactivity window.
        let stale = MockLedger { since_activity: 70_000, ..MockLedger::default() };
        assert!(decide(LIANA, &op, &stale, &["K3"]));
        // The timer keys on activity, not coin age: an old deposit that was spent recently still
        // blocks recovery. This is the decaying-multisig point.
        let reset = MockLedger { since_activity: 5, since_open: 70_000, ..MockLedger::default() };
        assert!(!decide(LIANA, &op, &reset, &["K3"]));
    }
}

mod ledger_primitives {
    use super::*;

    // A vesting cliff: the beneficiary may spend only after a fixed span since the deposit opened,
    // and — unlike `older` — this does NOT reset when the owner spends in the meantime.
    const VESTING: &str = "
        with(owner = K1, beneficiary = K2, in match(operation_type(),
          branch(spend, or(
            prove(pk(owner)),
            and(prove(pk(beneficiary)), blocks_since_open_at_least(26280))
          )),
          branch(else, false)
        ))";

    #[test]
    fn since_open_is_a_non_resetting_cliff() {
        let op = MockOp::spend(100, "x");
        // Before the cliff: beneficiary blocked even though there's been no recent activity.
        let early = MockLedger { since_open: 1000, since_activity: 99_999, ..MockLedger::default() };
        assert!(!decide(VESTING, &op, &early, &["K2"]));
        // After the cliff: beneficiary may spend, even if the owner just spent (since_activity low)
        // — the open-timer does not reset.
        let vested = MockLedger { since_open: 30_000, since_activity: 1, ..MockLedger::default() };
        assert!(decide(VESTING, &op, &vested, &["K2"]));
    }

    // A dead-man's-switch keyed on incoming payments: a backup key activates if no payment has
    // been received for a long time, independent of whether the owner has been spending.
    const NO_RECEIPT: &str = "
        with(owner = K1, backup = K2, in match(operation_type(),
          branch(spend, or(
            prove(pk(owner)),
            and(prove(pk(backup)), blocks_since_received_at_least(52560))
          )),
          branch(else, false)
        ))";

    #[test]
    fn since_received_gates_on_incoming_payments() {
        let op = MockOp::spend(100, "x");
        // A payment arrived recently: backup blocked.
        let recent = MockLedger { since_received: 100, ..MockLedger::default() };
        assert!(!decide(NO_RECEIPT, &op, &recent, &["K2"]));
        // No payment for a long time: backup activates, regardless of spend activity.
        let dry = MockLedger { since_received: 60_000, since_activity: 5, ..MockLedger::default() };
        assert!(decide(NO_RECEIPT, &op, &dry, &["K2"]));
    }

    #[test]
    fn new_primitives_admit_and_round_trip() {
        use crate::calculus::admission::admit;
        use crate::calculus::capability::CapabilitySet;
        use crate::calculus::encode::{decode_descriptor, encode_descriptor};
        for src in [VESTING, NO_RECEIPT] {
            let d = parse::<Pk>(src).unwrap();
            assert!(admit(&d, &CapabilitySet::everything()).is_ok());
            assert_eq!(d, decode_descriptor::<Pk>(&encode_descriptor(&d)).unwrap());
        }
    }
}

mod hardening {
    use super::*;
    use crate::calculus::admission::{admit, AdmissionError};
    use crate::calculus::ast::{BTerm, Descriptor};
    use crate::calculus::capability::CapabilitySet;
    use crate::calculus::encode::{decode_descriptor, DecodeError};
    use crate::calculus::limits::MAX_DEPTH;
    use crate::calculus::modify::{replace_at, ModifyError};

    fn nest_not(n: usize) -> BTerm<Pk> {
        let mut t: BTerm<Pk> = BTerm::Const(false);
        for _ in 0..n {
            t = BTerm::Not(Box::new(t));
        }
        t
    }

    #[test]
    fn parser_rejects_overdeep_nesting() {
        // A source string of `not(not(... not(false) ...))` past the depth limit.
        let mut src = String::new();
        for _ in 0..(MAX_DEPTH + 50) {
            src.push_str("not(");
        }
        src.push_str("false");
        for _ in 0..(MAX_DEPTH + 50) {
            src.push(')');
        }
        let r = parse::<Pk>(&src);
        assert!(r.is_err(), "expected parse to reject over-deep nesting");
        let msg = format!("{}", r.unwrap_err());
        assert!(msg.contains("nesting too deep"), "unexpected error: {}", msg);
    }

    #[test]
    fn decoder_rejects_overdeep_nesting() {
        // Bytes: version + 0 constants + (Not tag) * N + Const(false).
        let mut bytes = vec![0x01u8, 0, 0, 0, 0]; // version + 0 constants
        for _ in 0..(MAX_DEPTH + 50) {
            bytes.push(0x04); // BTerm::Not tag
        }
        bytes.push(0x00); // BTerm::Const tag
        bytes.push(0x00); // false
        assert_eq!(decode_descriptor::<Pk>(&bytes), Err(DecodeError::TooDeep));
    }

    #[test]
    fn decoder_rejects_oversized_list_count() {
        // version + constants count = u32::MAX, with no following bytes.
        let mut bytes = vec![0x01u8];
        bytes.extend_from_slice(&u32::MAX.to_be_bytes());
        assert_eq!(decode_descriptor::<Pk>(&bytes), Err(DecodeError::OversizedList));
    }

    #[test]
    fn modify_rejects_overdeep_path() {
        let body: BTerm<Pk> = BTerm::Const(true);
        let path: Vec<usize> = (0..(MAX_DEPTH + 1)).collect();
        assert_eq!(replace_at(&body, &path, BTerm::Const(false)), Err(ModifyError::PathTooDeep));
    }

    #[test]
    fn admit_rejects_overdeep_term() {
        let body = nest_not(MAX_DEPTH + 10);
        let d: Descriptor<Pk> = Descriptor { constants: BTreeMap::new(), body };
        assert_eq!(admit(&d, &CapabilitySet::everything()), Err(AdmissionError::TooDeep));
    }

    #[test]
    fn admit_accepts_at_the_limit() {
        // A term right at MAX_DEPTH should still admit (not under MAX_DEPTH + 1 levels of not).
        let body = nest_not(MAX_DEPTH - 1); // depth = MAX_DEPTH (MAX_DEPTH - 1 nots + leaf)
        let d: Descriptor<Pk> = Descriptor { constants: BTreeMap::new(), body };
        assert!(admit(&d, &CapabilitySet::everything()).is_ok());
    }
}

mod parser_edges {
    use super::*;
    use crate::calculus::ast::BTerm;

    #[test]
    fn invalid_constant_name_is_rejected_at_parse() {
        // Uppercase/hyphen names won't survive decode, so they must not survive parse either.
        assert!(parse::<Pk>("with(Bad_Name = 1, in true)").is_err());
        assert!(parse::<Pk>("with(has-hyphen = 1, in true)").is_err());
    }

    #[test]
    fn empty_hex_literal_is_rejected() {
        // `0x` with no digits is ambiguous and serves no purpose; reject it explicitly.
        let r = parse::<Pk>("with(x = 0x, in true)");
        assert!(r.is_err(), "expected error for empty hex literal");
    }

    #[test]
    fn negative_integer_literals_parse() {
        // The value sublanguage is signed (i128); -N is a literal.
        let d = parse::<Pk>("with(adj = -100, in true)").unwrap();
        assert_eq!(d.constants.get("adj"), Some(&Value::Int(-100)));
        // And inside an expression position.
        let d2 = parse::<Pk>("cmp(<=, -100, 100)").unwrap();
        assert!(matches!(d2.body, BTerm::Cmp(_, _, _)));
    }
}
