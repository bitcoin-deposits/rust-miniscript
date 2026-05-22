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

/// A mock operation: a type tag, named arguments, and optional modification path/subtree.
struct MockOp {
    ty: &'static str,
    args: BTreeMap<String, Value<Pk>>,
    path: Option<Vec<usize>>,
    subtree: Option<super::ast::BTerm<Pk>>,
    nonce: u64,
}

impl MockOp {
    fn spend(amount: i128, destination: &str) -> Self {
        let mut args = BTreeMap::new();
        args.insert("amount".to_string(), Value::Int(amount));
        args.insert("destination".to_string(), Value::Key(destination.to_string()));
        MockOp { ty: "spend", args, path: None, subtree: None, nonce: 0 }
    }
    fn of_type(ty: &'static str) -> Self {
        MockOp { ty, args: BTreeMap::new(), path: None, subtree: None, nonce: 0 }
    }
    fn replace(path: Vec<usize>, subtree: super::ast::BTerm<Pk>) -> Self {
        MockOp { ty: "replace", args: BTreeMap::new(), path: Some(path), subtree: Some(subtree), nonce: 0 }
    }
    fn with_nonce(mut self, nonce: u64) -> Self {
        self.nonce = nonce;
        self
    }
}

impl Operation<Pk> for MockOp {
    fn op_type(&self) -> Symbol { Symbol::new(self.ty) }
    fn arg(&self, name: &str) -> Option<Value<Pk>> { self.args.get(name).cloned() }
    fn args(&self) -> Vec<(String, Value<Pk>)> {
        self.args.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }
    fn path(&self) -> Option<Vec<usize>> { self.path.clone() }
    fn subtree(&self) -> Option<super::ast::BTerm<Pk>> { self.subtree.clone() }
    fn deposit_id(&self) -> [u8; 32] { [0u8; 32] }
    fn nonce(&self) -> u64 { self.nonce }
    fn expiry(&self) -> u32 { u32::MAX }
}

/// A mock ledger snapshot.
struct MockLedger {
    balance: i128,
    since_activity: i128,
    since_open: i128,
    rolling_out: i128,
    height: i128,
}

impl Default for MockLedger {
    fn default() -> Self {
        MockLedger { balance: 1000, since_activity: 0, since_open: 0, rolling_out: 0, height: 0 }
    }
}

impl LedgerState for MockLedger {
    fn blocks_since_activity(&self) -> i128 { self.since_activity }
    fn blocks_since_open(&self) -> i128 { self.since_open }
    fn balance(&self) -> i128 { self.balance }
    fn rolling_window(&self, field: &str, _period: i128) -> i128 {
        if field == "amount_out" {
            self.rolling_out
        } else {
            0
        }
    }
    fn cumulative_spent_via(&self, _path: &[usize]) -> i128 { 0 }
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
