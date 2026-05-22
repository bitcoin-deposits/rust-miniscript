// SPDX-License-Identifier: CC0-1.0

//! Integration tests: parse a worked example, then evaluate it to verdicts against a mock host.

use crate::prelude::*;

use super::eval::eval_b;
use super::host::{LedgerState, Operation};
use super::parse::parse;
use super::registry::Symbol;
use super::value::Value;
use super::witness::Witness;

type Pk = String;

/// A mock operation: a type tag and a bag of named arguments.
struct MockOp {
    ty: &'static str,
    args: BTreeMap<String, Value<Pk>>,
}

impl MockOp {
    fn spend(amount: i128, destination: &str) -> Self {
        let mut args = BTreeMap::new();
        args.insert("amount".to_string(), Value::Int(amount));
        args.insert("destination".to_string(), Value::Key(destination.to_string()));
        MockOp { ty: "spend", args }
    }
    fn of_type(ty: &'static str) -> Self { MockOp { ty, args: BTreeMap::new() } }
}

impl Operation<Pk> for MockOp {
    fn op_type(&self) -> Symbol { Symbol::new(self.ty) }
    fn arg(&self, name: &str) -> Option<Value<Pk>> { self.args.get(name).cloned() }
    fn path(&self) -> Option<Vec<usize>> { None }
    fn subtree(&self) -> Option<super::ast::BTerm<Pk>> { None }
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
    let w = Witness::signed_by(signers.iter().map(|s| s.to_string()));
    eval_b(&d.body, &d.constants, op, st, &w).expect("eval")
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
        let signers: Vec<String> = (0..4)
            .filter(|i| mask & (1 << i) != 0)
            .map(|i| KEYS[i].to_string())
            .collect();
        let w = Witness::signed_by(signers);
        let op = MockOp::spend(1, "x");
        let st = MockLedger::default();
        let env = BTreeMap::new();
        eval_b(term, &env, &op, &st, &w).expect("generated terms never error")
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
