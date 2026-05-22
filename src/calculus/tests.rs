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
