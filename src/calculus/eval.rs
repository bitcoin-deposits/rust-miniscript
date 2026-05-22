// SPDX-License-Identifier: CC0-1.0

//! The evaluator.
//!
//! Evaluation is a strict, total, structural fold of `(T, w, s, m)` to a verdict. The
//! m-constancy invariant is reflected in the signatures: [`eval_v`] and [`eval_state`] do not
//! receive the witness and cannot depend on it; [`verify_o`] is the sole entry point for witness
//! data.
//!
//! `eval_*` returns a `Result`. The error cases ([`EvalError`]) are exactly the well-formedness
//! violations that admission rules out — an unresolved constant, a sort/type mismatch, an
//! unsupported primitive. After a descriptor passes admission these cannot occur, so post-admission
//! evaluation is total.

use crate::prelude::*;
use crate::MiniscriptKey;

use super::ast::{BTerm, Obligation, VTerm};
use super::host::{LedgerState, Operation};
use super::registry::{CmpOp, StatePred, ValueFn};
use super::signature::Verifier;
use super::value::{bps, floor_div, pct, sat_add, sat_mul, sat_sub, HashValue, Value};
use super::witness::Witness;

/// A constant environment: the bindings from a descriptor's `with(...)`.
pub type Env<Pk> = BTreeMap<String, Value<Pk>>;

/// A condition under which evaluation cannot produce a verdict. All of these are caught by
/// admission; a descriptor that has passed admission never produces one.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum EvalError {
    /// A `with(...)` constant referenced but not bound.
    UnresolvedVar(String),
    /// A value had the wrong type for the position it was used in.
    TypeMismatch(&'static str),
    /// A primitive not yet implemented in this phase.
    Unsupported(&'static str),
}

/// Evaluate a boolean term to a verdict.
///
/// `w` and `verifier` are the only witness-dependent inputs; they reach the leaves solely through
/// [`verify_o`]. [`eval_v`] and [`eval_state`] do not receive them, so values and state predicates
/// are constant in the witness by construction.
pub fn eval_b<Pk, O, L, V>(
    t: &BTerm<Pk>,
    env: &Env<Pk>,
    op: &O,
    st: &L,
    w: &Witness<Pk>,
    verifier: &V,
) -> Result<bool, EvalError>
where
    Pk: MiniscriptKey,
    O: Operation<Pk>,
    L: LedgerState,
    V: Verifier<Pk>,
{
    match t {
        BTerm::Const(b) => Ok(*b),
        BTerm::And(bs) => {
            for b in bs {
                if !eval_b(b, env, op, st, w, verifier)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        BTerm::Or(bs) => {
            for b in bs {
                if eval_b(b, env, op, st, w, verifier)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        BTerm::Thresh(k, bs) => {
            let mut count = 0;
            for b in bs {
                if eval_b(b, env, op, st, w, verifier)? {
                    count += 1;
                }
            }
            Ok(count >= *k)
        }
        BTerm::Not(b) => Ok(!eval_b(b, env, op, st, w, verifier)?),
        BTerm::If(c, then_, els) => {
            if eval_b(c, env, op, st, w, verifier)? {
                eval_b(then_, env, op, st, w, verifier)
            } else {
                eval_b(els, env, op, st, w, verifier)
            }
        }
        BTerm::Match { scrutinee, arms, default } => {
            let key = eval_v(scrutinee, env, op, st)?;
            let sym = key.as_symbol().ok_or(EvalError::TypeMismatch("match scrutinee not a symbol"))?;
            for (tag, body) in arms {
                if tag == sym {
                    return eval_b(body, env, op, st, w, verifier);
                }
            }
            eval_b(default, env, op, st, w, verifier)
        }
        BTerm::Cmp(o, a, b) => {
            let av = eval_v(a, env, op, st)?;
            let bv = eval_v(b, env, op, st)?;
            eval_cmp(*o, &av, &bv)
        }
        BTerm::State(p, args) => {
            let mut vals = Vec::with_capacity(args.len());
            for a in args {
                vals.push(eval_v(a, env, op, st)?);
            }
            eval_state(*p, &vals, op, st)
        }
        BTerm::Prove(o) => verify_o(o, env, w, verifier, op, st),
    }
}

/// Evaluate a value term. Does not receive the witness: values are constant in `m`.
pub fn eval_v<Pk, O, L>(t: &VTerm<Pk>, env: &Env<Pk>, op: &O, st: &L) -> Result<Value<Pk>, EvalError>
where
    Pk: MiniscriptKey,
    O: Operation<Pk>,
    L: LedgerState,
{
    match t {
        VTerm::Lit(v) => Ok(v.clone()),
        VTerm::Var(name) => env.get(name).cloned().ok_or_else(|| EvalError::UnresolvedVar(name.clone())),
        VTerm::Op(f, args) => eval_valuefn(*f, args, env, op, st),
    }
}

fn eval_valuefn<Pk, O, L>(
    f: ValueFn,
    args: &[VTerm<Pk>],
    env: &Env<Pk>,
    op: &O,
    st: &L,
) -> Result<Value<Pk>, EvalError>
where
    Pk: MiniscriptKey,
    O: Operation<Pk>,
    L: LedgerState,
{
    let int_arg = |i: usize| -> Result<i128, EvalError> {
        eval_v(&args[i], env, op, st)?.as_int().ok_or(EvalError::TypeMismatch("expected integer"))
    };
    match f {
        ValueFn::Add => Ok(Value::Int(sat_add(int_arg(0)?, int_arg(1)?))),
        ValueFn::Sub => Ok(Value::Int(sat_sub(int_arg(0)?, int_arg(1)?))),
        ValueFn::Mul => Ok(Value::Int(sat_mul(int_arg(0)?, int_arg(1)?))),
        ValueFn::Div => Ok(Value::Int(floor_div(int_arg(0)?, int_arg(1)?))),
        ValueFn::Min => Ok(Value::Int(int_arg(0)?.min(int_arg(1)?))),
        ValueFn::Max => Ok(Value::Int(int_arg(0)?.max(int_arg(1)?))),
        ValueFn::Pct => Ok(Value::Int(pct(int_arg(0)?, int_arg(1)?))),
        ValueFn::Bps => Ok(Value::Int(bps(int_arg(0)?, int_arg(1)?))),
        ValueFn::OperationType => Ok(Value::Symbol(op.op_type())),
        ValueFn::OperationArg => {
            let name = eval_v(&args[0], env, op, st)?;
            let name = name.as_symbol().ok_or(EvalError::TypeMismatch("operation_arg name not a symbol"))?;
            op.arg(name.as_str()).ok_or(EvalError::TypeMismatch("operation lacks this argument"))
        }
        ValueFn::OperationPath => {
            op.path().map(Value::Path).ok_or(EvalError::TypeMismatch("operation has no path"))
        }
        ValueFn::OperationSubtree => op
            .subtree()
            .map(|t| Value::Subtree(Box::new(t)))
            .ok_or(EvalError::TypeMismatch("operation has no subtree")),
        ValueFn::BlocksSinceActivity => Ok(Value::Int(st.blocks_since_activity())),
        ValueFn::BlocksSinceOpen => Ok(Value::Int(st.blocks_since_open())),
        ValueFn::DepositBalance => Ok(Value::Int(st.balance())),
        ValueFn::RollingWindow => {
            let field = eval_v(&args[0], env, op, st)?;
            let field = field.as_symbol().ok_or(EvalError::TypeMismatch("rolling_window field not a symbol"))?;
            let period = int_arg(1)?;
            Ok(Value::Int(st.rolling_window(field.as_str(), period)))
        }
        ValueFn::CumulativeSpentVia => {
            let p = eval_v(&args[0], env, op, st)?;
            match p {
                Value::Path(p) => Ok(Value::Int(st.cumulative_spent_via(&p))),
                _ => Err(EvalError::TypeMismatch("cumulative_spent_via expects a path")),
            }
        }
        ValueFn::Path => {
            let mut idx = Vec::with_capacity(args.len());
            for a in args {
                let n = eval_v(a, env, op, st)?.as_int().ok_or(EvalError::TypeMismatch("path index not an integer"))?;
                idx.push(n as usize);
            }
            Ok(Value::Path(idx))
        }
        ValueFn::AstRef | ValueFn::AstShapeAt => Err(EvalError::Unsupported("ast inspection (phase 4)")),
    }
}

/// Evaluate a state predicate. Does not receive the witness: state predicates are constant in `m`.
pub fn eval_state<Pk, O, L>(
    p: StatePred,
    args: &[Value<Pk>],
    op: &O,
    st: &L,
) -> Result<bool, EvalError>
where
    Pk: MiniscriptKey,
    O: Operation<Pk>,
    L: LedgerState,
{
    let amount = || -> Result<i128, EvalError> {
        op.arg("amount").and_then(|v| v.as_int()).ok_or(EvalError::TypeMismatch("operation has no amount"))
    };
    let arg_int = |i: usize| args[i].as_int().ok_or(EvalError::TypeMismatch("expected integer argument"));
    match p {
        StatePred::Older => Ok(st.blocks_since_open() >= arg_int(0)?),
        StatePred::After => Ok(st.current_height() >= arg_int(0)?),
        StatePred::AmountAtMost => Ok(amount()? <= arg_int(0)?),
        StatePred::AmountInRange => Ok(amount()? >= arg_int(0)? && amount()? <= arg_int(1)?),
        StatePred::AmountAtMostPct => Ok(amount()? <= pct(st.balance(), arg_int(0)?)),
        StatePred::DestinationIs => {
            let dest = op.arg("destination").ok_or(EvalError::TypeMismatch("operation has no destination"))?;
            Ok(dest == args[0])
        }
        StatePred::DestinationIn => {
            let dest = op.arg("destination").ok_or(EvalError::TypeMismatch("operation has no destination"))?;
            match &args[0] {
                Value::List(set) => Ok(set.iter().any(|v| *v == dest)),
                _ => Err(EvalError::TypeMismatch("destination_in expects a list")),
            }
        }
        StatePred::BalanceAtLeast => Ok(st.balance() >= arg_int(0)?),
        StatePred::BalanceAtMost => Ok(st.balance() <= arg_int(0)?),
        StatePred::BlocksSinceActivityAtLeast => Ok(st.blocks_since_activity() >= arg_int(0)?),
        StatePred::BlocksSinceOpenBelow => Ok(st.blocks_since_open() < arg_int(0)?),
        StatePred::RollingAmountBelow => {
            Ok(st.rolling_window("amount_out", arg_int(1)?) <= arg_int(0)?)
        }
        StatePred::RollingAmountBelowPct => {
            Ok(st.rolling_window("amount_out", arg_int(1)?) <= pct(st.balance(), arg_int(0)?))
        }
        StatePred::SubtreeAt => Err(EvalError::Unsupported("subtree_at (phase 4)")),
    }
}

fn eval_cmp<Pk: MiniscriptKey>(o: CmpOp, a: &Value<Pk>, b: &Value<Pk>) -> Result<bool, EvalError> {
    match o {
        CmpOp::Eq => Ok(a == b),
        _ => {
            let (a, b) = (
                a.as_int().ok_or(EvalError::TypeMismatch("ordered comparison needs integers"))?,
                b.as_int().ok_or(EvalError::TypeMismatch("ordered comparison needs integers"))?,
            );
            Ok(match o {
                CmpOp::Lt => a < b,
                CmpOp::Le => a <= b,
                CmpOp::Gt => a > b,
                CmpOp::Ge => a >= b,
                CmpOp::Eq => unreachable!(),
            })
        }
    }
}

/// Discharge a proof obligation against the witness. The only witness-dependent evaluation.
pub fn verify_o<Pk, O, L, V>(
    o: &Obligation<Pk>,
    env: &Env<Pk>,
    w: &Witness<Pk>,
    verifier: &V,
    op: &O,
    st: &L,
) -> Result<bool, EvalError>
where
    Pk: MiniscriptKey,
    O: Operation<Pk>,
    L: LedgerState,
    V: Verifier<Pk>,
{
    let as_key = |v: &VTerm<Pk>| -> Result<Pk, EvalError> {
        match eval_v(v, env, op, st)? {
            Value::Key(k) => Ok(k),
            _ => Err(EvalError::TypeMismatch("expected a key")),
        }
    };
    let as_keys = |v: &VTerm<Pk>| -> Result<Vec<Pk>, EvalError> {
        match eval_v(v, env, op, st)? {
            Value::List(items) => items
                .into_iter()
                .map(|v| match v {
                    Value::Key(k) => Ok(k),
                    _ => Err(EvalError::TypeMismatch("key list contains a non-key")),
                })
                .collect(),
            _ => Err(EvalError::TypeMismatch("expected a list of keys")),
        }
    };
    // A signature by `key` is valid iff the witness carries an entry under that key that the
    // verifier accepts over the operation's signing message.
    let signed_by = |key: &Pk| -> bool {
        match w.signatures.get(key) {
            Some(sig) => verifier.verify_signature(key, sig, &op.signing_message()),
            None => false,
        }
    };
    match o {
        Obligation::Pk(v) => Ok(signed_by(&as_key(v)?)),
        Obligation::PkAny(v) => Ok(as_keys(v)?.iter().any(signed_by)),
        Obligation::PkThreshold(k, v) => {
            let mut keys = as_keys(v)?;
            keys.sort();
            keys.dedup();
            Ok(keys.iter().filter(|k| signed_by(k)).count() >= *k)
        }
        Obligation::PkH(v) => {
            let keyhash = match eval_v(v, env, op, st)? {
                Value::Hash(h) => h,
                _ => return Err(EvalError::TypeMismatch("pk_h expects a key hash")),
            };
            // Find a witnessed key that hashes to `keyhash` and whose signature verifies.
            let msg = op.signing_message();
            Ok(w.signatures.iter().any(|(k, sig)| {
                verifier.key_hashes_to(k, &keyhash) && verifier.verify_signature(k, sig, &msg)
            }))
        }
        Obligation::Hashlock(v) => {
            let h = match eval_v(v, env, op, st)? {
                Value::Hash(h) => h,
                _ => return Err(EvalError::TypeMismatch("hashlock expects a hash")),
            };
            Ok(match w.preimages.get(&h) {
                Some(preimage) => hash_matches(&h, preimage),
                None => false,
            })
        }
        Obligation::Attest(key, _schema) => Ok(w.attestations.contains(&as_key(key)?)),
    }
}

/// Whether `preimage` hashes to `h` under the function `h` is tagged with.
fn hash_matches(h: &HashValue, preimage: &[u8]) -> bool {
    use bitcoin::hashes::{hash160, ripemd160, sha256, Hash as _};
    match h {
        HashValue::Sha256(d) => sha256::Hash::hash(preimage).to_byte_array() == *d,
        HashValue::Hash256(d) => crate::hash256::Hash::hash(preimage).to_byte_array() == *d,
        HashValue::Ripemd160(d) => ripemd160::Hash::hash(preimage).to_byte_array() == *d,
        HashValue::Hash160(d) => hash160::Hash::hash(preimage).to_byte_array() == *d,
    }
}
