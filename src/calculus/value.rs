// SPDX-License-Identifier: CC0-1.0

//! Runtime values (sort `V`) and bounded-integer arithmetic.
//!
//! Arithmetic is on bounded integers modeled as [`i128`]. Addition, subtraction, and
//! multiplication saturate at the representable endpoints; division by zero yields zero. These
//! choices keep every value function total and free of implementation-defined behavior, as the
//! calculus requires for cross-implementation determinism.

use crate::prelude::*;
use crate::MiniscriptKey;

use super::ast::BTerm;
use super::registry::Symbol;

/// A hash value, tagged with the hash function that produced it.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum HashValue {
    /// SHA-256.
    Sha256([u8; 32]),
    /// Double-SHA-256.
    Hash256([u8; 32]),
    /// RIPEMD-160.
    Ripemd160([u8; 20]),
    /// SHA-256 followed by RIPEMD-160.
    Hash160([u8; 20]),
}

/// A runtime value (sort `V`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Value<Pk: MiniscriptKey> {
    /// A bounded integer.
    Int(i128),
    /// A public key.
    Key(Pk),
    /// A tagged hash.
    Hash(HashValue),
    /// Opaque bytes: destinations, deposit ids, and other identifiers.
    Bytes(Vec<u8>),
    /// A path into the descriptor's ast.
    Path(Vec<usize>),
    /// A subtree of the descriptor reified as data.
    Subtree(Box<BTerm<Pk>>),
    /// A list of values.
    List(Vec<Value<Pk>>),
    /// A symbol (an operation-type or branch tag).
    Symbol(Symbol),
}

impl<Pk: MiniscriptKey> Value<Pk> {
    /// Interpret this value as an integer, if it is one.
    pub fn as_int(&self) -> Option<i128> {
        match self {
            Value::Int(n) => Some(*n),
            _ => None,
        }
    }

    /// Interpret this value as a symbol, if it is one.
    pub fn as_symbol(&self) -> Option<&Symbol> {
        match self {
            Value::Symbol(s) => Some(s),
            _ => None,
        }
    }
}

/// Saturating addition.
pub fn sat_add(a: i128, b: i128) -> i128 { a.saturating_add(b) }

/// Saturating subtraction.
pub fn sat_sub(a: i128, b: i128) -> i128 { a.saturating_sub(b) }

/// Saturating multiplication.
pub fn sat_mul(a: i128, b: i128) -> i128 { a.saturating_mul(b) }

/// Floor division; division by zero yields zero. The single non-saturating overflow case
/// (`i128::MIN / -1`) saturates to [`i128::MAX`].
pub fn floor_div(a: i128, b: i128) -> i128 {
    if b == 0 {
        0
    } else {
        a.checked_div(b).unwrap_or(i128::MAX)
    }
}

/// `pct(n, p) = floor_div(sat_mul(n, p), 100)`.
pub fn pct(n: i128, p: i128) -> i128 { floor_div(sat_mul(n, p), 100) }

/// `bps(n, bp) = floor_div(sat_mul(n, bp), 10000)`.
pub fn bps(n: i128, bp: i128) -> i128 { floor_div(sat_mul(n, bp), 10000) }
