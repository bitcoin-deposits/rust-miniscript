// SPDX-License-Identifier: CC0-1.0

//! Fixed signatures of operators, value functions, state predicates, and symbols.
//!
//! These enumerations are the only avenue by which the calculus names operations on the
//! environment. They are fixed at the protocol level; an operator advertises which subset it
//! implements via capability declaration.

use crate::prelude::*;

/// Comparison operators usable in `cmp(...)`.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum CmpOp {
    /// `=`
    Eq,
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `>`
    Gt,
    /// `>=`
    Ge,
}

impl CmpOp {
    /// The source name of this operator.
    pub fn name(self) -> &'static str {
        match self {
            CmpOp::Eq => "=",
            CmpOp::Lt => "<",
            CmpOp::Le => "<=",
            CmpOp::Gt => ">",
            CmpOp::Ge => ">=",
        }
    }

    /// Parse an operator from its source name.
    pub fn from_name(s: &str) -> Option<Self> {
        Some(match s {
            "=" => CmpOp::Eq,
            "<" => CmpOp::Lt,
            "<=" => CmpOp::Le,
            ">" => CmpOp::Gt,
            ">=" => CmpOp::Ge,
            _ => return None,
        })
    }
}

/// Value-producing functions (sort `V`). Each is a total, deterministic function of the
/// operation and ledger state, and is constant in the witness.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum ValueFn {
    /// Saturating addition.
    Add,
    /// Saturating subtraction.
    Sub,
    /// Saturating multiplication.
    Mul,
    /// Floor division; division by zero yields zero.
    Div,
    /// Minimum.
    Min,
    /// Maximum.
    Max,
    /// `pct(n, p) = div(mul(n, p), 100)`.
    Pct,
    /// `bps(n, bp) = div(mul(n, bp), 10000)`.
    Bps,
    /// The operation's type, as a symbol.
    OperationType,
    /// A named argument of the operation.
    OperationArg,
    /// The ast path targeted by a modification operation.
    OperationPath,
    /// The subtree introduced by an `insert` or `replace` operation.
    OperationSubtree,
    /// Blocks since the deposit's last authorized operation.
    BlocksSinceActivity,
    /// Blocks since the deposit was opened.
    BlocksSinceOpen,
    /// The deposit's current balance.
    DepositBalance,
    /// Cumulative `field` over a rolling window of `period` blocks.
    RollingWindow,
    /// Lifetime spend authorized via a descriptor path.
    CumulativeSpentVia,
    /// The subtree at a path in the current descriptor.
    AstRef,
    /// The head constructor at a path in the current descriptor.
    AstShapeAt,
    /// Construct a path value from a sequence of indices.
    Path,
}

impl ValueFn {
    /// The source name of this function.
    pub fn name(self) -> &'static str {
        match self {
            ValueFn::Add => "add",
            ValueFn::Sub => "sub",
            ValueFn::Mul => "mul",
            ValueFn::Div => "div",
            ValueFn::Min => "min",
            ValueFn::Max => "max",
            ValueFn::Pct => "pct",
            ValueFn::Bps => "bps",
            ValueFn::OperationType => "operation_type",
            ValueFn::OperationArg => "operation_arg",
            ValueFn::OperationPath => "operation_path",
            ValueFn::OperationSubtree => "operation_subtree",
            ValueFn::BlocksSinceActivity => "blocks_since_activity",
            ValueFn::BlocksSinceOpen => "blocks_since_open",
            ValueFn::DepositBalance => "deposit_balance",
            ValueFn::RollingWindow => "rolling_window",
            ValueFn::CumulativeSpentVia => "cumulative_spent_via",
            ValueFn::AstRef => "ast_ref",
            ValueFn::AstShapeAt => "ast_shape_at",
            ValueFn::Path => "path",
        }
    }

    /// Parse a function from its source name.
    pub fn from_name(s: &str) -> Option<Self> {
        Some(match s {
            "add" => ValueFn::Add,
            "sub" => ValueFn::Sub,
            "mul" => ValueFn::Mul,
            "div" => ValueFn::Div,
            "min" => ValueFn::Min,
            "max" => ValueFn::Max,
            "pct" => ValueFn::Pct,
            "bps" => ValueFn::Bps,
            "operation_type" => ValueFn::OperationType,
            "operation_arg" => ValueFn::OperationArg,
            "operation_path" => ValueFn::OperationPath,
            "operation_subtree" => ValueFn::OperationSubtree,
            "blocks_since_activity" => ValueFn::BlocksSinceActivity,
            "blocks_since_open" => ValueFn::BlocksSinceOpen,
            "deposit_balance" => ValueFn::DepositBalance,
            "rolling_window" => ValueFn::RollingWindow,
            "cumulative_spent_via" => ValueFn::CumulativeSpentVia,
            "ast_ref" => ValueFn::AstRef,
            "ast_shape_at" => ValueFn::AstShapeAt,
            "path" => ValueFn::Path,
            _ => return None,
        })
    }
}

/// Boolean state predicates (sort `B`): total, deterministic functions of the operation and
/// ledger state, constant in the witness. They may appear freely under negation and as `if`
/// conditions because they cannot be exploited by withholding witness data.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum StatePred {
    /// `older(n)`: a relative timelock has elapsed.
    Older,
    /// `after(n)`: an absolute height has been reached.
    After,
    /// The operation amount is at most `n`.
    AmountAtMost,
    /// The operation amount is between `low` and `high`.
    AmountInRange,
    /// The operation amount is at most `p` percent of the deposit balance.
    AmountAtMostPct,
    /// The operation destination equals an id.
    DestinationIs,
    /// The operation destination is in a set.
    DestinationIn,
    /// The balance is at least `n`.
    BalanceAtLeast,
    /// The balance is at most `n`.
    BalanceAtMost,
    /// At least `n` blocks since last activity.
    BlocksSinceActivityAtLeast,
    /// Fewer than `n` blocks since deposit open.
    BlocksSinceOpenBelow,
    /// Rolling-window amount over `period` is below `n`.
    RollingAmountBelow,
    /// Rolling-window amount over `period` is below `p` percent of balance.
    RollingAmountBelowPct,
    /// Structural equality of a value with the subtree at a path.
    SubtreeAt,
}

impl StatePred {
    /// The source name of this predicate.
    pub fn name(self) -> &'static str {
        match self {
            StatePred::Older => "older",
            StatePred::After => "after",
            StatePred::AmountAtMost => "amount_at_most",
            StatePred::AmountInRange => "amount_in_range",
            StatePred::AmountAtMostPct => "amount_at_most_pct",
            StatePred::DestinationIs => "destination_is",
            StatePred::DestinationIn => "destination_in",
            StatePred::BalanceAtLeast => "balance_at_least",
            StatePred::BalanceAtMost => "balance_at_most",
            StatePred::BlocksSinceActivityAtLeast => "blocks_since_activity_at_least",
            StatePred::BlocksSinceOpenBelow => "blocks_since_open_below",
            StatePred::RollingAmountBelow => "rolling_amount_below",
            StatePred::RollingAmountBelowPct => "rolling_amount_below_pct",
            StatePred::SubtreeAt => "subtree_at",
        }
    }

    /// Parse a predicate from its source name.
    pub fn from_name(s: &str) -> Option<Self> {
        Some(match s {
            "older" => StatePred::Older,
            "after" => StatePred::After,
            "amount_at_most" => StatePred::AmountAtMost,
            "amount_in_range" => StatePred::AmountInRange,
            "amount_at_most_pct" => StatePred::AmountAtMostPct,
            "destination_is" => StatePred::DestinationIs,
            "destination_in" => StatePred::DestinationIn,
            "balance_at_least" => StatePred::BalanceAtLeast,
            "balance_at_most" => StatePred::BalanceAtMost,
            "blocks_since_activity_at_least" => StatePred::BlocksSinceActivityAtLeast,
            "blocks_since_open_below" => StatePred::BlocksSinceOpenBelow,
            "rolling_amount_below" => StatePred::RollingAmountBelow,
            "rolling_amount_below_pct" => StatePred::RollingAmountBelowPct,
            "subtree_at" => StatePred::SubtreeAt,
            _ => return None,
        })
    }
}

/// A symbol: an operation-type tag or a `match` branch tag (e.g. `spend`, `insert`).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Symbol(pub String);

impl Symbol {
    /// Construct a symbol from a string.
    pub fn new(s: impl Into<String>) -> Self { Symbol(s.into()) }

    /// The symbol's text.
    pub fn as_str(&self) -> &str { &self.0 }
}
