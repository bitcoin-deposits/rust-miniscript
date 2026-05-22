// SPDX-License-Identifier: CC0-1.0

//! A concrete ledger-state snapshot.
//!
//! [`LedgerState`] is the trait the evaluator reads through; [`Snapshot`] is the canonical,
//! committable object a fraud proof carries. It holds exactly the fields dep-17 fixes, and reads
//! of absent rolling-window or cumulative-spend entries yield zero, so a snapshot need only carry
//! the referenced non-zero values. The byte encoding and commitment live in
//! [`encode`](super::encode).

use core::convert::TryFrom;

use crate::prelude::*;

use super::host::LedgerState;

/// A snapshot of the deposit's ledger state at the time of authorization.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Snapshot {
    /// The deposit's current balance.
    pub balance: i128,
    /// Blocks since the deposit's last authorized operation.
    pub blocks_since_activity: u32,
    /// Blocks since the deposit was opened.
    pub blocks_since_open: u32,
    /// Blocks since the deposit's last incoming payment.
    pub blocks_since_received: u32,
    /// The current block height.
    pub height: u32,
    /// Rolling-window totals, keyed by `(field, period)`. `field` is one of `amount_out`,
    /// `amount_in`, `transfer_count`.
    pub rolling: BTreeMap<(String, u32), i128>,
    /// Lifetime spend authorized via descriptor paths, keyed by path.
    pub cumulative_spent: BTreeMap<Vec<usize>, i128>,
}

impl LedgerState for Snapshot {
    fn blocks_since_activity(&self) -> i128 { self.blocks_since_activity as i128 }
    fn blocks_since_open(&self) -> i128 { self.blocks_since_open as i128 }
    fn blocks_since_received(&self) -> i128 { self.blocks_since_received as i128 }
    fn balance(&self) -> i128 { self.balance }
    fn rolling_window(&self, field: &str, period: i128) -> i128 {
        // A period that does not fit a u32 cannot have a recorded entry, so it reads as zero.
        match u32::try_from(period) {
            Ok(p) => self.rolling.get(&(field.to_string(), p)).copied().unwrap_or(0),
            Err(_) => 0,
        }
    }
    fn cumulative_spent_via(&self, path: &[usize]) -> i128 {
        self.cumulative_spent.get(path).copied().unwrap_or(0)
    }
    fn current_height(&self) -> i128 { self.height as i128 }
}
