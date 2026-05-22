// SPDX-License-Identifier: CC0-1.0

//! Attestation schemas.
//!
//! The second argument of an `attest(oracle, schema)` proof obligation. A schema describes the
//! shape of payload an oracle attestation must carry to discharge the obligation. v1 fixes a
//! small set; the set is capability-gated and expected to grow empirically.

/// An oracle attestation schema.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Schema {
    /// A price attestation whose attested amount must match the operation amount within
    /// `tolerance_bps` basis points. Written `price_schema(tolerance_bps)` in source.
    PriceWithinBps {
        /// Tolerance in basis points.
        tolerance_bps: u32,
    },
}
