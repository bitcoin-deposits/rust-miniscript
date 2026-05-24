// SPDX-License-Identifier: CC0-1.0

//! Hard limits enforced across the calculus.
//!
//! These cap untrusted-input depth and breadth at every entry point that takes adversary-controlled
//! bytes — the parser, the canonical decoder, and modification operations whose path comes from an
//! operation. Admission additionally checks descriptor depth, so any term that has passed admission
//! is bounded by these constants and post-admission evaluation does not need to re-check.

/// Maximum nesting depth of an AST during parse, decode, and modification. Terms deeper than this
/// are rejected at the boundary; admission rejects descriptors exceeding it.
///
/// 128 is chosen to stay well within typical thread-stack budgets (2 MiB on most platforms,
/// including the default cargo-test thread) even in debug builds where stack frames are larger.
/// It is also far deeper than any realistic descriptor.
pub const MAX_DEPTH: usize = 128;
