# How this implementation is verified

This implementation of the dep-16 calculus was written collaboratively with an AI coding assistant. AI codegen does not relieve the verification burden; it raises it. This document is the inventory of what we did to convince ourselves the implementation matches its specification, and — equally important — what we have **not** yet done.

## Layers, outer to inner

Read this as a defense-in-depth listing, not a hierarchy. Each layer catches a different class of mistake.

### 1. Static guarantees encoded in the type system

These are properties that hold by construction; the compiler refuses any code that would violate them.

- **Sort discipline.** `BTerm`, `VTerm`, and `Obligation` are distinct Rust enums. A B-term cannot appear where a V-term is expected, and vice versa. The polarity check in `admission.rs` enumerates `BTerm` constructors exhaustively, so adding a new constructor without updating the polarity rule is a compile error.
- **m-constancy of state predicates and value functions** ([PAPER.md §3.2](PAPER.md)). `eval_v` and `eval_state` take `(env, root, op, st)` but no `Witness`. There is no expressible code path in which a value function or state predicate observes the witness — that's the load-bearing invariant the monotonicity theorem rests on, and it is checked by the type-checker, not by tests.
- **Verifier abstraction.** All real cryptography flows through the `Verifier<Pk>` trait. The calculus's evaluator is generic in the key type, so secp256k1 and the test mock are the same code path from the evaluator's point of view.
- **CanonicalKey trait** for the dep-17 encoding. Each key type fixes its canonical byte serialization (33-byte compressed for `bitcoin::PublicKey`, 32-byte x-only for `XOnlyPublicKey`).
- **Scheme tag enumerated, not strung together.** `Scheme<Pk>` is an enum with two arms (`Wsh` / `Tr`); the encoder and decoder dispatch on it. Adding a new scheme requires updating both ends; no string-based dispatch.
- **`DescriptorNode` is a sum.** Descriptor-rooted path navigation returns `Body(&BTerm) | InternalKey(&Pk)`. Code that consumes a node has to handle both; you cannot accidentally treat an internal key as a body subterm.

### 2. Properties checked by tests

The lib suite is 247 tests, all green — 127 in `calculus::*` (the new work) plus 120 upstream miniscript tests retained unchanged. Notable shapes of the new tests:

- **Witness-monotonicity, randomized** (`calculus::tests::monotonicity::admitted_terms_are_witness_monotone`): generate 500 adversarial random terms, run them through admission, and for each admitted term enumerate every witness-mask pair `(m ⊆ m')` and assert that `eval(T, w, s, m) ⇒ eval(T, w, s, m')`. This is the empirical complement to the structural argument in PAPER.md §3.1. The rejected terms confirm the polarity check is doing real work.
- **Source roundtrip, randomized** (`calculus::tests::roundtrip_properties::source_roundtrip_for_admitted_terms`): for 500 admitted random terms, `parse(to_string(d)) == d`. Tests the printer/parser pair against the AST.
- **Polarity exhaustiveness** (`calculus::tests::polarity_exhaustiveness`): for every B-term constructor, place a proof obligation in every positional slot and verify admission accepts iff the slot is positive. Adding a new constructor without polarity coverage will fail this test.
- **Canonical encoding rejection** (`calculus::tests::codec` — 8 tests): the decoder is tested against deliberately malformed inputs — unknown scheme bytes, non-canonical sort order of constants, duplicate names, trailing bytes, non-canonical name format, signed-vs-unsigned literal forms, hash-function tag bounds. Every such input is rejected with a specific `DecodeError`.
- **Operation signature binding** (`calculus::tests::operation_codec` — 3 tests): two operations differing only in nonce, only in arguments, or only in `(path, subtree)` produce distinct preimages and distinct sighashes. A signature over one does not authorize the other.
- **Modification chain invariants** (`calculus::tests::partial_reveal_modification` — 19 tests): `T → T' → T''` through repeated modifications, each one re-running admission. The scheme is preserved, the internal key is preserved (under body edits), the descriptor_id is fresh, ill-formed candidates are rejected even when the underlying operation is authorized.
- **Scheme equivalences** (`calculus::tests::wrappers` — 7 tests): `tr(K) ≡ prove(pk(K))` and `tr(K, body) ≡ or(prove(pk(K)), body)` as authorization relations, with descriptor_id distinguishing the wrapper choice.
- **Internal-key rotation** (in the partial_reveal module): `replace` at `[0]` of a tr descriptor rotates K; `[0]` is a path-tree leaf so deeper paths are rejected; insert/delete at `[0]` are rejected; rotation against `tr(K)` (no body) works; rotation against `wsh` is rejected for the right reason (missing `subtree` arg); rotation requires the new key as a `key` argument, not as a `subtree`.
- **Worked wallet templates** (`calculus::tests::templates` and `calculus::tests::ledger_primitives`): social recovery with guardian key rotation, Liana-style decaying multisig, linear vesting, spending rate limit, inheritance, dead-man's-switch keyed on incoming payments, cliff vesting via `since_open`. Plus a delegate-with-allowance + guardian-recovery descriptor (`ALLOWANCE`) exercised across nine top-level tests. Each template is a parseable descriptor with positive and negative scenarios — what the policy admits and what it rejects, with the relevant ledger conditions.
- **Real cryptography** (`calculus::secp_tests` — 9 tests with `bitcoin::secp256k1`): real ECDSA keypairs sign real operations and verify through `EcdsaVerifier`; the same shape with x-only keys and BIP-340 Schnorr through `SchnorrVerifier`; signatures bind to the operation preimage (a signature over op A does not authorize op B); descriptors with real keys round-trip through the canonical encoder.
- **ECDSA low-s rejection** (in secp_tests): take a real low-s signature, negate the `s` component to produce a mathematically valid high-s signature, and verify the verifier rejects it. Closes the canonical malleability under ECDSA.
- **Fraud-proof bundle round-trip** (`calculus::tests::fraud_bundle` — 5 tests): a complete `FraudProof` (descriptor, operation, snapshot, witness, verdict) encodes, decodes, and re-adjudicates identically. This is the determinism property of PAPER.md §3.3 made concrete.
- **Depth limit** (`calculus::tests::hardening`): `MAX_DEPTH = 128`. Inputs deeper than the cap are rejected before any recursive descent that could overflow the stack.

### 3. Fuzz harnesses

Three honggfuzz targets exercise the parsing and decoding paths against arbitrary bytes:

- `fuzz/fuzz_targets/dep16_parse.rs` — the source parser. Any byte string either parses or returns a structured `ParseError`; nothing panics.
- `fuzz/fuzz_targets/dep16_decode_descriptor.rs` — the canonical descriptor decoder. Any byte string either decodes to a `Descriptor` or returns a structured `DecodeError`.
- `fuzz/fuzz_targets/dep16_decode_fraud_proof.rs` — the fraud-proof bundle decoder.

These are smoke-tested in CI by `calculus::tests::fuzz_smoke` (each harness's `do_test` is called on a handful of edge inputs); for real coverage they must be run under `cargo hfuzz`.

### 4. Cross-document consistency

DEP-16 (the calculus spec), DEP-17 (the canonical encodings spec), PAPER.md (the formal calculus paper), the README, and the implementation are kept in sync by edit. When path semantics moved from body-rooted to descriptor-rooted, DEP-16, DEP-17, PAPER (where relevant), the README, the implementation, and every test were updated in a single commit. This is the manual analog of a conformance suite — if the spec says it and the test asserts it, the implementation has to match both.

## What we don't yet verify

These are honest limitations, called out so a reviewer doesn't have to find them by absence.

- **No mechanized proof.** The witness-monotonicity theorem (PAPER.md §3.1) is argued by structural induction on terms in prose. A Coq / Lean / Rocq mechanization would be a meaningful upgrade and is not done. The 500-term randomized property test is the empirical check; it does not cover the space.
- **One implementation.** Cross-implementation conformance is a property dep-17's canonical encoding rules are designed to support, but there is currently no second implementation to disagree with this one.
- **`Obligation::Attest` is a stub.** The verifier in this crate checks attestor *presence* in the witness, not real oracle-signature verification + schema satisfaction. Marked `SECURITY: deferred` at `src/calculus/ast.rs:79` and `src/calculus/eval.rs:436`. The full attestation/oracle dep is what unblocks this; see DEP-17's open question.
- **No leaf-Merkle commitment for `tr` script-path.** v1 reveals the full body in fraud proofs. The "partial reveal" property we test is at the witness layer (the witness for a key-path-authorized operation carries no body information); the *encoding* still commits to and reveals the whole body. A BIP-341-style leaf-Merkle commitment is a forward-compatible addition that v1 does not include.
- **Operator-side state is mock-only in tests.** `LedgerState` is implemented for a fixed-field `MockLedger`. Real operators will need an implementation that derives the same fields from a live ledger; that integration is out of scope here.
- **No formal soundness proof for the modification rule.** PAPER.md §3.4 (reflexivity) argues by induction that admission on every candidate preserves the system invariant. This is correct and not mechanized.

## How AI codegen specifically figures in

Working with AI codegen amplifies the value of the layers above. A handful of practices we ran into:

- **Specifications drive implementation, not the other way around.** When PAPER.md / DEP-16 / DEP-17 said something the implementation didn't, the implementation moved. This direction matters: AI-generated code reads as plausible even when wrong, and the spec is the cheaper place to detect a confused design.
- **Every committed change runs the full test suite first.** No "I'll fix the test in the next commit." The cost of letting a known failure ride is much higher when the code reviewer is not also the author of the next change.
- **Static guarantees are the most valuable line of defense** when reviewing AI-written code. A type-level invariant (`eval_v` cannot see the witness) is a thing the reviewer doesn't have to look for, and the compiler never overlooks it. We invested in making the structure express the safety properties wherever we could — sort-indexed enums, scheme as a sum, descriptor navigation as a sum.
- **Property tests over hand-rolled cases.** A randomized witness-monotonicity test catches a class of error a hand-rolled list of cases does not. Same for the source-roundtrip property over 500 admitted terms.
- **Negative tests carry their weight.** Every "X is rejected" assertion is worth as much as the positive ones, because the easiest AI-codegen failure mode is silently accepting input that should be rejected.

## Running the verification

```
# Full lib suite — 247 tests, including everything above.
cargo test --features dep16

# Calculus-only (parse, eval, admission, modify, codec, modification, secp).
cargo test --features dep16 --lib calculus::

# The witness-monotonicity property test specifically.
cargo test --features dep16 --lib calculus::tests::monotonicity

# Real-crypto tests (ECDSA + Schnorr through bitcoin::secp256k1).
cargo test --features dep16 --lib calculus::secp_tests

# Fuzz a target locally (requires `cargo install honggfuzz`).
cd fuzz && cargo hfuzz run dep16_parse
cd fuzz && cargo hfuzz run dep16_decode_descriptor
cd fuzz && cargo hfuzz run dep16_decode_fraud_proof
```

When in doubt, the test suite is the executable specification.
