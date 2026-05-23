# rust-miniscript + dep-16 calculus

An extension of [rust-miniscript](https://github.com/rust-bitcoin/rust-miniscript) that implements **dep-16**, a monotone term calculus for ledger-based deposit authorization, and **dep-17**, its canonical encodings. The upstream library is preserved unchanged — the upstream README is at [`README.upstream.md`](README.upstream.md) — and the new work lives in [`src/calculus/`](src/calculus/) behind the `dep16` cargo feature. Built on the upstream crate by Andrew Poelstra, Sanket Kanjalkar, and contributors.

## What it is

In Bitcoin, miniscript describes *spend* authorization compiled to Script and evaluated against a witness stack. dep-16 generalizes that model to a ledger / account setting: a deposit is an account with state (balance, descriptor, history), and the descriptor authorizes **any** operation against the account — spending, modifying the descriptor itself, accepting an incoming payment, updating metadata — by evaluating a closed term against `(operation, ledger-state, witness)`.

Key properties:

- **Witness-monotone by construction.** A single static placement rule — proof obligations only in positive position — guarantees that acquiring additional capabilities (a signature, a preimage) never revokes authority. Checked at deposit-open and re-checked after every modification.
- **Self-modifying.** A descriptor can authorize changes to itself, including ones that *expand* authority (social recovery, key rotation) — patterns that capability-narrowing systems cannot express.
- **Strict and total.** Evaluation is a typed fold over a fixed term with no recursion, no search, no fixpoint; cost is bounded in the term and operation size.
- **Deterministic fraud proofs.** Every operation produces the same fraud-proof shape; replay is bit-identical given dep-17's canonical encodings, with full canonical rejection on decode.
- **Real crypto, generic surface.** ECDSA and BIP-340 Schnorr verifiers ride a `Verifier` trait, so the calculus stays generic over the key type. `bitcoin::PublicKey` and `XOnlyPublicKey` both work.

The formal calculus, monotonicity theorem, and reflexivity argument live in the dep documents (a separate repo). The implementation plan is in [`PLAN.md`](PLAN.md).

## Example descriptors

**Social recovery** — guardians may rotate the owner's key after a long inactivity window. Authority *expands* under the recovery branch, which capability-narrowing systems cannot express:

```
with(owner = K1, guardians = [G1, G2, G3], in match(operation_type(),
  branch(spend, prove(pk(owner))),
  branch(replace, or(
    prove(pk(owner)),
    and(
      prove(pk_threshold(2, guardians)),
      blocks_since_activity_at_least(4320),
      cmp(=, operation_path(), path(0))
    )
  )),
  branch(else, false)
))
```

**Liana (decaying multisig)** — 2-of-2 primary path, single-key recovery that becomes spendable after a span of inactivity (`older` reads blocks-since-activity in the ledger model, so the recovery timer resets on every spend — the same intent as Bitcoin CSV):

```
with(primary_a = K1, primary_b = K2, recovery = K3, in match(operation_type(),
  branch(spend, or(
    and(prove(pk(primary_a)), prove(pk(primary_b))),
    and(prove(pk(recovery)), older(65535))
  )),
  branch(else, false)
))
```

**Linear vesting** — the beneficiary may withdraw only up to the linearly-vested fraction of an allocation, with cumulative withdrawals bounded by `vested = allocation · min(elapsed, vesting_blocks) / vesting_blocks`:

```
with(beneficiary = K1, allocation = 1000000, vesting_blocks = 52560,
  in match(operation_type(),
    branch(spend, and(
      prove(pk(beneficiary)),
      cmp(<=,
        add(cumulative_spent_via(path(0)), operation_arg(amount)),
        div(mul(allocation, min(blocks_since_open(), vesting_blocks)), vesting_blocks)
      )
    )),
    branch(else, false)
  ))
```

More templates — spending rate limit, inheritance, dead-man's-switch keyed on incoming payments, cliff vesting — live in [`src/calculus/tests.rs`](src/calculus/tests.rs) under the `templates` and `ledger_primitives` modules, each as a documented descriptor with behavior tests.

## Running it

The calculus is gated on the `dep16` feature; the default build is unchanged upstream miniscript.

```
# The calculus suite (parse, eval, admission, modification, codec, real ECDSA + Schnorr).
cargo test --features dep16 --lib calculus::

# Just the worked wallet templates.
cargo test --features dep16 --lib templates::

# The witness-monotonicity property test (500 adversarial terms through admission).
cargo test --features dep16 --lib monotonicity::

# The fraud-proof bundle round-trip and adjudication.
cargo test --features dep16 --lib fraud_bundle::

# The full library suite.
cargo test --features dep16

# Default build — only the upstream miniscript code is compiled.
cargo build
```

There are no example binaries yet; the test modules are written to double as worked documentation — each template is a short, readable descriptor with the scenarios it authorizes and rejects.

## Module map

```
src/calculus/
  ast            sort-indexed AST (BTerm / VTerm / Obligation)
  parse          combinator surface + with(=) + [list] + hash/bytes literals
  eval           strict total fold to a verdict
  admission      polarity + capability + var-resolution checks
  modify         insert / replace / delete -> T' + re-admission
  encode         dep-17 byte encoding + descriptor_id + canonical decoder
  fraud          replay and the self-contained FraudProof bundle
  host           Operation / LedgerState traits + OperationData
  witness        keyed Witness bundle
  signature      Verifier trait
  secp           EcdsaVerifier + SchnorrVerifier (BIP-340)
  snapshot       concrete LedgerState carried by a FraudProof
  capability     CapabilitySet (operator-declared primitives)
  schema         attestation schemas
  registry       value functions, state predicates, comparison ops
  value          Value enum + saturating arithmetic
  tests          integration tests (worked examples, templates, codec)
```

The upstream miniscript implementation is untouched — descriptors that compile to Bitcoin Script work exactly as before. The calculus adds a parallel evaluator for the off-chain ledger model, sharing only `MiniscriptKey`, the hash primitives, and the existing key serializations.

## License

CC0-1.0, the same as upstream.
