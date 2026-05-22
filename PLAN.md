# Implementation plan: dep-16 term calculus

This plan implements the authorization calculus specified in `PAPER.md` (formal
semantics) and dep-16 / `PROJECT3.md` (implementation spec). It is a **new evaluator**
that reuses three pieces of rust-miniscript and ignores the rest.

## What we reuse, what we don't

| from rust-miniscript | use |
|---|---|
| `expression::Tree` (`src/expression/`) | combinator nesting parses for free; we add surgery for `with(=)`, `[lists]`, unit literals |
| `MiniscriptKey` + `Sha256`/`Hash256`/`Ripemd160`/`Hash160` assoc types | the `Pk` type parameter and hash tagging |
| `Threshold` (`src/primitives/threshold.rs`) | `thresh` / `pk_threshold` |
| `AbsLockTime` / `RelLockTime` | `older` / `after` state predicates |
| Script compiler, `miniscript/types/`, `interpreter/`, `psbt/`, `satisfy.rs`, `descriptor/` | **not used** — Script infrastructure |

The calculus never compiles to Bitcoin Script. This evaluator is the only evaluator.

## Module layout

New tree `src/calculus/`, behind a `dep16` cargo feature.

```
src/calculus/
  mod.rs        re-exports, module docs, the feature gate
  ast.rs        BTerm / VTerm / Obligation  (sort-indexed AST), Literal
  value.rs      Value, saturating bounded-int arithmetic
  registry.rs   CmpOp, ValueFn, StatePred, Symbol/ArgName, capability identifiers
  parse.rs      expression::Tree -> AST; with(...), lists, literals
  host.rs       Operation + LedgerState traits (the host interface)
  witness.rs    keyed Witness bundle + the pk_h key-hash index
  schema.rs     attestation Schema + satisfies()
  eval.rs       eval_b / eval_v / eval_state / verify_o
  admission.rs  polarity + capability checks
  modify.rs     insert/replace/delete -> T', re-admission
  encode.rs     canonical encoding trait (stub for now)
  fraud.rs      replay
```

## Two design decisions that carry the invariants into the type system

**1. Sort-indexed AST.** `B`, `V`, `O` are three separate Rust enums. The calculus's
sort discipline — "`prove` cannot appear in a `V` position" — is then enforced by Rust
at construction time; ill-sorted terms are unrepresentable. `Cmp`/`State`/`Match`-scrutinee
hold `VTerm`, which structurally cannot contain `Prove`, so the polarity walk only handles
`Not` and the `If`-condition (the two non-vacuous cases in `PAPER.md` §2.4).

**2. m-constancy in the function signatures.** The monotonicity proof rests on "`prove`
is the only `m`-dependent construct." We mirror that by **not passing the witness** to the
value/state evaluators:

```rust
fn eval_v(t: &VTerm<Pk>, env: &Env<Pk>, op: &dyn Operation, st: &dyn LedgerState) -> Value<Pk>;
fn eval_state(p: StatePred, args: &[Value<Pk>], op: &dyn Operation, st: &dyn LedgerState) -> bool;
fn verify_o(o: &Obligation<Pk>, w: &Witness<Pk>, op: &dyn Operation, st: &dyn LedgerState) -> bool;
fn eval_b(t: &BTerm<Pk>, env: &Env<Pk>, op: &dyn Operation, st: &dyn LedgerState, w: &Witness<Pk>) -> bool;
```

`eval_v`/`eval_state` literally cannot read the witness — m-constancy is a compile-time
fact. `verify_o` is the only entry point for `m`. (It still takes `st`: signature expiry is
checked against current height, which is fine — monotonicity is over `m` with `(w,s)` fixed.)

## Core types (sketch)

```rust
pub enum BTerm<Pk: MiniscriptKey> {
    And(Vec<BTerm<Pk>>),
    Or(Vec<BTerm<Pk>>),
    Thresh(usize, Vec<BTerm<Pk>>),
    Not(Box<BTerm<Pk>>),
    If(Box<BTerm<Pk>>, Box<BTerm<Pk>>, Box<BTerm<Pk>>),
    Match { scrutinee: VTerm<Pk>, arms: Vec<(Symbol, BTerm<Pk>)>, default: Box<BTerm<Pk>> },
    Cmp(CmpOp, VTerm<Pk>, VTerm<Pk>),
    State(StatePred, Vec<VTerm<Pk>>),
    Prove(Obligation<Pk>),
}
pub enum VTerm<Pk: MiniscriptKey> { Lit(Literal<Pk>), Var(String), Op(ValueFn, Vec<VTerm<Pk>>) }
pub enum Obligation<Pk: MiniscriptKey> {
    Pk(VTerm<Pk>), PkH(VTerm<Pk>), PkAny(VTerm<Pk>), PkThreshold(usize, VTerm<Pk>),
    Hashlock(VTerm<Pk>), Attest(VTerm<Pk>, Schema),
}
pub enum Value<Pk: MiniscriptKey> {
    Int(i128), Key(Pk), Hash(HashValue), Path(Vec<usize>),
    Subtree(Box<BTerm<Pk>>), List(Vec<Value<Pk>>), Symbol(Symbol),
}
pub struct Witness<Pk: MiniscriptKey> {
    signatures: BTreeMap<Pk, OpSignature>,       // keyed by full key
    preimages: BTreeMap<HashValue, Vec<u8>>,
    attestations: BTreeMap<Pk, Attestation>,
    // plus a hash160(key) -> key index built at construction, for pk_h lookup
}
```

## Decisions folded in from the review

- **`pk_h`** is a real `Obligation` variant. Since signatures are keyed by full key and the
  node holds only `H = hash(K)`, discharge uses a `hash160(key) -> key` index built with the
  witness (O(1), not a scan). This works only because the witness reveals full keys; documented.
- **`attest` schemas** are a concrete `Schema` type with a `satisfies()` relation. v1 keeps the
  schema set tiny (e.g. `PriceWithinBps`) and capability-gated.
- **lists/sets** are first-class `Value::List` / `Literal::List`; `pk_threshold` dedups when counting.
- **boolean connectives are always-on**, never capability-gated. The capability scan only walks
  `ValueFn` / `StatePred` / `Obligation` / operation-type nodes.
- **cost** is operator-local policy, not a protocol admission check (admission is
  operation-independent and cannot see `|w|`). Admission runs exactly two checks: polarity
  and capability.

## Admission

```rust
fn check_polarity(t: &BTerm<Pk>, positive: bool) -> Result<(), Reject> {
    match t {
        Prove(_) if !positive => Err(Reject::NegativeProof),
        Prove(_) => Ok(()),
        Not(b) => check_polarity(b, false),                 // poison, not parity-flip
        If(c, then_, els) => { check_polarity(c, false)?;
                               check_polarity(then_, positive)?;
                               check_polarity(els, positive) }
        And(bs) | Or(bs) | Thresh(_, bs) => bs.iter().try_for_each(|b| check_polarity(b, positive)),
        Match { arms, default, .. } => { for (_, b) in arms { check_polarity(b, positive)? }
                                         check_polarity(default, positive) }
        Cmp(..) | State(..) => Ok(()),  // VTerm children: no Prove possible
    }
}
```

Both checks are linear, syntactic, and run pre-evaluation at deposit-open and after each
modification.

## Phasing — each milestone independently testable

0. **AST + value types + parser.** Round-trip parse/display tests.
1. **Evaluator + mock host.** `eval_b/v/state`, `prove` against a stub verifier. Run the
   allowance-with-recovery example to a verdict.
2. **Admission.** Polarity + capability, with a battery of polarity-rejection cases.
3. **Real signatures.** secp verification of `OpSignature` over `Operation::canonical_encoding`,
   the `pk_h` index, hashlocks.
4. **AST ops + modification.** `ast_ref`/`subtree_at`/`operation_subtree`, `insert/replace/delete`
   producing `T'`, re-admission. Run the guardian-rotation example end-to-end.
5. **Canonical encoding + fraud replay + determinism fixtures.**

## Testing

- The three worked examples (allowance, oracle rebalance, guardian rotation) as integration tests.
- Polarity-rejection suite.
- **Property test for the monotonicity theorem (PAPER.md §3.1):** generate admitted terms,
  evaluate under random `(w, s, m)`, then under `m' ⊇ m`, assert `accept(m) ⟹ accept(m')`. This
  is the single highest-value test — it exercises the polarity checker and evaluator against the
  one security claim.
- Determinism golden vectors `(T, w, s, m) -> verdict`, shared across implementations once the canonical encodings are fixed.
- Fuzz the parser and `eval` (reuse the `fuzz/` harness style).

## First step

Phase 0 plus a slice of Phase 1: the sort-indexed AST, the parser over `expression::Tree`, a
mock host, and the allowance example evaluating to a verdict as a test. This exercises the whole
spine (sorts, parsing, `eval_b/v`, witness lookup) without secp, modification, or encodings.
