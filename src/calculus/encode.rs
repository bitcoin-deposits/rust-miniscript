// SPDX-License-Identifier: CC0-1.0

//! Canonical encodings (dep-17).
//!
//! Two encodings live here. [`to_string`] is the canonical *source* form (round-trips through the
//! parser). The byte encodings below are the dep-17 canonical form: tagged, length-prefixed,
//! fixed-width-integer, used for the descriptor commitment ([`descriptor_id`]) and the operation
//! signing preimage ([`operation_preimage`] / [`operation_sighash`]). They are what makes dep-16's
//! determinism and signature-binding claims unconditional.
//!
//! Integers are big-endian: ledger `int` is 16-byte two's complement, counts/lengths/heights are
//! `u32`, nonces `u64`. Byte strings and lists are length/count prefixed. Capability-gated
//! primitive ids are `u16`; fixed structural tags are `u8`.

use core::fmt::Display;

use crate::prelude::*;
use crate::MiniscriptKey;

use super::ast::{BTerm, Descriptor, Obligation, VTerm};
use super::host::Operation;
use super::registry::{CmpOp, StatePred, ValueFn};
use super::schema::Schema;
use super::value::{HashValue, Value};

/// A key type that has a fixed canonical byte serialization, required to encode values and
/// descriptors. Implemented for `bitcoin::PublicKey` (33-byte compressed) here; test key types
/// implement it alongside their use.
pub trait CanonicalKey {
    /// The canonical bytes of this key.
    fn to_canonical_bytes(&self) -> Vec<u8>;
}

impl CanonicalKey for bitcoin::PublicKey {
    fn to_canonical_bytes(&self) -> Vec<u8> { self.inner.serialize().to_vec() }
}

/// The BIP-340 tagged hash `SHA256(SHA256(tag) || SHA256(tag) || msg)`.
pub fn tagged_hash(tag: &str, msg: &[u8]) -> [u8; 32] {
    use bitcoin::hashes::{sha256, Hash as _};
    let t = sha256::Hash::hash(tag.as_bytes());
    let mut data = Vec::with_capacity(64 + msg.len());
    data.extend_from_slice(t.as_byte_array());
    data.extend_from_slice(t.as_byte_array());
    data.extend_from_slice(msg);
    sha256::Hash::hash(&data).to_byte_array()
}

/// The canonical source form of a descriptor.
pub fn to_string<Pk: MiniscriptKey + Display>(d: &Descriptor<Pk>) -> String {
    let mut out = String::new();
    if d.constants.is_empty() {
        write_b(&mut out, &d.body);
    } else {
        out.push_str("with(");
        for (name, value) in &d.constants {
            out.push_str(name);
            out.push_str(" = ");
            write_value(&mut out, value);
            out.push_str(", ");
        }
        out.push_str("in ");
        write_b(&mut out, &d.body);
        out.push(')');
    }
    out
}

fn write_list<T>(out: &mut String, items: &[T], mut each: impl FnMut(&mut String, &T)) {
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        each(out, item);
    }
}

fn write_b<Pk: MiniscriptKey + Display>(out: &mut String, t: &BTerm<Pk>) {
    match t {
        BTerm::Const(b) => out.push_str(if *b { "true" } else { "false" }),
        BTerm::And(bs) => {
            out.push_str("and(");
            write_list(out, bs, write_b);
            out.push(')');
        }
        BTerm::Or(bs) => {
            out.push_str("or(");
            write_list(out, bs, write_b);
            out.push(')');
        }
        BTerm::Thresh(k, bs) => {
            out.push_str("thresh(");
            out.push_str(&k.to_string());
            for b in bs {
                out.push_str(", ");
                write_b(out, b);
            }
            out.push(')');
        }
        BTerm::Not(b) => {
            out.push_str("not(");
            write_b(out, b);
            out.push(')');
        }
        BTerm::If(c, t1, e) => {
            out.push_str("if(");
            write_b(out, c);
            out.push_str(", ");
            write_b(out, t1);
            out.push_str(", ");
            write_b(out, e);
            out.push(')');
        }
        BTerm::Match { scrutinee, arms, default } => {
            out.push_str("match(");
            write_v(out, scrutinee);
            for (tag, body) in arms {
                out.push_str(", branch(");
                out.push_str(tag.as_str());
                out.push_str(", ");
                write_b(out, body);
                out.push(')');
            }
            out.push_str(", branch(else, ");
            write_b(out, default);
            out.push_str("))");
        }
        BTerm::Cmp(op, a, b) => {
            out.push_str("cmp(");
            out.push_str(op.name());
            out.push_str(", ");
            write_v(out, a);
            out.push_str(", ");
            write_v(out, b);
            out.push(')');
        }
        BTerm::State(p, args) => {
            out.push_str(p.name());
            out.push('(');
            write_list(out, args, write_v);
            out.push(')');
        }
        BTerm::Prove(o) => {
            out.push_str("prove(");
            write_o(out, o);
            out.push(')');
        }
    }
}

fn write_o<Pk: MiniscriptKey + Display>(out: &mut String, o: &Obligation<Pk>) {
    match o {
        Obligation::Pk(v) => wrap(out, "pk", v),
        Obligation::PkH(v) => wrap(out, "pk_h", v),
        Obligation::PkAny(v) => wrap(out, "pk_any", v),
        Obligation::PkThreshold(k, v) => {
            out.push_str("pk_threshold(");
            out.push_str(&k.to_string());
            out.push_str(", ");
            write_v(out, v);
            out.push(')');
        }
        Obligation::Hashlock(v) => wrap(out, "hashlock", v),
        Obligation::Attest(v, schema) => {
            out.push_str("attest(");
            write_v(out, v);
            out.push_str(", ");
            write_schema(out, schema);
            out.push(')');
        }
    }
}

fn wrap<Pk: MiniscriptKey + Display>(out: &mut String, name: &str, v: &VTerm<Pk>) {
    out.push_str(name);
    out.push('(');
    write_v(out, v);
    out.push(')');
}

fn write_schema(out: &mut String, schema: &Schema) {
    match schema {
        Schema::PriceWithinBps { tolerance_bps } => {
            out.push_str("price_schema(");
            out.push_str(&tolerance_bps.to_string());
            out.push(')');
        }
    }
}

fn write_v<Pk: MiniscriptKey + Display>(out: &mut String, t: &VTerm<Pk>) {
    match t {
        VTerm::Lit(v) => write_value(out, v),
        VTerm::Var(name) => out.push_str(name),
        VTerm::Op(f, args) => {
            out.push_str(f.name());
            out.push('(');
            write_list(out, args, write_v);
            out.push(')');
        }
    }
}

fn write_value<Pk: MiniscriptKey + Display>(out: &mut String, v: &Value<Pk>) {
    match v {
        Value::Int(n) => out.push_str(&n.to_string()),
        Value::Key(k) => out.push_str(&k.to_string()),
        Value::Symbol(s) => out.push_str(s.as_str()),
        Value::Bytes(b) => {
            out.push_str("0x");
            for byte in b {
                out.push_str(&format!("{:02x}", byte));
            }
        }
        Value::Hash(h) => write_hash(out, h),
        Value::Path(p) => {
            out.push_str("path(");
            write_list(out, p, |o, i| o.push_str(&i.to_string()));
            out.push(')');
        }
        Value::List(items) => {
            out.push('[');
            write_list(out, items, write_value);
            out.push(']');
        }
        Value::Subtree(b) => write_b(out, b),
    }
}

fn write_hash(out: &mut String, h: &HashValue) {
    let (tag, bytes): (&str, &[u8]) = match h {
        HashValue::Sha256(d) => ("sha256", d),
        HashValue::Hash256(d) => ("hash256", d),
        HashValue::Ripemd160(d) => ("ripemd160", d),
        HashValue::Hash160(d) => ("hash160", d),
    };
    out.push_str(tag);
    out.push_str(":0x");
    for byte in bytes {
        out.push_str(&format!("{:02x}", byte));
    }
}

// ----------------------------------------------------------------------------------------------
// dep-17 byte encoding
// ----------------------------------------------------------------------------------------------

fn put_u32(out: &mut Vec<u8>, n: u32) { out.extend_from_slice(&n.to_be_bytes()); }
fn put_u16(out: &mut Vec<u8>, n: u16) { out.extend_from_slice(&n.to_be_bytes()); }
fn put_int(out: &mut Vec<u8>, n: i128) { out.extend_from_slice(&n.to_be_bytes()); }
fn put_bytes(out: &mut Vec<u8>, b: &[u8]) {
    put_u32(out, b.len() as u32);
    out.extend_from_slice(b);
}

// Stable primitive ids (the dep-17 registry). Assigned in declaration order; never reused.
fn cmpop_id(o: CmpOp) -> u8 {
    match o {
        CmpOp::Eq => 0,
        CmpOp::Lt => 1,
        CmpOp::Le => 2,
        CmpOp::Gt => 3,
        CmpOp::Ge => 4,
    }
}

fn valuefn_id(f: ValueFn) -> u16 {
    match f {
        ValueFn::Add => 0,
        ValueFn::Sub => 1,
        ValueFn::Mul => 2,
        ValueFn::Div => 3,
        ValueFn::Min => 4,
        ValueFn::Max => 5,
        ValueFn::Pct => 6,
        ValueFn::Bps => 7,
        ValueFn::OperationType => 8,
        ValueFn::OperationArg => 9,
        ValueFn::OperationPath => 10,
        ValueFn::OperationSubtree => 11,
        ValueFn::BlocksSinceActivity => 12,
        ValueFn::BlocksSinceOpen => 13,
        ValueFn::DepositBalance => 14,
        ValueFn::RollingWindow => 15,
        ValueFn::CumulativeSpentVia => 16,
        ValueFn::AstRef => 17,
        ValueFn::AstShapeAt => 18,
        ValueFn::Path => 19,
    }
}

fn statepred_id(p: StatePred) -> u16 {
    match p {
        StatePred::Older => 0,
        StatePred::After => 1,
        StatePred::AmountAtMost => 2,
        StatePred::AmountInRange => 3,
        StatePred::AmountAtMostPct => 4,
        StatePred::DestinationIs => 5,
        StatePred::DestinationIn => 6,
        StatePred::BalanceAtLeast => 7,
        StatePred::BalanceAtMost => 8,
        StatePred::BlocksSinceActivityAtLeast => 9,
        StatePred::BlocksSinceOpenBelow => 10,
        StatePred::RollingAmountBelow => 11,
        StatePred::RollingAmountBelowPct => 12,
        StatePred::SubtreeAt => 13,
    }
}

fn put_value<Pk: MiniscriptKey + CanonicalKey>(out: &mut Vec<u8>, v: &Value<Pk>) {
    match v {
        Value::Int(n) => {
            out.push(0x00);
            put_int(out, *n);
        }
        Value::Key(k) => {
            out.push(0x01);
            put_bytes(out, &k.to_canonical_bytes());
        }
        Value::Hash(h) => {
            out.push(0x02);
            put_hash(out, h);
        }
        Value::Bytes(b) => {
            out.push(0x03);
            put_bytes(out, b);
        }
        Value::Path(p) => {
            out.push(0x04);
            put_u32(out, p.len() as u32);
            for i in p {
                put_u32(out, *i as u32);
            }
        }
        Value::List(items) => {
            out.push(0x05);
            put_u32(out, items.len() as u32);
            for it in items {
                put_value(out, it);
            }
        }
        Value::Symbol(s) => {
            out.push(0x06);
            put_bytes(out, s.as_str().as_bytes());
        }
        Value::Subtree(b) => {
            out.push(0x07);
            put_term(out, b);
        }
    }
}

fn put_hash(out: &mut Vec<u8>, h: &HashValue) {
    match h {
        HashValue::Sha256(d) => {
            out.push(0x00);
            out.extend_from_slice(d);
        }
        HashValue::Hash256(d) => {
            out.push(0x01);
            out.extend_from_slice(d);
        }
        HashValue::Ripemd160(d) => {
            out.push(0x02);
            out.extend_from_slice(d);
        }
        HashValue::Hash160(d) => {
            out.push(0x03);
            out.extend_from_slice(d);
        }
    }
}

fn put_term<Pk: MiniscriptKey + CanonicalKey>(out: &mut Vec<u8>, t: &BTerm<Pk>) {
    match t {
        BTerm::Const(b) => {
            out.push(0x00);
            out.push(if *b { 1 } else { 0 });
        }
        BTerm::And(bs) => {
            out.push(0x01);
            put_term_list(out, bs);
        }
        BTerm::Or(bs) => {
            out.push(0x02);
            put_term_list(out, bs);
        }
        BTerm::Thresh(k, bs) => {
            out.push(0x03);
            put_u32(out, *k as u32);
            put_term_list(out, bs);
        }
        BTerm::Not(b) => {
            out.push(0x04);
            put_term(out, b);
        }
        BTerm::If(c, t1, e) => {
            out.push(0x05);
            put_term(out, c);
            put_term(out, t1);
            put_term(out, e);
        }
        BTerm::Match { scrutinee, arms, default } => {
            out.push(0x06);
            put_vterm(out, scrutinee);
            put_u32(out, arms.len() as u32);
            for (tag, body) in arms {
                put_bytes(out, tag.as_str().as_bytes());
                put_term(out, body);
            }
            put_term(out, default);
        }
        BTerm::Cmp(op, a, b) => {
            out.push(0x07);
            out.push(cmpop_id(*op));
            put_vterm(out, a);
            put_vterm(out, b);
        }
        BTerm::State(p, args) => {
            out.push(0x08);
            put_u16(out, statepred_id(*p));
            put_u32(out, args.len() as u32);
            for a in args {
                put_vterm(out, a);
            }
        }
        BTerm::Prove(o) => {
            out.push(0x09);
            put_obligation(out, o);
        }
    }
}

fn put_term_list<Pk: MiniscriptKey + CanonicalKey>(out: &mut Vec<u8>, bs: &[BTerm<Pk>]) {
    put_u32(out, bs.len() as u32);
    for b in bs {
        put_term(out, b);
    }
}

fn put_vterm<Pk: MiniscriptKey + CanonicalKey>(out: &mut Vec<u8>, t: &VTerm<Pk>) {
    match t {
        VTerm::Lit(v) => {
            out.push(0x00);
            put_value(out, v);
        }
        VTerm::Var(name) => {
            out.push(0x01);
            put_bytes(out, name.as_bytes());
        }
        VTerm::Op(f, args) => {
            out.push(0x02);
            put_u16(out, valuefn_id(*f));
            put_u32(out, args.len() as u32);
            for a in args {
                put_vterm(out, a);
            }
        }
    }
}

fn put_obligation<Pk: MiniscriptKey + CanonicalKey>(out: &mut Vec<u8>, o: &Obligation<Pk>) {
    match o {
        Obligation::Pk(v) => {
            put_u16(out, 0x0000);
            put_vterm(out, v);
        }
        Obligation::PkH(v) => {
            put_u16(out, 0x0001);
            put_vterm(out, v);
        }
        Obligation::PkAny(v) => {
            put_u16(out, 0x0002);
            put_vterm(out, v);
        }
        Obligation::PkThreshold(k, v) => {
            put_u16(out, 0x0003);
            put_u32(out, *k as u32);
            put_vterm(out, v);
        }
        Obligation::Hashlock(v) => {
            put_u16(out, 0x0004);
            put_vterm(out, v);
        }
        Obligation::Attest(v, schema) => {
            put_u16(out, 0x0005);
            put_vterm(out, v);
            put_schema(out, schema);
        }
    }
}

fn put_schema(out: &mut Vec<u8>, schema: &Schema) {
    match schema {
        Schema::PriceWithinBps { tolerance_bps } => {
            put_u16(out, 0x0000);
            put_u32(out, *tolerance_bps);
        }
    }
}

/// The dep-17 canonical byte encoding of a descriptor.
pub fn encode_descriptor<Pk: MiniscriptKey + CanonicalKey>(d: &Descriptor<Pk>) -> Vec<u8> {
    let mut out = vec![0x01]; // version
    put_u32(&mut out, d.constants.len() as u32);
    // BTreeMap iterates in sorted key order, giving the required canonical order.
    for (name, value) in &d.constants {
        put_bytes(&mut out, name.as_bytes());
        put_value(&mut out, value);
    }
    put_term(&mut out, &d.body);
    out
}

/// The descriptor commitment: `tagged_hash("dep17/descriptor", encode_descriptor(d))`.
pub fn descriptor_id<Pk: MiniscriptKey + CanonicalKey>(d: &Descriptor<Pk>) -> [u8; 32] {
    tagged_hash("dep17/descriptor", &encode_descriptor(d))
}

/// The canonical operation preimage: the bytes a signature over the operation commits to. Binds
/// the deposit, the operation type and arguments, the nonce, and the expiry.
pub fn operation_preimage<Pk, O>(op: &O) -> Vec<u8>
where
    Pk: MiniscriptKey + CanonicalKey,
    O: Operation<Pk>,
{
    let mut out = vec![0x01]; // version
    out.extend_from_slice(&op.deposit_id());
    put_bytes(&mut out, op.op_type().as_str().as_bytes());
    let mut args = op.args();
    args.sort_by(|a, b| a.0.cmp(&b.0));
    put_u32(&mut out, args.len() as u32);
    for (name, value) in &args {
        put_bytes(&mut out, name.as_bytes());
        put_value(&mut out, value);
    }
    out.extend_from_slice(&op.nonce().to_be_bytes());
    out.extend_from_slice(&op.expiry().to_be_bytes());
    out
}

/// The operation signing hash: `tagged_hash("dep17/operation", operation_preimage)`. This is the
/// 32-byte digest a signature is verified against.
pub fn operation_sighash(preimage: &[u8]) -> [u8; 32] {
    tagged_hash("dep17/operation", preimage)
}
