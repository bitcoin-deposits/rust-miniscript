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
use super::registry::{CmpOp, StatePred, Symbol, ValueFn};
use super::schema::Schema;
use super::value::{HashValue, Value};

/// A key type that has a fixed canonical byte serialization, required to encode and decode values
/// and descriptors. Implemented for `bitcoin::PublicKey` (33-byte compressed) here; test key types
/// implement it alongside their use.
pub trait CanonicalKey: Sized {
    /// The canonical bytes of this key.
    fn to_canonical_bytes(&self) -> Vec<u8>;

    /// Parse a key from its canonical bytes, rejecting any non-canonical encoding.
    fn from_canonical_bytes(bytes: &[u8]) -> Option<Self>;
}

impl CanonicalKey for bitcoin::PublicKey {
    fn to_canonical_bytes(&self) -> Vec<u8> { self.inner.serialize().to_vec() }

    fn from_canonical_bytes(bytes: &[u8]) -> Option<Self> {
        // Canonical form is the 33-byte compressed serialization; reject anything else.
        if bytes.len() != 33 {
            return None;
        }
        bitcoin::secp256k1::PublicKey::from_slice(bytes).ok().map(bitcoin::PublicKey::new)
    }
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

/// Decode an operation from its canonical preimage encoding (the inverse of
/// [`operation_preimage`]), rejecting non-canonical input. The result is an
/// [`OperationData`](super::host::OperationData), the concrete transmittable operation.
pub fn decode_operation<Pk: MiniscriptKey + CanonicalKey>(
    buf: &[u8],
) -> Result<super::host::OperationData<Pk>, DecodeError> {
    let mut d = Decoder::new(buf);
    let version = d.u8()?;
    if version != 0x01 {
        return Err(DecodeError::BadVersion(version));
    }
    let mut deposit_id = [0u8; 32];
    deposit_id.copy_from_slice(d.take(32)?);
    let op_type = Symbol::new(d.symbol()?);
    let n = d.u32()?;
    let mut args = BTreeMap::new();
    let mut prev: Option<String> = None;
    for _ in 0..n {
        let name = d.symbol()?;
        if !is_canonical_name(&name) {
            return Err(DecodeError::InvalidName);
        }
        if let Some(prev) = &prev {
            if &name <= prev {
                return Err(DecodeError::NonCanonicalOrder);
            }
        }
        let value = dec_value(&mut d)?;
        prev = Some(name.clone());
        args.insert(name, value);
    }
    let nonce = d.u64()?;
    let expiry = d.u32()?;
    d.finish()?;
    Ok(super::host::OperationData { op_type, args, deposit_id, nonce, expiry })
}

// ----------------------------------------------------------------------------------------------
// dep-17 decoding (with canonical rejection)
// ----------------------------------------------------------------------------------------------

/// A reason a byte string is not a valid canonical encoding.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum DecodeError {
    /// Input ended before the structure was complete.
    UnexpectedEof,
    /// Bytes remained after the structure was complete.
    TrailingBytes,
    /// An unsupported version byte.
    BadVersion(u8),
    /// An unknown type tag or primitive id (which axis, which id).
    UnknownTag(&'static str, u32),
    /// A boolean byte other than 0 or 1.
    NonCanonicalBool(u8),
    /// Constant names not strictly increasing (unsorted or duplicated).
    NonCanonicalOrder,
    /// A constant name that does not match `[a-z_][a-z0-9_]*`.
    InvalidName,
    /// A key that is not a canonical encoding of the key type.
    BadKey,
    /// A symbol or name that is not valid UTF-8.
    BadUtf8,
}

struct Decoder<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Decoder<'a> {
    fn new(buf: &'a [u8]) -> Self { Decoder { buf, pos: 0 } }

    fn take(&mut self, n: usize) -> Result<&'a [u8], DecodeError> {
        let end = self.pos.checked_add(n).ok_or(DecodeError::UnexpectedEof)?;
        if end > self.buf.len() {
            return Err(DecodeError::UnexpectedEof);
        }
        let slice = &self.buf[self.pos..end];
        self.pos = end;
        Ok(slice)
    }

    fn u8(&mut self) -> Result<u8, DecodeError> { Ok(self.take(1)?[0]) }

    fn u16(&mut self) -> Result<u16, DecodeError> {
        let b = self.take(2)?;
        Ok(u16::from_be_bytes([b[0], b[1]]))
    }

    fn u32(&mut self) -> Result<u32, DecodeError> {
        let b = self.take(4)?;
        Ok(u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
    }

    fn u64(&mut self) -> Result<u64, DecodeError> {
        let mut a = [0u8; 8];
        a.copy_from_slice(self.take(8)?);
        Ok(u64::from_be_bytes(a))
    }

    fn int(&mut self) -> Result<i128, DecodeError> {
        let mut a = [0u8; 16];
        a.copy_from_slice(self.take(16)?);
        Ok(i128::from_be_bytes(a))
    }

    fn bytes(&mut self) -> Result<Vec<u8>, DecodeError> {
        let n = self.u32()? as usize;
        Ok(self.take(n)?.to_vec())
    }

    fn boolean(&mut self) -> Result<bool, DecodeError> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            other => Err(DecodeError::NonCanonicalBool(other)),
        }
    }

    fn symbol(&mut self) -> Result<String, DecodeError> {
        String::from_utf8(self.bytes()?).map_err(|_| DecodeError::BadUtf8)
    }

    fn finish(self) -> Result<(), DecodeError> {
        if self.pos == self.buf.len() {
            Ok(())
        } else {
            Err(DecodeError::TrailingBytes)
        }
    }
}

fn cmpop_from_id(id: u8) -> Result<CmpOp, DecodeError> {
    Ok(match id {
        0 => CmpOp::Eq,
        1 => CmpOp::Lt,
        2 => CmpOp::Le,
        3 => CmpOp::Gt,
        4 => CmpOp::Ge,
        _ => return Err(DecodeError::UnknownTag("cmpop", id as u32)),
    })
}

fn valuefn_from_id(id: u16) -> Result<ValueFn, DecodeError> {
    Ok(match id {
        0 => ValueFn::Add,
        1 => ValueFn::Sub,
        2 => ValueFn::Mul,
        3 => ValueFn::Div,
        4 => ValueFn::Min,
        5 => ValueFn::Max,
        6 => ValueFn::Pct,
        7 => ValueFn::Bps,
        8 => ValueFn::OperationType,
        9 => ValueFn::OperationArg,
        10 => ValueFn::OperationPath,
        11 => ValueFn::OperationSubtree,
        12 => ValueFn::BlocksSinceActivity,
        13 => ValueFn::BlocksSinceOpen,
        14 => ValueFn::DepositBalance,
        15 => ValueFn::RollingWindow,
        16 => ValueFn::CumulativeSpentVia,
        17 => ValueFn::AstRef,
        18 => ValueFn::AstShapeAt,
        19 => ValueFn::Path,
        _ => return Err(DecodeError::UnknownTag("valuefn", id as u32)),
    })
}

fn statepred_from_id(id: u16) -> Result<StatePred, DecodeError> {
    Ok(match id {
        0 => StatePred::Older,
        1 => StatePred::After,
        2 => StatePred::AmountAtMost,
        3 => StatePred::AmountInRange,
        4 => StatePred::AmountAtMostPct,
        5 => StatePred::DestinationIs,
        6 => StatePred::DestinationIn,
        7 => StatePred::BalanceAtLeast,
        8 => StatePred::BalanceAtMost,
        9 => StatePred::BlocksSinceActivityAtLeast,
        10 => StatePred::BlocksSinceOpenBelow,
        11 => StatePred::RollingAmountBelow,
        12 => StatePred::RollingAmountBelowPct,
        13 => StatePred::SubtreeAt,
        _ => return Err(DecodeError::UnknownTag("statepred", id as u32)),
    })
}

fn dec_hash(d: &mut Decoder) -> Result<HashValue, DecodeError> {
    Ok(match d.u8()? {
        0x00 => {
            let mut a = [0u8; 32];
            a.copy_from_slice(d.take(32)?);
            HashValue::Sha256(a)
        }
        0x01 => {
            let mut a = [0u8; 32];
            a.copy_from_slice(d.take(32)?);
            HashValue::Hash256(a)
        }
        0x02 => {
            let mut a = [0u8; 20];
            a.copy_from_slice(d.take(20)?);
            HashValue::Ripemd160(a)
        }
        0x03 => {
            let mut a = [0u8; 20];
            a.copy_from_slice(d.take(20)?);
            HashValue::Hash160(a)
        }
        t => return Err(DecodeError::UnknownTag("hashfn", t as u32)),
    })
}

fn dec_value<Pk: MiniscriptKey + CanonicalKey>(d: &mut Decoder) -> Result<Value<Pk>, DecodeError> {
    Ok(match d.u8()? {
        0x00 => Value::Int(d.int()?),
        0x01 => {
            let b = d.bytes()?;
            Value::Key(Pk::from_canonical_bytes(&b).ok_or(DecodeError::BadKey)?)
        }
        0x02 => Value::Hash(dec_hash(d)?),
        0x03 => Value::Bytes(d.bytes()?),
        0x04 => {
            let n = d.u32()?;
            let mut p = Vec::with_capacity(n as usize);
            for _ in 0..n {
                p.push(d.u32()? as usize);
            }
            Value::Path(p)
        }
        0x05 => {
            let n = d.u32()?;
            let mut items = Vec::with_capacity(n as usize);
            for _ in 0..n {
                items.push(dec_value(d)?);
            }
            Value::List(items)
        }
        0x06 => Value::Symbol(Symbol::new(d.symbol()?)),
        0x07 => Value::Subtree(Box::new(dec_term(d)?)),
        t => return Err(DecodeError::UnknownTag("value", t as u32)),
    })
}

fn dec_term<Pk: MiniscriptKey + CanonicalKey>(d: &mut Decoder) -> Result<BTerm<Pk>, DecodeError> {
    Ok(match d.u8()? {
        0x00 => BTerm::Const(d.boolean()?),
        0x01 => BTerm::And(dec_term_list(d)?),
        0x02 => BTerm::Or(dec_term_list(d)?),
        0x03 => {
            let k = d.u32()? as usize;
            BTerm::Thresh(k, dec_term_list(d)?)
        }
        0x04 => BTerm::Not(Box::new(dec_term(d)?)),
        0x05 => BTerm::If(
            Box::new(dec_term(d)?),
            Box::new(dec_term(d)?),
            Box::new(dec_term(d)?),
        ),
        0x06 => {
            let scrutinee = dec_vterm(d)?;
            let n = d.u32()?;
            let mut arms = Vec::with_capacity(n as usize);
            for _ in 0..n {
                let tag = Symbol::new(d.symbol()?);
                arms.push((tag, dec_term(d)?));
            }
            let default = Box::new(dec_term(d)?);
            BTerm::Match { scrutinee, arms, default }
        }
        0x07 => {
            let op = cmpop_from_id(d.u8()?)?;
            BTerm::Cmp(op, dec_vterm(d)?, dec_vterm(d)?)
        }
        0x08 => {
            let p = statepred_from_id(d.u16()?)?;
            let n = d.u32()?;
            let mut args = Vec::with_capacity(n as usize);
            for _ in 0..n {
                args.push(dec_vterm(d)?);
            }
            BTerm::State(p, args)
        }
        0x09 => BTerm::Prove(dec_obligation(d)?),
        t => return Err(DecodeError::UnknownTag("node", t as u32)),
    })
}

fn dec_term_list<Pk: MiniscriptKey + CanonicalKey>(
    d: &mut Decoder,
) -> Result<Vec<BTerm<Pk>>, DecodeError> {
    let n = d.u32()?;
    let mut out = Vec::with_capacity(n as usize);
    for _ in 0..n {
        out.push(dec_term(d)?);
    }
    Ok(out)
}

fn dec_vterm<Pk: MiniscriptKey + CanonicalKey>(d: &mut Decoder) -> Result<VTerm<Pk>, DecodeError> {
    Ok(match d.u8()? {
        0x00 => VTerm::Lit(dec_value(d)?),
        0x01 => VTerm::Var(d.symbol()?),
        0x02 => {
            let f = valuefn_from_id(d.u16()?)?;
            let n = d.u32()?;
            let mut args = Vec::with_capacity(n as usize);
            for _ in 0..n {
                args.push(dec_vterm(d)?);
            }
            VTerm::Op(f, args)
        }
        t => return Err(DecodeError::UnknownTag("vterm", t as u32)),
    })
}

fn dec_obligation<Pk: MiniscriptKey + CanonicalKey>(
    d: &mut Decoder,
) -> Result<Obligation<Pk>, DecodeError> {
    Ok(match d.u16()? {
        0x0000 => Obligation::Pk(dec_vterm(d)?),
        0x0001 => Obligation::PkH(dec_vterm(d)?),
        0x0002 => Obligation::PkAny(dec_vterm(d)?),
        0x0003 => {
            let k = d.u32()? as usize;
            Obligation::PkThreshold(k, dec_vterm(d)?)
        }
        0x0004 => Obligation::Hashlock(dec_vterm(d)?),
        0x0005 => {
            let v = dec_vterm(d)?;
            Obligation::Attest(v, dec_schema(d)?)
        }
        t => return Err(DecodeError::UnknownTag("obligation", t as u32)),
    })
}

fn dec_schema(d: &mut Decoder) -> Result<Schema, DecodeError> {
    Ok(match d.u16()? {
        0x0000 => Schema::PriceWithinBps { tolerance_bps: d.u32()? },
        t => return Err(DecodeError::UnknownTag("schema", t as u32)),
    })
}

fn is_canonical_name(name: &str) -> bool {
    let mut chars = name.chars();
    match chars.next() {
        Some(c) if c == '_' || c.is_ascii_lowercase() => {}
        _ => return false,
    }
    chars.all(|c| c == '_' || c.is_ascii_lowercase() || c.is_ascii_digit())
}

/// Decode a descriptor from its dep-17 canonical encoding, rejecting any non-canonical input.
pub fn decode_descriptor<Pk: MiniscriptKey + CanonicalKey>(
    buf: &[u8],
) -> Result<Descriptor<Pk>, DecodeError> {
    let mut d = Decoder::new(buf);
    let version = d.u8()?;
    if version != 0x01 {
        return Err(DecodeError::BadVersion(version));
    }
    let n = d.u32()?;
    let mut constants = BTreeMap::new();
    let mut prev: Option<String> = None;
    for _ in 0..n {
        let name = d.symbol()?;
        if !is_canonical_name(&name) {
            return Err(DecodeError::InvalidName);
        }
        // Strictly increasing names enforce both sorted order and uniqueness.
        if let Some(prev) = &prev {
            if &name <= prev {
                return Err(DecodeError::NonCanonicalOrder);
            }
        }
        let value = dec_value(&mut d)?;
        prev = Some(name.clone());
        constants.insert(name, value);
    }
    let body = dec_term(&mut d)?;
    d.finish()?;
    Ok(Descriptor { constants, body })
}

// ----------------------------------------------------------------------------------------------
// dep-17 state-snapshot encoding
// ----------------------------------------------------------------------------------------------

fn rwfield_id(field: &str) -> Option<u8> {
    match field {
        "amount_out" => Some(0),
        "amount_in" => Some(1),
        "transfer_count" => Some(2),
        _ => None,
    }
}

fn rwfield_name(id: u8) -> Result<&'static str, DecodeError> {
    match id {
        0 => Ok("amount_out"),
        1 => Ok("amount_in"),
        2 => Ok("transfer_count"),
        _ => Err(DecodeError::UnknownTag("rwfield", id as u32)),
    }
}

/// The dep-17 canonical byte encoding of a ledger snapshot.
pub fn encode_snapshot(s: &super::snapshot::Snapshot) -> Vec<u8> {
    let mut out = vec![0x01]; // version
    put_int(&mut out, s.balance);
    put_u32(&mut out, s.blocks_since_activity);
    put_u32(&mut out, s.blocks_since_open);
    put_u32(&mut out, s.height);

    // Rolling windows, sorted by (field id, period). Entries with an unregistered field are
    // dropped: they can never be read (no value function names them) and have no canonical id.
    let mut rolling: Vec<(u8, u32, i128)> = s
        .rolling
        .iter()
        .filter_map(|((field, period), amount)| rwfield_id(field).map(|id| (id, *period, *amount)))
        .collect();
    rolling.sort_by(|a, b| (a.0, a.1).cmp(&(b.0, b.1)));
    put_u32(&mut out, rolling.len() as u32);
    for (field_id, period, amount) in &rolling {
        out.push(*field_id);
        put_u32(&mut out, *period);
        put_int(&mut out, *amount);
    }

    // Cumulative spend, sorted by path (BTreeMap iterates in path order).
    put_u32(&mut out, s.cumulative_spent.len() as u32);
    for (path, amount) in &s.cumulative_spent {
        put_u32(&mut out, path.len() as u32);
        for i in path {
            put_u32(&mut out, *i as u32);
        }
        put_int(&mut out, *amount);
    }
    out
}

/// The snapshot commitment: `tagged_hash("dep17/snapshot", encode_snapshot(s))`.
pub fn snapshot_id(s: &super::snapshot::Snapshot) -> [u8; 32] {
    tagged_hash("dep17/snapshot", &encode_snapshot(s))
}

/// Decode a snapshot from its dep-17 canonical encoding, rejecting non-canonical input.
pub fn decode_snapshot(buf: &[u8]) -> Result<super::snapshot::Snapshot, DecodeError> {
    let mut d = Decoder::new(buf);
    let version = d.u8()?;
    if version != 0x01 {
        return Err(DecodeError::BadVersion(version));
    }
    let balance = d.int()?;
    let blocks_since_activity = d.u32()?;
    let blocks_since_open = d.u32()?;
    let height = d.u32()?;

    let mut rolling = BTreeMap::new();
    let n = d.u32()?;
    let mut prev: Option<(u8, u32)> = None;
    for _ in 0..n {
        let field_id = d.u8()?;
        let period = d.u32()?;
        let amount = d.int()?;
        let key = (field_id, period);
        if let Some(prev) = prev {
            if key <= prev {
                return Err(DecodeError::NonCanonicalOrder);
            }
        }
        prev = Some(key);
        rolling.insert((rwfield_name(field_id)?.to_string(), period), amount);
    }

    let mut cumulative_spent: BTreeMap<Vec<usize>, i128> = BTreeMap::new();
    let m = d.u32()?;
    let mut prev_path: Option<Vec<usize>> = None;
    for _ in 0..m {
        let plen = d.u32()?;
        let mut path = Vec::with_capacity(plen as usize);
        for _ in 0..plen {
            path.push(d.u32()? as usize);
        }
        let amount = d.int()?;
        if let Some(prev) = &prev_path {
            if &path <= prev {
                return Err(DecodeError::NonCanonicalOrder);
            }
        }
        prev_path = Some(path.clone());
        cumulative_spent.insert(path, amount);
    }

    d.finish()?;
    Ok(super::snapshot::Snapshot {
        balance,
        blocks_since_activity,
        blocks_since_open,
        height,
        rolling,
        cumulative_spent,
    })
}
