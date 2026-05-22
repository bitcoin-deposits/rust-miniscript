// SPDX-License-Identifier: CC0-1.0

//! Canonical surface encoding of a descriptor.
//!
//! Produces the descriptor's source form deterministically: the same descriptor always prints to
//! the same string, and (for descriptors without hash literals, which currently have no surface
//! syntax) the result re-parses to an equal descriptor. This is the basis for a descriptor
//! commitment and for the determinism the fraud-proof mechanism requires. The byte-level canonical
//! encoding used for signing is host-specified and separate.

use core::fmt::Display;

use crate::prelude::*;
use crate::MiniscriptKey;

use super::ast::{BTerm, Descriptor, Obligation, VTerm};
use super::schema::Schema;
use super::value::{HashValue, Value};

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
