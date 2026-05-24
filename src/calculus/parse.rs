// SPDX-License-Identifier: CC0-1.0

//! Parser for the calculus surface syntax.
//!
//! The surface is miniscript-shaped — `combinator(arg, ...)` — extended with the `with(...)`
//! constant-binding form, `[..]` list literals, and bare comparison operators as `cmp` arguments.
//! These extensions need handling that the bare `expression::Tree` splitter does not provide (it
//! does not track `[..]` nesting and treats `=` as an ordinary character), so this is a small
//! self-contained recursive-descent parser over the same token shape.
//!
//! Dispatch is by combinator name into the correct sort: a name is looked up against the boolean
//! combinators, the [`ValueFn`](super::registry::ValueFn) table, the
//! [`StatePred`](super::registry::StatePred) table, and the obligation forms, in that order.

use core::convert::TryInto;
use core::fmt;
use core::str::FromStr;

use crate::prelude::*;
use crate::MiniscriptKey;

use super::ast::{BTerm, Descriptor, Obligation, Scheme, VTerm};
use super::encode::is_canonical_name;
use super::limits::MAX_DEPTH;
use super::registry::{CmpOp, StatePred, Symbol, ValueFn};
use super::schema::Schema;
use super::value::{HashValue, Value};

fn is_hashfn(w: &str) -> bool {
    matches!(w, "sha256" | "hash256" | "ripemd160" | "hash160")
}

/// Decode a hex string (without `0x`) into bytes, rejecting odd lengths and non-hex digits.
fn decode_hex(s: &str) -> Result<Vec<u8>, ParseError> {
    if s.len() % 2 != 0 {
        return err("hex literal has an odd number of digits");
    }
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(s.len() / 2);
    let mut i = 0;
    while i < bytes.len() {
        let hi = (bytes[i] as char).to_digit(16);
        let lo = (bytes[i + 1] as char).to_digit(16);
        match (hi, lo) {
            (Some(h), Some(l)) => out.push((h * 16 + l) as u8),
            _ => return err(format!("invalid hex in `{}`", s)),
        }
        i += 2;
    }
    Ok(out)
}

/// Build a tagged hash value from a hash-function name and `0x`-prefixed hex digest.
fn hash_literal(fnname: &str, hexword: &str) -> Result<HashValue, ParseError> {
    let hex = hexword.strip_prefix("0x").ok_or(ParseError {
        message: "hash literal digest must be 0x-prefixed".to_string(),
    })?;
    let bytes = decode_hex(hex)?;
    let arr32 = || -> Result<[u8; 32], ParseError> {
        bytes.clone().try_into().map_err(|_| ParseError {
            message: format!("{} digest must be 32 bytes", fnname),
        })
    };
    let arr20 = || -> Result<[u8; 20], ParseError> {
        bytes.clone().try_into().map_err(|_| ParseError {
            message: format!("{} digest must be 20 bytes", fnname),
        })
    };
    Ok(match fnname {
        "sha256" => HashValue::Sha256(arr32()?),
        "hash256" => HashValue::Hash256(arr32()?),
        "ripemd160" => HashValue::Ripemd160(arr20()?),
        "hash160" => HashValue::Hash160(arr20()?),
        _ => return err(format!("unknown hash function `{}`", fnname)),
    })
}

/// An error produced while parsing a descriptor.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParseError {
    /// A human-readable description of the failure.
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { f.write_str(&self.message) }
}

fn err<T>(msg: impl Into<String>) -> Result<T, ParseError> {
    Err(ParseError { message: msg.into() })
}

/// Parse a descriptor from its source representation.
pub fn parse<Pk>(s: &str) -> Result<Descriptor<Pk>, ParseError>
where
    Pk: MiniscriptKey + FromStr,
{
    let tokens = lex(s)?;
    let mut p = Parser { tokens: &tokens, pos: 0, bound: BTreeSet::new(), depth: 0 };
    let d = p.descriptor()?;
    if p.pos != p.tokens.len() {
        return err(format!("trailing tokens after descriptor at position {}", p.pos));
    }
    Ok(d)
}

// ----------------------------------------------------------------------------------------------
// Lexer
// ----------------------------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Debug)]
enum Tok {
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Eq,
    Colon,
    Lt,
    Le,
    Gt,
    Ge,
    Word(String),
    Num(i128),
}

fn lex(s: &str) -> Result<Vec<Tok>, ParseError> {
    let bytes = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i] as char;
        match c {
            c if c.is_whitespace() => i += 1,
            '(' => {
                out.push(Tok::LParen);
                i += 1;
            }
            ')' => {
                out.push(Tok::RParen);
                i += 1;
            }
            '[' => {
                out.push(Tok::LBracket);
                i += 1;
            }
            ']' => {
                out.push(Tok::RBracket);
                i += 1;
            }
            ',' => {
                out.push(Tok::Comma);
                i += 1;
            }
            '=' => {
                out.push(Tok::Eq);
                i += 1;
            }
            ':' => {
                out.push(Tok::Colon);
                i += 1;
            }
            '-' => {
                // A `-` is only meaningful as the sign of a numeric literal; require a digit next.
                if i + 1 < bytes.len() && (bytes[i + 1] as char).is_ascii_digit() {
                    let start = i;
                    i += 1; // consume the `-`
                    while i < bytes.len() && (bytes[i] as char).is_ascii_digit() {
                        i += 1;
                    }
                    let text = &s[start..i];
                    let n: i128 = text
                        .parse()
                        .map_err(|_| ParseError { message: format!("bad integer `{}`", text) })?;
                    out.push(Tok::Num(n));
                } else {
                    return err(format!("unexpected character `-`"));
                }
            }
            '<' => {
                if i + 1 < bytes.len() && bytes[i + 1] == b'=' {
                    out.push(Tok::Le);
                    i += 2;
                } else {
                    out.push(Tok::Lt);
                    i += 1;
                }
            }
            '>' => {
                if i + 1 < bytes.len() && bytes[i + 1] == b'=' {
                    out.push(Tok::Ge);
                    i += 2;
                } else {
                    out.push(Tok::Gt);
                    i += 1;
                }
            }
            c if c == '_' || c.is_ascii_alphanumeric() => {
                // Consume a maximal alphanumeric/underscore run, then classify: an all-digit run is
                // an integer; anything else (including hex keys that begin with a digit) is a word.
                let start = i;
                while i < bytes.len() {
                    let d = bytes[i] as char;
                    if d == '_' || d.is_ascii_alphanumeric() {
                        i += 1;
                    } else {
                        break;
                    }
                }
                let text = &s[start..i];
                if text.bytes().all(|b| b.is_ascii_digit()) {
                    let n: i128 = text
                        .parse()
                        .map_err(|_| ParseError { message: format!("bad integer `{}`", text) })?;
                    out.push(Tok::Num(n));
                } else {
                    out.push(Tok::Word(text.to_string()));
                }
            }
            other => return err(format!("unexpected character `{}`", other)),
        }
    }
    Ok(out)
}

// ----------------------------------------------------------------------------------------------
// Parser
// ----------------------------------------------------------------------------------------------

struct Parser<'a> {
    tokens: &'a [Tok],
    pos: usize,
    /// Names bound by the enclosing `with(...)`. A bare word in value position resolves to a
    /// constant reference if bound, and is otherwise parsed as a key literal.
    bound: BTreeSet<String>,
    /// Current AST nesting depth, bounded by [`MAX_DEPTH`] to stop adversary-supplied input from
    /// driving the recursive descent into a stack overflow.
    depth: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&Tok> { self.tokens.get(self.pos) }

    fn next(&mut self) -> Result<&'a Tok, ParseError> {
        let t = self.tokens.get(self.pos).ok_or(ParseError {
            message: "unexpected end of input".to_string(),
        })?;
        self.pos += 1;
        Ok(t)
    }

    fn expect(&mut self, want: &Tok) -> Result<(), ParseError> {
        match self.next()? {
            t if t == want => Ok(()),
            t => err(format!("expected {:?}, found {:?}", want, t)),
        }
    }

    fn word(&mut self) -> Result<String, ParseError> {
        match self.next()? {
            Tok::Word(w) => Ok(w.clone()),
            t => err(format!("expected an identifier, found {:?}", t)),
        }
    }

    fn descriptor<Pk>(&mut self) -> Result<Descriptor<Pk>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        // Look at the leading word for a scheme wrapper. `wsh(...)` and `tr(...)` are recognized;
        // anything else (including a bare body or a `with(...)` at the top) is implicitly wsh for
        // backward compatibility.
        if let Some(Tok::Word(w)) = self.peek() {
            match w.as_str() {
                "wsh" => return self.parse_wsh::<Pk>(),
                "tr" => return self.parse_tr::<Pk>(),
                _ => {}
            }
        }
        let (constants, body) = self.parse_with_or_bare()?;
        Ok(Descriptor { constants, scheme: Scheme::Wsh { body } })
    }

    /// `wsh( <with-or-bare-body> )` — explicit wrapper for the default scheme.
    fn parse_wsh<Pk>(&mut self) -> Result<Descriptor<Pk>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        self.pos += 1; // consume "wsh"
        self.expect(&Tok::LParen)?;
        let (constants, body) = self.parse_with_or_bare()?;
        self.expect(&Tok::RParen)?;
        Ok(Descriptor { constants, scheme: Scheme::Wsh { body } })
    }

    /// `tr( KEY )` or `tr( KEY, <with-or-bare-body> )`.
    fn parse_tr<Pk>(&mut self) -> Result<Descriptor<Pk>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        self.pos += 1; // consume "tr"
        self.expect(&Tok::LParen)?;
        // Internal key — a bare word that resolves via Pk::from_str. There is no `with(...)`
        // binding for the internal key; tr's K slot is a key literal by construction.
        let key_word = self.word()?;
        let internal_key = Pk::from_str(&key_word)
            .map_err(|_| ParseError { message: format!("tr internal key `{}` is not a valid key", key_word) })?;
        let body = if matches!(self.peek(), Some(Tok::Comma)) {
            self.pos += 1;
            let (constants_for_body, body) = self.parse_with_or_bare()?;
            self.expect(&Tok::RParen)?;
            // Constants from the body's `with(...)` are part of the descriptor.
            return Ok(Descriptor {
                constants: constants_for_body,
                scheme: Scheme::Tr { internal_key, body: Some(body) },
            });
        } else {
            None
        };
        self.expect(&Tok::RParen)?;
        Ok(Descriptor {
            constants: BTreeMap::new(),
            scheme: Scheme::Tr { internal_key, body },
        })
    }

    /// `with(name = val, ..., in body)` or just `body` — common to wsh and tr's body slot.
    fn parse_with_or_bare<Pk>(&mut self) -> Result<(BTreeMap<String, Value<Pk>>, BTerm<Pk>), ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        if matches!(self.peek(), Some(Tok::Word(w)) if w == "with") {
            self.pos += 1;
            self.expect(&Tok::LParen)?;
            let mut constants = BTreeMap::new();
            loop {
                if matches!(self.peek(), Some(Tok::Word(w)) if w == "in") {
                    self.pos += 1;
                    break;
                }
                let name = self.word()?;
                if !is_canonical_name(&name) {
                    return err(format!("invalid constant name `{}`", name));
                }
                self.expect(&Tok::Eq)?;
                let value = self.literal()?;
                constants.insert(name, value);
                self.expect(&Tok::Comma)?;
            }
            self.bound = constants.keys().cloned().collect();
            let body = self.bterm()?;
            self.expect(&Tok::RParen)?;
            Ok((constants, body))
        } else {
            let body = self.bterm()?;
            Ok((BTreeMap::new(), body))
        }
    }

    /// A literal value, used on the right of a `with(...)` binding.
    fn literal<Pk>(&mut self) -> Result<Value<Pk>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        if self.depth >= MAX_DEPTH {
            return err(format!("nesting too deep (> {})", MAX_DEPTH));
        }
        self.depth += 1;
        let r = self.literal_inner();
        self.depth -= 1;
        r
    }

    fn literal_inner<Pk>(&mut self) -> Result<Value<Pk>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        match self.peek() {
            Some(Tok::LBracket) => {
                self.pos += 1;
                let mut items = Vec::new();
                if !matches!(self.peek(), Some(Tok::RBracket)) {
                    loop {
                        items.push(self.literal()?);
                        match self.next()? {
                            Tok::Comma => {}
                            Tok::RBracket => break,
                            t => return err(format!("expected `,` or `]`, found {:?}", t)),
                        }
                    }
                } else {
                    self.pos += 1;
                }
                Ok(Value::List(items))
            }
            Some(Tok::Num(n)) => {
                let n = *n;
                self.pos += 1;
                Ok(Value::Int(n))
            }
            Some(Tok::Word(w)) => {
                let w = w.clone();
                // Hash literal: `sha256(0x...)` is canonical; `sha256:0x...` is legacy.
                if is_hashfn(&w) && matches!(self.tokens.get(self.pos + 1), Some(Tok::LParen)) {
                    self.pos += 1;
                    self.expect(&Tok::LParen)?;
                    let hexword = self.word()?;
                    self.expect(&Tok::RParen)?;
                    return Ok(Value::Hash(hash_literal(&w, &hexword)?));
                }
                if is_hashfn(&w) && matches!(self.tokens.get(self.pos + 1), Some(Tok::Colon)) {
                    self.pos += 1;
                    self.expect(&Tok::Colon)?;
                    let hexword = self.word()?;
                    return Ok(Value::Hash(hash_literal(&w, &hexword)?));
                }
                self.pos += 1;
                // bytes literal: `0x...` (non-empty).
                if let Some(hex) = w.strip_prefix("0x") {
                    if hex.is_empty() {
                        return err("empty hex literal `0x`");
                    }
                    return Ok(Value::Bytes(decode_hex(hex)?));
                }
                match Pk::from_str(&w) {
                    Ok(k) => Ok(Value::Key(k)),
                    Err(_) => Ok(Value::Bytes(w.into_bytes())),
                }
            }
            t => err(format!("expected a literal, found {:?}", t)),
        }
    }

    fn bterm<Pk>(&mut self) -> Result<BTerm<Pk>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        if self.depth >= MAX_DEPTH {
            return err(format!("nesting too deep (> {})", MAX_DEPTH));
        }
        self.depth += 1;
        let r = self.bterm_inner();
        self.depth -= 1;
        r
    }

    fn bterm_inner<Pk>(&mut self) -> Result<BTerm<Pk>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        let name = self.word()?;
        match name.as_str() {
            "true" => return Ok(BTerm::Const(true)),
            "false" => return Ok(BTerm::Const(false)),
            _ => {}
        }
        self.expect(&Tok::LParen)?;
        let result = match name.as_str() {
            "and" => BTerm::And(self.bterm_list()?),
            "or" => BTerm::Or(self.bterm_list()?),
            "thresh" => {
                let k = self.num()? as usize;
                self.expect(&Tok::Comma)?;
                BTerm::Thresh(k, self.bterm_list()?)
            }
            "not" => {
                let b = self.bterm()?;
                self.expect(&Tok::RParen)?;
                BTerm::Not(Box::new(b))
            }
            "if" => {
                let c = self.bterm()?;
                self.expect(&Tok::Comma)?;
                let t = self.bterm()?;
                self.expect(&Tok::Comma)?;
                let e = self.bterm()?;
                self.expect(&Tok::RParen)?;
                BTerm::If(Box::new(c), Box::new(t), Box::new(e))
            }
            "match" => self.match_term()?,
            "cmp" => {
                let op = self.cmpop()?;
                self.expect(&Tok::Comma)?;
                let a = self.vterm()?;
                self.expect(&Tok::Comma)?;
                let b = self.vterm()?;
                self.expect(&Tok::RParen)?;
                BTerm::Cmp(op, a, b)
            }
            "prove" => {
                let o = self.obligation()?;
                self.expect(&Tok::RParen)?;
                BTerm::Prove(o)
            }
            // Comparison predicates as direct BTerm forms (boring; matches miniscript-style
            // naming). The legacy `cmp(<op>, a, b)` form above still parses.
            "eq" | "lt" | "le" | "gt" | "ge" => {
                let op = match name.as_str() {
                    "eq" => CmpOp::Eq,
                    "lt" => CmpOp::Lt,
                    "le" => CmpOp::Le,
                    "gt" => CmpOp::Gt,
                    "ge" => CmpOp::Ge,
                    _ => unreachable!(),
                };
                let a = self.vterm()?;
                self.expect(&Tok::Comma)?;
                let b = self.vterm()?;
                self.expect(&Tok::RParen)?;
                BTerm::Cmp(op, a, b)
            }
            other => {
                if Self::is_obligation_name(other) {
                    // Direct obligation form at BTerm position — `pk(K)` rather than
                    // `prove(pk(K))`. Matches miniscript surface; internally still wraps in Prove.
                    let o = self.obligation_body(other)?;
                    BTerm::Prove(o)
                } else if let Some(pred) = StatePred::from_name(other) {
                    let args = self.vterm_list()?;
                    BTerm::State(pred, args)
                } else {
                    return err(format!("unknown boolean combinator `{}`", other));
                }
            }
        };
        Ok(result)
    }

    fn bterm_list<Pk>(&mut self) -> Result<Vec<BTerm<Pk>>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        let mut out = Vec::new();
        if matches!(self.peek(), Some(Tok::RParen)) {
            self.pos += 1;
            return Ok(out);
        }
        loop {
            out.push(self.bterm()?);
            match self.next()? {
                Tok::Comma => {}
                Tok::RParen => break,
                t => return err(format!("expected `,` or `)`, found {:?}", t)),
            }
        }
        Ok(out)
    }

    fn match_term<Pk>(&mut self) -> Result<BTerm<Pk>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        let scrutinee = self.vterm()?;
        self.expect(&Tok::Comma)?;
        let mut arms = Vec::new();
        let mut default = None;
        loop {
            let kw = self.word()?;
            if kw != "branch" {
                return err(format!("expected `branch`, found `{}`", kw));
            }
            self.expect(&Tok::LParen)?;
            let tag = self.word()?;
            self.expect(&Tok::Comma)?;
            let body = self.bterm()?;
            self.expect(&Tok::RParen)?;
            if tag == "else" {
                default = Some(Box::new(body));
            } else {
                arms.push((Symbol::new(tag), body));
            }
            match self.next()? {
                Tok::Comma => {}
                Tok::RParen => break,
                t => return err(format!("expected `,` or `)`, found {:?}", t)),
            }
        }
        match default {
            Some(default) => Ok(BTerm::Match { scrutinee, arms, default }),
            None => err("match is missing an `else` branch"),
        }
    }

    /// True iff `name` is a proof-obligation form (so it can be dispatched directly at BTerm
    /// position without the `prove(...)` wrapper, matching miniscript's `pk(K)` etc.).
    fn is_obligation_name(name: &str) -> bool {
        matches!(
            name,
            "pk" | "pk_h"
                | "pk_any"
                | "multi"
                | "pk_threshold"
                | "hashlock"
                | "attest"
        )
    }

    /// Parse the body of an obligation `name(...)` whose name and opening `(` have already been
    /// consumed. Shared between the `prove(<obligation>)` legacy form and the direct dispatch
    /// from `bterm` (where `pk(K)` admits as a BTerm without the `prove` wrapper).
    fn obligation_body<Pk>(&mut self, name: &str) -> Result<Obligation<Pk>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        let result = match name {
            "pk" => {
                let v = self.vterm()?;
                self.expect(&Tok::RParen)?;
                Obligation::Pk(v)
            }
            "pk_h" => {
                let v = self.vterm()?;
                self.expect(&Tok::RParen)?;
                Obligation::PkH(v)
            }
            "pk_any" => {
                let v = self.vterm()?;
                self.expect(&Tok::RParen)?;
                Obligation::PkAny(v)
            }
            // `multi` is the canonical name (matches miniscript); `pk_threshold` is the legacy
            // alias from an earlier iteration of this codebase.
            "multi" | "pk_threshold" => {
                let k = self.num()? as usize;
                self.expect(&Tok::Comma)?;
                let v = self.vterm()?;
                self.expect(&Tok::RParen)?;
                Obligation::Multi(k, v)
            }
            "hashlock" => {
                let v = self.vterm()?;
                self.expect(&Tok::RParen)?;
                Obligation::Hashlock(v)
            }
            "attest" => {
                let key = self.vterm()?;
                self.expect(&Tok::Comma)?;
                let schema = self.schema()?;
                self.expect(&Tok::RParen)?;
                Obligation::Attest(key, schema)
            }
            other => return err(format!("unknown proof obligation `{}`", other)),
        };
        Ok(result)
    }

    /// Parse a full obligation form `name(...)`, used by the legacy `prove(<obligation>)` wrapper.
    fn obligation<Pk>(&mut self) -> Result<Obligation<Pk>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        let name = self.word()?;
        self.expect(&Tok::LParen)?;
        self.obligation_body(&name)
    }

    fn schema(&mut self) -> Result<Schema, ParseError> {
        let name = self.word()?;
        self.expect(&Tok::LParen)?;
        let result = match name.as_str() {
            "price_schema" => {
                let n = self.num()?;
                self.expect(&Tok::RParen)?;
                Schema::PriceWithinBps { tolerance_bps: n as u32 }
            }
            other => return err(format!("unknown schema `{}`", other)),
        };
        Ok(result)
    }

    fn vterm<Pk>(&mut self) -> Result<VTerm<Pk>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        if self.depth >= MAX_DEPTH {
            return err(format!("nesting too deep (> {})", MAX_DEPTH));
        }
        self.depth += 1;
        let r = self.vterm_inner();
        self.depth -= 1;
        r
    }

    fn vterm_inner<Pk>(&mut self) -> Result<VTerm<Pk>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        match self.peek() {
            Some(Tok::Num(n)) => {
                let n = *n;
                self.pos += 1;
                Ok(VTerm::Lit(Value::Int(n)))
            }
            Some(Tok::LBracket) => Ok(VTerm::Lit(self.literal()?)),
            Some(Tok::Word(w)) => {
                let w = w.clone();
                // Hash literal: `sha256(0x...)` is canonical; `sha256:0x...` is legacy.
                if is_hashfn(&w) && matches!(self.tokens.get(self.pos + 1), Some(Tok::LParen)) {
                    self.pos += 1;
                    self.expect(&Tok::LParen)?;
                    let hexword = self.word()?;
                    self.expect(&Tok::RParen)?;
                    return Ok(VTerm::Lit(Value::Hash(hash_literal(&w, &hexword)?)));
                }
                if is_hashfn(&w) && matches!(self.tokens.get(self.pos + 1), Some(Tok::Colon)) {
                    self.pos += 1;
                    self.expect(&Tok::Colon)?;
                    let hexword = self.word()?;
                    return Ok(VTerm::Lit(Value::Hash(hash_literal(&w, &hexword)?)));
                }
                // bytes literal: `0x...` (non-empty).
                if let Some(hex) = w.strip_prefix("0x") {
                    self.pos += 1;
                    if hex.is_empty() {
                        return err("empty hex literal `0x`");
                    }
                    return Ok(VTerm::Lit(Value::Bytes(decode_hex(hex)?)));
                }
                // A word followed by `(` is a value-function application; otherwise it is a
                // reference to a `with(...)` constant.
                if matches!(self.tokens.get(self.pos + 1), Some(Tok::LParen)) {
                    self.pos += 1; // consume the word
                    self.expect(&Tok::LParen)?;
                    let f = ValueFn::from_name(&w)
                        .ok_or(ParseError { message: format!("unknown value function `{}`", w) })?;
                    let args = if f == ValueFn::OperationArg {
                        // operation_arg's argument is a field symbol, not a constant reference.
                        let sym = self.word()?;
                        self.expect(&Tok::RParen)?;
                        vec![VTerm::Lit(Value::Symbol(Symbol::new(sym)))]
                    } else {
                        self.vterm_list()?
                    };
                    Ok(VTerm::Op(f, args))
                } else {
                    self.pos += 1;
                    // A bound name is a constant reference; otherwise treat it as a key literal if
                    // it parses as one, falling back to a (later unresolved) reference.
                    if self.bound.contains(&w) {
                        Ok(VTerm::Var(w))
                    } else {
                        match Pk::from_str(&w) {
                            Ok(k) => Ok(VTerm::Lit(Value::Key(k))),
                            Err(_) => Ok(VTerm::Var(w)),
                        }
                    }
                }
            }
            t => err(format!("expected a value, found {:?}", t)),
        }
    }

    fn vterm_list<Pk>(&mut self) -> Result<Vec<VTerm<Pk>>, ParseError>
    where
        Pk: MiniscriptKey + FromStr,
    {
        let mut out = Vec::new();
        if matches!(self.peek(), Some(Tok::RParen)) {
            self.pos += 1;
            return Ok(out);
        }
        loop {
            out.push(self.vterm()?);
            match self.next()? {
                Tok::Comma => {}
                Tok::RParen => break,
                t => return err(format!("expected `,` or `)`, found {:?}", t)),
            }
        }
        Ok(out)
    }

    fn num(&mut self) -> Result<i128, ParseError> {
        match self.next()? {
            Tok::Num(n) => Ok(*n),
            t => err(format!("expected an integer, found {:?}", t)),
        }
    }

    fn cmpop(&mut self) -> Result<CmpOp, ParseError> {
        match self.next()? {
            Tok::Eq => Ok(CmpOp::Eq),
            Tok::Lt => Ok(CmpOp::Lt),
            Tok::Le => Ok(CmpOp::Le),
            Tok::Gt => Ok(CmpOp::Gt),
            Tok::Ge => Ok(CmpOp::Ge),
            t => err(format!("expected a comparison operator, found {:?}", t)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALLOWANCE: &str = "
        with(
          user = K1,
          delegate = K2,
          guardians = [K3, K4, K5],
          recovery_to = D1,
          in match(operation_type(),
            branch(spend,
              or(
                prove(pk(user)),
                and(
                  prove(pk(delegate)),
                  amount_at_most_pct(10),
                  rolling_amount_below_pct(30, 4320)
                ),
                and(
                  prove(pk_threshold(2, guardians)),
                  blocks_since_activity_at_least(4320),
                  destination_is(recovery_to)
                )
              )
            ),
            branch(insert, prove(pk(user))),
            branch(replace, prove(pk(user))),
            branch(delete, prove(pk(user))),
            branch(else, false)
          )
        )";

    const ORACLE: &str = "
        with(
          user = K1,
          rebalancer = K2,
          oracle = K3,
          counterparty = D1,
          in match(operation_type(),
            branch(spend,
              or(
                prove(pk(user)),
                and(
                  prove(pk(rebalancer)),
                  destination_is(counterparty),
                  prove(attest(oracle, price_schema(50)))
                )
              )
            ),
            branch(else, false)
          )
        )";

    const ROTATION: &str = "
        with(
          user = K1,
          guardians = [G1, G2, G3, G4],
          in match(operation_type(),
            branch(spend, prove(pk(user))),
            branch(replace,
              or(
                prove(pk(user)),
                and(
                  prove(pk_threshold(3, guardians)),
                  blocks_since_activity_at_least(8640),
                  cmp(=, operation_path(), path(0, 0))
                )
              )
            ),
            branch(else, false)
          )
        )";

    fn parse_ok(s: &str) -> Descriptor<String> {
        parse::<String>(s).unwrap_or_else(|e| panic!("parse failed: {}", e))
    }

    #[test]
    fn parses_allowance_example() {
        let d = parse_ok(ALLOWANCE);
        assert_eq!(d.constants.len(), 4);
        assert_eq!(d.constants.get("user"), Some(&Value::Key("K1".to_string())));
        match d.constants.get("guardians") {
            Some(Value::List(ks)) => assert_eq!(ks.len(), 3),
            other => panic!("guardians not a 3-list: {:?}", other),
        }
        match d.body().unwrap() {
            BTerm::Match { arms, .. } => assert_eq!(arms.len(), 4), // spend/insert/replace/delete
            other => panic!("body not a match: {:?}", other),
        }
    }

    #[test]
    fn parses_oracle_example() {
        let d = parse_ok(ORACLE);
        assert_eq!(d.constants.len(), 4);
        // The rebalancer branch carries an oracle attestation with a 50bps schema.
        let found = format!("{:?}", d.body().unwrap()).contains("PriceWithinBps { tolerance_bps: 50 }");
        assert!(found, "expected a 50bps price schema in the parsed body");
    }

    #[test]
    fn parses_rotation_example() {
        let d = parse_ok(ROTATION);
        assert_eq!(d.constants.len(), 2);
        match d.constants.get("guardians") {
            Some(Value::List(ks)) => assert_eq!(ks.len(), 4),
            other => panic!("guardians not a 4-list: {:?}", other),
        }
    }

    #[test]
    fn rejects_match_without_else() {
        let r = parse::<String>("match(operation_type(), branch(spend, true))");
        assert!(r.is_err(), "match without else should fail");
    }

    #[test]
    fn parses_bare_expression_without_with() {
        let d = parse::<String>("prove(pk(user_key))").unwrap();
        assert!(d.constants.is_empty());
        assert!(matches!(d.body().unwrap(), BTerm::Prove(Obligation::Pk(_))));
    }
}
