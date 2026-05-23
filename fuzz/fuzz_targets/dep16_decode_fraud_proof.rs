#![allow(unexpected_cfgs)]

// Fuzz the full FraudProof bundle decoder: the highest-value target, since it exercises every
// sub-decoder (descriptor, operation, snapshot, witness) through its length-delimited sub-slice.
// Any byte string should either decode or return a DecodeError without panicking.

use honggfuzz::fuzz;
use miniscript::calculus::FraudProof;

fn do_test(data: &[u8]) {
    let _ = FraudProof::<String>::decode(data);
}

fn main() {
    loop {
        fuzz!(|data| {
            do_test(data);
        });
    }
}
