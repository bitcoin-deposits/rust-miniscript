#![allow(unexpected_cfgs)]

// Fuzz the dep-17 canonical descriptor decoder: any byte string should either decode to a
// well-formed descriptor or return a DecodeError, without panicking, allocating multi-gigabytes,
// or recursing past MAX_DEPTH.

use honggfuzz::fuzz;
use miniscript::calculus::decode_descriptor;

fn do_test(data: &[u8]) {
    let _ = decode_descriptor::<String>(data);
}

fn main() {
    loop {
        fuzz!(|data| {
            do_test(data);
        });
    }
}
