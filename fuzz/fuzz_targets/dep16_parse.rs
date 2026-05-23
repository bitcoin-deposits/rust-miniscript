#![allow(unexpected_cfgs)]

// Fuzz the dep-16 source parser: any byte string should either parse successfully or return a
// ParseError without panicking. Uses String as the key type so parsing depends only on the parser
// (String::from_str is infallible), exercising the parser surface rather than the key parser.

use honggfuzz::fuzz;
use miniscript::calculus::parse;

fn do_test(data: &[u8]) {
    let s = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return,
    };
    let _ = parse::<String>(s);
}

fn main() {
    loop {
        fuzz!(|data| {
            do_test(data);
        });
    }
}
