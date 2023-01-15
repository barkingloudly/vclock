# VClock

[VClock](https://gitlab.com/liberecofr/vclock) is a vector clock implemented in [Rust](https://www.rust-lang.org/).

It offers a [partial order of events in a distributed system](https://en.wikipedia.org/wiki/Vector_clock).
In practice, it implements [the rust partial order trait](https://doc.rust-lang.org/stable/std/cmp/trait.PartialOrd.html) over hash maps which maintain an integer count of each modification, per key.

![VClock icon](https://gitlab.com/liberecofr/vclock/raw/main/vclock.png)

# Status

This is, to my knowledge, not used in "real" production, so the
only safety net is unit tests. Project has a reasonable test harness, so
it *should be OK* to use it. Again, *DISCLAIMER*, use at your own risks.

[![Build Status](https://gitlab.com/liberecofr/vclock/badges/main/pipeline.svg)](https://gitlab.com/liberecofr/vclock/pipelines)
[![Crates.io](https://img.shields.io/crates/v/vclock.svg)](https://crates.io/crates/vclock)
[![Gitlab](https://img.shields.io/gitlab/last-commit/liberecofr/vclock)](https://gitlab.com/liberecofr/vclock/tree/main)
[![License](https://img.shields.io/gitlab/license/liberecofr/vclock)](https://gitlab.com/liberecofr/vclock/blob/main/LICENSE)

# Usage

```rust
use vclock::VClock64;

let c1 = VClock64::new("a");      // c1 is now a:0
let mut c2 = VClock64::new("b");  // c2 is now b:0
c2.incr(&"a");                    // c1 is now a:1,b:0
assert!(c1 < c2, "c2 is a parent of c1");
```

# Benchmarks

[TODO...]

# Links

* [crate](https://crates.io/crates/vclock) on crates.io
* [doc](https://docs.rs/vclock/) on docs.rs
* [source](https://gitlab.com/liberecofr/vclock/tree/main) on gitlab.com

# License

VClock is licensed under the [MIT](https://gitlab.com/liberecofr/vclock/blob/main/LICENSE) license.
