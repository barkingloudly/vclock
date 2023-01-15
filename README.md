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
c2.incr(&"a");                    // c1 is now a:1, b:0
assert!(c1 < c2, "c1 should be a child of c2");
```

Package has two optional features:

* `serde` to enable [Serde](https://serde.rs/) support for (de)serialization
* `bigint` to enable [big integers](https://crates.io/crates/num_bigint) support and have "infinite" vector clocks

# Benchmarks

Taken from a random CI job:

```
running 15 tests
test tests::bench_vclock64_int_cmp_10     ... bench:         383 ns/iter (+/- 12)
test tests::bench_vclock64_int_cmp_100    ... bench:       2,889 ns/iter (+/- 78)
test tests::bench_vclock64_int_cmp_1000   ... bench:      26,221 ns/iter (+/- 384)
test tests::bench_vclock64_int_cmp_10000  ... bench:     276,902 ns/iter (+/- 3,855)
test tests::bench_vclock64_int_incr       ... bench:          35 ns/iter (+/- 2)
test tests::bench_vclock64_str_cmp_10     ... bench:         346 ns/iter (+/- 8)
test tests::bench_vclock64_str_cmp_100    ... bench:       3,104 ns/iter (+/- 87)
test tests::bench_vclock64_str_cmp_1000   ... bench:      36,570 ns/iter (+/- 2,054)
test tests::bench_vclock64_str_cmp_10000  ... bench:     663,951 ns/iter (+/- 52,968)
test tests::bench_vclock64_str_incr       ... bench:          53 ns/iter (+/- 10)
test tests::bench_vclockbig_str_cmp_10    ... bench:         548 ns/iter (+/- 11)
test tests::bench_vclockbig_str_cmp_100   ... bench:       3,945 ns/iter (+/- 96)
test tests::bench_vclockbig_str_cmp_1000  ... bench:      37,310 ns/iter (+/- 3,270)
test tests::bench_vclockbig_str_cmp_10000 ... bench:     688,678 ns/iter (+/- 157,335)
test tests::bench_vclockbig_str_incr      ... bench:         113 ns/iter (+/- 4)
test result: ok. 0 passed; 0 failed; 0 ignored; 15 measured; 0 filtered out; finished in 11.35s
```

This is not the result of thorough, intensive benchmarking, but we can at least
infer that one significant game changer, when comparing, is the length of the vector clocks.
It grows more or less linearily as their size increases.

To run the benchmarks:

```shell
cd bench
rustup default nightly
cargo bench
```

# Links

* [crate](https://crates.io/crates/vclock) on crates.io
* [doc](https://docs.rs/vclock/) on docs.rs
* [source](https://gitlab.com/liberecofr/vclock/tree/main) on gitlab.com

# License

VClock is licensed under the [MIT](https://gitlab.com/liberecofr/vclock/blob/main/LICENSE) license.
