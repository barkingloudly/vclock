#![feature(test)]
extern crate test;
extern crate vclock;

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;
    use test::Bencher;
    use vclock::{VClock, VClock64};

    #[bench]
    fn bench_vclock64_str_incr(b: &mut Bencher) {
        let mut c = VClock64::default();
        b.iter(|| {
            c.incr(&"key");
        });
        println!("c: {}", c);
    }

    fn bench_vclock64_str_cmp_n(b: &mut Bencher, n: usize) {
        let mut c1 = VClock64::default();
        let mut c2 = VClock64::default();
        for i in 0..n {
            c1.incr(&format!("key{}", i));
            c2.incr(&format!("key{}", i + n / 10));
        }
        let mut cmp = false;
        b.iter(|| {
            cmp = c1 < c2;
        });
        println!("cmp: {}", cmp);
    }

    #[bench]
    fn bench_vclock64_str_cmp_10(b: &mut Bencher) {
        bench_vclock64_str_cmp_n(b, 10);
    }

    #[bench]
    fn bench_vclock64_str_cmp_100(b: &mut Bencher) {
        bench_vclock64_str_cmp_n(b, 100);
    }

    #[bench]
    fn bench_vclock64_str_cmp_1000(b: &mut Bencher) {
        bench_vclock64_str_cmp_n(b, 1_000);
    }

    #[bench]
    fn bench_vclock64_str_cmp_10000(b: &mut Bencher) {
        bench_vclock64_str_cmp_n(b, 10_000);
    }

    #[bench]
    fn bench_vclock64_int_incr(b: &mut Bencher) {
        let mut c = VClock64::default();
        b.iter(|| {
            c.incr(&1);
        });
        println!("c: {}", c);
    }

    fn bench_vclock64_int_cmp_n(b: &mut Bencher, n: usize) {
        let mut c1 = VClock64::default();
        let mut c2 = VClock64::default();
        for i in 0..n as usize {
            c1.incr(&i);
            c2.incr(&(i + n / 10));
        }
        let mut cmp = false;
        b.iter(|| {
            cmp = c1 < c2;
        });
        println!("cmp: {}", cmp);
    }

    #[bench]
    fn bench_vclock64_int_cmp_10(b: &mut Bencher) {
        bench_vclock64_int_cmp_n(b, 10);
    }

    #[bench]
    fn bench_vclock64_int_cmp_100(b: &mut Bencher) {
        bench_vclock64_int_cmp_n(b, 100);
    }

    #[bench]
    fn bench_vclock64_int_cmp_1000(b: &mut Bencher) {
        bench_vclock64_int_cmp_n(b, 1_000);
    }

    #[bench]
    fn bench_vclock64_int_cmp_10000(b: &mut Bencher) {
        bench_vclock64_int_cmp_n(b, 10_000);
    }

    #[bench]
    fn bench_vclockbig_str_incr(b: &mut Bencher) {
        let mut c = VClock::<&str, BigUint>::default();
        b.iter(|| {
            c.incr(&"key");
        });
        println!("c: {}", c);
    }

    fn bench_vclockbig_str_cmp_n(b: &mut Bencher, n: usize) {
        let mut c1 = VClock64::default();
        let mut c2 = VClock64::default();
        for i in 0..n {
            c1.incr(&format!("key{}", i));
            c2.incr(&format!("key{}", i + n / 10));
        }
        let mut cmp = false;
        b.iter(|| {
            cmp = c1 < c2;
        });
        println!("cmp: {}", cmp);
    }

    #[bench]
    fn bench_vclockbig_str_cmp_10(b: &mut Bencher) {
        bench_vclockbig_str_cmp_n(b, 10);
    }

    #[bench]
    fn bench_vclockbig_str_cmp_100(b: &mut Bencher) {
        bench_vclockbig_str_cmp_n(b, 100);
    }

    #[bench]
    fn bench_vclockbig_str_cmp_1000(b: &mut Bencher) {
        bench_vclockbig_str_cmp_n(b, 1_000);
    }

    #[bench]
    fn bench_vclockbig_str_cmp_10000(b: &mut Bencher) {
        bench_vclockbig_str_cmp_n(b, 10_000);
    }
}
