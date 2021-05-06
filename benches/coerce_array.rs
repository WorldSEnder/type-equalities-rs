#![feature(test)]
extern crate test;

mod benches {
    use test::Bencher;
    use type_equalities::*;

    // Must still fit on the stack.
    const BENCH_LEN: usize = 100_000;
    const THE_ARRAY: [u32; BENCH_LEN] = [0; BENCH_LEN];

    #[bench]
    fn bench_no_coerce(b: &mut Bencher) {
        b.iter(|| THE_ARRAY);
    }

    #[bench]
    fn bench_coerce_array_refl(b: &mut Bencher) {
        let eq = refl::<u32>().lift_through::<SliceF<BENCH_LEN>>();
        b.iter(|| eq.coerce(THE_ARRAY));
    }
}
