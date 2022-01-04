# type-equalities
[![Documentation](https://docs.rs/type-equalities/badge.svg)](https://docs.rs/type-equalities/)
[![Further crate info](https://img.shields.io/crates/v/type-equalities.svg)](https://crates.io/crates/type-equalities)

The central type, `TypeEq<_, _>`, allows for zero-overhead, safe value coercions and is itself zero-sized.
Further, naming `TypeEq<T, U>` is well-formed for any types, but an inhabitant is available only if the
equality holds. For trait-level type equality, `T: IsEqual<U>` can be used.

The zero overhead claim can be seen in the provided benchmarks:

```rust
let eq = refl::<u32>().lift_through::<SliceF<BENCH_LEN>>();
b.iter(|| [0; BENCH_LEN]);            // bench_no_coerce
b.iter(|| eq.coerce([0; BENCH_LEN])); // bench_coerce_array_refl

> running 2 tests
test benches::bench_no_coerce         ... bench:      10,570 ns/iter (+/- 569)
test benches::bench_coerce_array_refl ... bench:      10,557 ns/iter (+/- 605)
```

This crate is **no-std** and has a (default: enabled) feature for **alloc** features, i.e. coercing `Box`.

## License

Licensed under either of
 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)
at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you shall be dual licensed as above, without any
additional terms or conditions.
