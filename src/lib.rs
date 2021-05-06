// Copyright (c) 2021 t WorldSEnder
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>,
// at your option. All files in the project carrying such
// notice may not be copied, modified, or distributed except
// according to those terms.
#![cfg_attr(feature = "test-for-type-equality", feature(specialization))]
#![cfg_attr(test, allow(soft_unstable))]
#![cfg_attr(test, feature(test))]
#![feature(unsized_fn_params)]
#![feature(const_fn_trait_bound)]
#![warn(missing_docs, missing_crate_level_docs)]
#![no_std]
//! Implements [`TypeEq`] that can be passed around and used at runtime to safely coerce values,
//! references and other structures dependending on these types.
//!
//! The equality type is zero-sized, and the coercion should optimize to a no-op in all cases.

extern crate core;
use core::marker::PhantomData;

#[cfg(feature = "std")]
extern crate alloc;
#[cfg(feature = "std")]
use alloc::boxed::Box;
#[cfg(test)]
extern crate test;

use crate::kernel::{refl as refl_kernel, use_eq as use_kernel_eq, TheEq};

/// Trait used to convince the rust type checker of the claimed equality
pub trait AliasSelf {
    /// Always set to `Self`, but the type checker doesn't reduce `T::Alias` to `T`.
    type Alias: ?Sized;
}
impl<T: ?Sized> AliasSelf for T {
    type Alias = T;
}

/// Equality at a constraint level, as a type alias. Reflexivity holds.
///
/// # Example
///
/// Note that due to the rust type checker, coercions are not as simple as they
/// might look.
///
/// ```compile_fail
/// # use type_equalities::IsEqual;
/// // Trying to implement coerce like this fails!
/// fn foo<U, T: IsEqual<U>>(t: T) -> U { t }
/// assert_eq!(foo::<u32, u32>(42), 42)
/// //   |
/// // 6 | fn foo<U, T: IsEqual<U>>(t: T) -> U { t }
/// //   |        -  -                       -   ^ expected type parameter `U`, found type parameter `T`
/// //   |        |  |                       |
/// //   |        |  found type parameter    expected `U` because of return type
/// //   |        expected type parameter
/// ```
///
/// But the following works correctly:
///
/// ```
/// # use type_equalities::{IsEqual, coerce, trivial_eq};
/// fn foo<U, T: IsEqual<U>>(t: T) -> U { trivial_eq().coerce(t) }
/// assert_eq!(foo::<u32, u32>(42), 42)
/// ```
pub trait IsEqual<U: ?Sized>: AliasSelf<Alias = U> {}
impl<T: ?Sized, U: ?Sized> IsEqual<U> for T where T: AliasSelf<Alias = U> {}

/// Evidence of the equality `T == U` as a zero-sized type.
///
/// ```
/// # use type_equalities::TypeEq;
/// # type T = ();
/// # type U = ();
/// assert_eq!(core::mem::size_of::<TypeEq<T, U>>(), 0);
/// ```
pub struct TypeEq<T: ?Sized, U: ?Sized> {
    _inner: TheEq<T, U>,
}

impl<T: ?Sized, U: ?Sized> Clone for TypeEq<T, U> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T: ?Sized, U: ?Sized> Copy for TypeEq<T, U> {}

/// Construct evidence of the reflexive equality `T == T`.
pub const fn refl<T: ?Sized>() -> TypeEq<T, T> {
    TypeEq {
        _inner: refl_kernel(),
    }
}

/// Construct evidence of `TypeEq<T, U>` under the constraint `T: IsEqual<U>`.
///
/// Note quite as trivial as it might appear, since we're fighting the type checker a bit.
/// Also should be `const fn` but isn't due to [issue #57563].
///
/// [issue #57563]: https://github.com/rust-lang/rust/issues/57563
pub const fn trivial_eq<T: ?Sized, U: ?Sized>() -> TypeEq<T, U>
where
    T: IsEqual<U>,
{
    const fn refl_alias<T: ?Sized>() -> TypeEq<T, <T as AliasSelf>::Alias> {
        refl()
    }
    refl_alias()
}

/// A consumer recives evidence of a type equality `T == U` and computes a result.
// TODO: This trait could be unsafe to implement, since it gets transmuted, but time will tell.
pub trait Consumer<T: ?Sized, U: ?Sized> {
    /// The result type returned from [`Consumer::consume_eq`].
    type Result;
    /// The strange `where` clause enables the consumer to observe that:
    /// - `T == <T as AssocSelf>::Alias` by the implementation of `AssocSelf`
    /// - `T::Alias == U`
    ///
    /// Directly writing `T = U` is currently not possible, as tracked by [issue #20041].
    ///
    /// A workaround, to make it easier for implementors to construct your own `Consumer`
    /// is, if your consumer takes a generic parameter `T`, store of values with type
    /// `<T as AliasSelf>::Alias` internally. In `consume_eq`, the compiler will correctly
    /// reduce this to `U`, since it sees the `where` clause. Additionally, during
    /// construction (somewhere else), the compiler sees the `impl<T> for AssocSelf`,
    /// correctly using the first equality. Thus, you don't have to coerce consumers.
    ///
    /// [issue #20041]: https://github.com/rust-lang/rust/issues/20041
    fn consume_eq(self) -> Self::Result
    where
        T: IsEqual<U>;
}

/// The identity [`TypeFunction`], `ApF<IdF, T> == T`. Coercing through this gives
/// us the basic safe transmute.
pub struct IdF;
impl<A: ?Sized> TypeFunction<A> for IdF {
    type Result = A;
}

/// Coerce a value of type `T` to a value of type `U`, given evidence that `T == U`.
///
/// Note that this is operationally a no-op
///
/// # Examples
///
/// ```
/// # use type_equalities::{coerce, refl};
/// assert_eq!(coerce(42, refl()), 42);
/// ```
#[inline]
pub fn coerce<T, U>(t: T, ev: TypeEq<T, U>) -> U {
    substitute::<_, _, IdF>(t, ev)
}

/// The [`TypeFunction`] `ApF<BoxF, A> == Box<A>`
#[cfg(feature = "std")]
struct BoxF;
#[cfg(feature = "std")]
impl<A: ?Sized> TypeFunction<A> for BoxF {
    type Result = Box<A>;
}

/// Coerce a value of type `Box<T>` to a value of type `Box<U>`, given evidence that `T == U`.
///
/// # Examples
///
/// ```
/// # use type_equalities::{coerce_box, refl};
/// assert_eq!(*coerce_box(Box::new(42), refl()), 42);
/// ```
#[cfg(feature = "std")]
#[inline]
pub fn coerce_box<T: ?Sized, U: ?Sized>(t: Box<T>, ev: TypeEq<T, U>) -> Box<U> {
    substitute::<_, _, BoxF>(t, ev)
}

/// The [`TypeFunction`] `ApF<RefF<'a>, A> == &'a A`
pub struct RefF<'a>(PhantomData<&'a ()>);
impl<'a, A: ?Sized + 'a> TypeFunction<A> for RefF<'a> {
    type Result = &'a A;
}

/// Coerce a value of type `&T` to a value of type `&U`, given evidence that `T == U`.
///
/// # Examples
///
/// ```
/// # use type_equalities::{coerce_ref, refl};
/// assert_eq!(*coerce_ref(&42, refl()), 42);
/// ```
#[inline]
pub fn coerce_ref<'a, T: ?Sized, U: ?Sized>(t: &'a T, ev: TypeEq<T, U>) -> &'a U {
    substitute::<_, _, RefF>(t, ev)
}

/// The [`TypeFunction`] `ApF<MutRefF<'a>, A> == &'a mut A`
pub struct MutRefF<'a>(PhantomData<&'a ()>);
impl<'a, A: ?Sized + 'a> TypeFunction<A> for MutRefF<'a> {
    type Result = &'a mut A;
}

/// Coerce a value of type `&mut T` to a value of type `&mut U`, given evidence that `T == U`.
///
/// # Examples
///
/// ```
/// # use type_equalities::{coerce_ref, refl};
/// assert_eq!(*coerce_ref(&mut 42, refl()), 42);
/// ```
#[inline]
pub fn coerce_mut<'a, T: ?Sized, U: ?Sized>(t: &'a mut T, ev: TypeEq<T, U>) -> &'a mut U {
    substitute::<_, _, MutRefF>(t, ev)
}

/// The [`TypeFunction`] `ApF<SliceF<N>, A> == [A; N]`
pub struct SliceF<const N: usize>(PhantomData<*const [(); N]>);
impl<A, const N: usize> TypeFunction<A> for SliceF<N> {
    type Result = [A; N];
}

/// A trait for type level functions, mapping type arguments to type results.
///
/// Note that `Self` is used only as a marker. See also [`substitute`], which implements coercing of results.
pub trait TypeFunction<Arg: ?Sized> {
    /// The type that `Arg` is mapped to by the implementor.
    type Result: ?Sized;
}

/// The result of applying the [`TypeFunction`] `F` to `T`.
pub type ApF<F, T> = <F as TypeFunction<T>>::Result;

/// Our internal workhorse for most of the other coerce implementations, lifting the equality through
/// an arbitrary [`TypeFunction`]. Do consider using this before writing a custom Consumer.
#[inline(always)]
pub fn substitute<T: ?Sized, U: ?Sized, F: TypeFunction<T> + TypeFunction<U>>(
    t: ApF<F, T>,
    ev: TypeEq<T, U>,
) -> ApF<F, U>
where
    ApF<F, T>: Sized,
    ApF<F, U>: Sized,
{
    struct FunCoercer<T: ?Sized, F: TypeFunction<<T as AliasSelf>::Alias>>(F::Result);

    impl<T: ?Sized, U: ?Sized, F: TypeFunction<T> + TypeFunction<U>> Consumer<T, U> for FunCoercer<T, F>
    where
        ApF<F, U>: Sized,
    {
        type Result = ApF<F, U>;
        fn consume_eq(self) -> Self::Result
        where
            T: IsEqual<U>,
        {
            self.0
        }
    }
    let con: FunCoercer<T, F> = FunCoercer(t);
    ev.use_eq(con)
}

/// A [`TypeFunction`] version of the Martin-Löf identity type:
/// `ApF<LoefIdF<T>, U> == TypeEq<T, U>`.
pub struct LoefIdF<T: ?Sized>(PhantomData<T>);
impl<T: ?Sized, Arg: ?Sized> TypeFunction<Arg> for LoefIdF<T> {
    type Result = TypeEq<T, Arg>;
}
/// [`LoefIdF`] flipped, i.e. `ApF<LoefIdFlippedF<T>, U> == TypeEq<U, T>`
pub struct LoefIdFlippedF<T: ?Sized>(PhantomData<T>);
impl<T: ?Sized, Arg: ?Sized> TypeFunction<Arg> for LoefIdFlippedF<T> {
    type Result = TypeEq<Arg, T>;
}

/// Composition for [`TypeFunction`]s, i.e. `ApF<ComposeF<F, G>, T> == ApF<F, ApF<G, T>>`
pub struct ComposeF<F: ?Sized, G: ?Sized>(PhantomData<F>, PhantomData<G>);
impl<F: ?Sized, G: ?Sized, Arg: ?Sized> TypeFunction<Arg> for ComposeF<F, G>
where
    G: TypeFunction<Arg>,
    F: TypeFunction<G::Result>,
{
    type Result = F::Result;
}

impl<T: ?Sized> TypeEq<T, T> {
    /// Same as [`crate::refl`].
    pub const fn refl() -> TypeEq<T, T> {
        self::refl()
    }
}

impl<T: ?Sized, U: ?Sized> TypeEq<T, U> {
    /// Same as [`crate::trivial_eq`].
    pub const fn trivial() -> Self
    where
        T: IsEqual<U>,
    {
        self::trivial_eq()
    }
    /// Same as [`crate::substitute`].
    #[inline]
    pub fn substitute<F: TypeFunction<T> + TypeFunction<U>>(self, t: ApF<F, T>) -> ApF<F, U>
    where
        ApF<F, T>: Sized,
        ApF<F, U>: Sized,
    {
        self::substitute::<_, _, F>(t, self)
    }
    /// Same as [`crate::coerce`]. Note that this is operationally a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// # use type_equalities::refl;
    /// assert_eq!(refl().coerce(42), 42);
    /// ```
    #[inline]
    pub fn coerce(self, t: T) -> U
    where
        T: Sized,
        U: Sized,
    {
        self::coerce(t, self)
    }
    /// Lift the type equality through any [`TypeFunction`]
    pub fn lift_through<F: TypeFunction<T> + TypeFunction<U>>(
        self,
    ) -> TypeEq<ApF<F, T>, ApF<F, U>> {
        type R<T, F> = ComposeF<LoefIdF<ApF<F, T>>, F>;
        self.substitute::<R<T, F>>(refl())
    }
    /// Get the inverse equality. `T == U  ==>  U == T`
    pub fn invert(self) -> TypeEq<U, T> {
        self.substitute::<LoefIdFlippedF<T>>(refl())
    }
    /// Apply transitivity. `T == U  ==>  U == V  ==>  T == V`
    pub fn trans<V: ?Sized>(self, rhs: TypeEq<U, V>) -> TypeEq<T, V> {
        rhs.substitute::<LoefIdF<T>>(self)
    }
}

impl<T: ?Sized, U: ?Sized> TypeEq<T, U> {
    /// Use the observed equality to call the consumer to compute a result.
    ///
    /// Consider using either [`TypeEq::coerce`] or [`TypeEq::lift_through`] first.
    #[inline(always)]
    pub fn use_eq<C: Consumer<T, U>>(self, c: C) -> C::Result {
        use_kernel_eq(self._inner, c)
    }
}

mod kernel {
    use super::Consumer;
    #[cfg(feature = "std")]
    use alloc::boxed::Box;
    use core::marker::PhantomData;
    #[cfg(not(feature = "std"))]
    core::compile_error!(
        "Currently core-only is not supported, but reserved for the future. The reason is technical, internally
        Box is used to do a transmute of trait objects. If you know how to work around this, please open an issue.
        For the meanwhile, 'alloc' has to be available.");

    pub(crate) struct TheEq<T: ?Sized, U: ?Sized> {
        _phantomt: PhantomData<*const T>,
        _phantomu: PhantomData<*const U>,
    }

    impl<T: ?Sized, U: ?Sized> Clone for TheEq<T, U> {
        fn clone(&self) -> Self {
            *self
        }
    }
    impl<T: ?Sized, U: ?Sized> Copy for TheEq<T, U> {}

    pub(crate) const fn refl<T: ?Sized>() -> TheEq<T, T> {
        // This is the only place where a TypeEq is constructed
        TheEq {
            _phantomt: PhantomData,
            _phantomu: PhantomData,
        }
    }

    pub(crate) fn use_eq<T: ?Sized, U: ?Sized, C: Consumer<T, U>>(
        _: TheEq<T, U>,
        c: C,
    ) -> C::Result {
        // By our invariant of only constructing `TheEq<T, T>`, we know here that `U = T`.
        // Use this to transmute the consumer
        let ref_c: Box<dyn Consumer<T, U, Result = C::Result>> = Box::new(c);
        let tref_c: Box<dyn Consumer<T, T, Result = C::Result>> =
            unsafe { core::mem::transmute(ref_c) };
        <dyn Consumer<T, T, Result = C::Result> as Consumer<T, T>>::consume_eq(*tref_c)
    }
}

/// Optionally obtain a type equality if the type checker can solve `T == U`.
///
/// Note that this depends on `#![feature(specialization)]` and works by overloading
/// some defined instances. Do not depend on always getting back a `Some(..)`, but
/// it will work fine in the simple cases.
///
/// # Examples
///
/// ```
/// # use type_equalities::maybe_type_eq;
/// assert_eq!(maybe_type_eq::<u32, u32>().unwrap().coerce(42), 42);
/// ```
#[cfg(feature = "test-for-type-equality")]
pub const fn maybe_type_eq<T: ?Sized, U: ?Sized>() -> Option<TypeEq<T, U>> {
    // Helper trait. `VALUE` is false, except for the specialization of the
    // case where `T == U`.
    trait ObsTypeEq<U: ?Sized> {
        const VALUE: Option<TypeEq<Self, U>>;
    }

    // Default implementation.
    impl<T: ?Sized, U: ?Sized> ObsTypeEq<U> for T {
        default const VALUE: Option<TypeEq<T, U>> = None;
    }
    // Specialization for `T == U`.
    impl<T: ?Sized> ObsTypeEq<T> for T {
        const VALUE: Option<TypeEq<T, T>> = Some(refl::<T>());
    }

    <T as ObsTypeEq<U>>::VALUE
}

#[cfg(all(test, feature = "test-for-type-equality"))]
mod test {
    use super::*;

    fn test_type_eq<T, U>(t: T) -> Option<U> {
        match maybe_type_eq() {
            None => None,
            Some(eq) => Some(eq.coerce(t)),
        }
    }

    #[test]
    fn test_some_integers() {
        assert_eq!(test_type_eq::<i32, i32>(0), Some(0));
        assert_eq!(test_type_eq::<&i32, &i32>(&0).copied(), Some(0));
        assert_eq!(test_type_eq::<&i32, i32>(&0), None);
        assert_eq!(test_type_eq::<i32, u32>(0), None);
    }
}

#[cfg(all(test, feature = "std"))]
mod benches {
    use super::*;
    use test::Bencher;

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
