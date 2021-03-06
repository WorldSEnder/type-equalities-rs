// Copyright (c) 2021 t WorldSEnder
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>,
// at your option. All files in the project carrying such
// notice may not be copied, modified, or distributed except
// according to those terms.
#![cfg_attr(feature = "test-for-type-equality", feature(specialization))]
#![cfg_attr(unstable_feature, feature(const_fn_trait_bound))]
#![cfg_attr(unstable_feature, feature(doc_cfg))]
#![warn(missing_docs, rustdoc::missing_crate_level_docs)]
#![no_std]
//! Implements [`TypeEq`] that can be passed around and used at runtime to safely coerce values,
//! references and other structures dependending on these types.
//!
//! The equality type is zero-sized, and the coercion should optimize to a no-op in all cases.
//!
//! This crate is `![no_std]`. You can optionally turn off the `alloc` feature.

extern crate core;
use core::marker::PhantomData;

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "alloc")]
use alloc::boxed::Box;

use details::*;
use kernel::{refl as refl_kernel, use_eq as use_kernel_eq, TheEq};
use type_functions::*;

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
///
/// It is important to note that the `TypeEq` is [invariant]
/// in both arguments.
///
/// ```compile_fail
/// # use type_equalities::TypeEq;
/// fn coerce_lt<'a, 'b: 'a, T>(eq: TypeEq<&'b T, &'b T>)
///     -> TypeEq<&'b T, &'a T>
/// {
///     eq
/// }
/// ```
///
/// ```compile_fail
/// # use type_equalities::TypeEq;
/// fn coerce_lt_inv<'a, 'b: 'a, T>(eq: TypeEq<&'a T, &'a T>)
///     -> TypeEq<&'a T, &'b T>
/// {
///     eq
/// }
/// ```
///
/// Unsizing also does not work for TypeEq.
///
/// ```compile_fail
/// fn coerce_dyn<T: core::fmt::Debug>(eq: &TypeEq<T, T>)
///     -> &TypeEq<T, dyn core::fmt::Debug>
/// {
///     eq
/// }
/// ```
///
/// [invariant]: https://doc.rust-lang.org/nomicon/subtyping.html#variance
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
///
/// There is also a constructor-like version of this, [`TypeEq::refl`].
pub const fn refl<T: ?Sized>() -> TypeEq<T, T> {
    TypeEq {
        _inner: refl_kernel(),
    }
}

/// Construct evidence of `TypeEq<T, U>` under the constraint `T: IsEqual<U>`.
///
/// There is also a receiver version of this, [`TypeEq::trivial`].
///
/// Note quite as trivial to implement as it might appear, since we're fighting
/// the type checker a bit.
///
/// **Note**: this function is `const` only on nightly, since it depends on the
/// [`const_fn_trait_bound`] feature.
///
/// [`const_fn_trait_bound`]: https://doc.rust-lang.org/stable/unstable-book/language-features/const-fn-trait-bound.html
#[rustversion::attr(nightly, const)]
pub fn trivial_eq<T: ?Sized, U: ?Sized>() -> TypeEq<T, U>
where
    T: IsEqual<U>,
{
    const fn refl_alias<T: ?Sized>() -> TypeEq<T, <T as AliasSelf>::Alias> {
        refl()
    }
    refl_alias()
}

/// Coerce a value of type `T` to a value of type `U`, given evidence that `T == U`.
///
/// Note that this is operationally a no-op.
///
/// There is also a receiver version of this, [`TypeEq::coerce`].
///
/// # Examples
///
/// ```
/// # use type_equalities::{coerce, refl};
/// assert_eq!(coerce(42, refl()), 42);
/// ```
#[inline(always)]
pub fn coerce<T, U>(t: T, ev: TypeEq<T, U>) -> U {
    substitute::<_, _, IdF>(t, ev)
}

/// Coerce a value of type `Box<T>` to a value of type `Box<U>`, given evidence that `T == U`.
///
/// # Examples
///
/// ```
/// # use type_equalities::{coerce_box, refl};
/// assert_eq!(*coerce_box(Box::new(42), refl()), 42);
/// ```
#[cfg(feature = "alloc")]
#[rustversion::attr(nightly, doc(cfg(feature = "alloc")))]
#[inline]
pub fn coerce_box<T: ?Sized, U: ?Sized>(t: Box<T>, ev: TypeEq<T, U>) -> Box<U> {
    substitute::<_, _, BoxF>(t, ev)
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
pub fn coerce_ref<T: ?Sized, U: ?Sized>(t: &T, ev: TypeEq<T, U>) -> &U {
    substitute::<_, _, RefF>(t, ev)
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
pub fn coerce_mut<T: ?Sized, U: ?Sized>(t: &mut T, ev: TypeEq<T, U>) -> &mut U {
    substitute::<_, _, MutRefF>(t, ev)
}

/// Our workhorse for most of the other coerce implementations, lifting the equality through
/// an arbitrary [`TypeFunction`]. Do consider using this before writing a custom Consumer.
///
/// There is also a receiver version of this, [`TypeEq::substitute`].
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

    unsafe impl<T: ?Sized, U: ?Sized, F: TypeFunction<T> + TypeFunction<U>> Consumer<T, U>
        for FunCoercer<T, F>
    where
        ApF<F, U>: Sized,
    {
        type Result = ApF<F, U>;
        fn consume_eq(&self) -> Self::Result
        where
            T: IsEqual<U>,
        {
            let self_ = unsafe { core::ptr::read(self as *const Self) };
            self_.0
        }
    }
    let con: FunCoercer<T, F> = FunCoercer(t);
    ev.use_eq(con)
}

impl<T: ?Sized> TypeEq<T, T> {
    /// Same as [`crate::refl`].
    pub const fn refl() -> TypeEq<T, T> {
        self::refl()
    }
}

impl<T: ?Sized, U: ?Sized> TypeEq<T, U> {
    /// Same as [`crate::trivial_eq`].
    ///
    /// **Note**: this function is `const` only on nightly, since it depends on the
    /// [`const_fn_trait_bound`] feature.
    ///
    /// [`const_fn_trait_bound`]: https://doc.rust-lang.org/stable/unstable-book/language-features/const-fn-trait-bound.html
    #[rustversion::attr(nightly, const)]
    pub fn trivial() -> Self
    where
        T: IsEqual<U>,
    {
        self::trivial_eq()
    }
    /// Same as [`crate::substitute`].
    #[inline(always)]
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
    #[inline(always)]
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
    /// Apply transitivity. `T == U & U == V  ==>  T == V`
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

/// Details for primitively consuming an equality.
pub mod details {
    use crate::IsEqual;

    /// A consumer recives evidence of a type equality `T == U` and computes a result.
    ///
    /// # Safety
    ///
    /// See the docs of [`consume_eq`] for further safety.
    ///
    /// [`consume_eq`]: Self::consume_eq
    pub unsafe trait Consumer<T: ?Sized, U: ?Sized> {
        /// The result type returned from [`Consumer::consume_eq`].
        type Result;
        /// The strange `where` clause enables the consumer to observe that:
        /// - `T == <T as AssocSelf>::Alias` by the implementation of `AssocSelf`
        /// - `T::Alias == U`
        ///
        /// Directly writing `T = U` is currently not possible, as tracked by [issue #20041].
        ///
        /// [`AliasSelf`] is a workaround, to make it easier for implementors to construct their
        /// own `Consumer`s.
        ///
        /// # Safety
        ///
        /// `self` is passed as a const ref. Using [`ptr::read`] is guaranteed to be safe.
        /// If you do not read from it, your consumer will forgotten without running its
        /// destructor, as with [`mem::forget`].
        ///
        /// [issue #20041]: https://github.com/rust-lang/rust/issues/20041
        /// [`ptr::read`]: core::ptr::read
        /// [`mem::forget`]: core::mem::forget
        fn consume_eq(&self) -> Self::Result
        where
            T: IsEqual<U>;
    }

    /// Trait used to convince the rust type checker of the claimed equality.
    ///
    /// If your consumer takes a generic parameter `T`, store values with type
    /// `<T as AliasSelf>::Alias` instead of `T` directly. In `consume_eq`, the compiler
    /// will correctly reduce this to `U`, since it sees the `where` clause. Additionally,
    /// during construction (somewhere else), the compiler sees the `impl<T> AssocSelf for T`,
    /// correctly using the first equality. Thus, you shouldn't have to coerce consumers.
    ///
    pub trait AliasSelf {
        /// Always set to `Self`, but the type checker doesn't reduce `T::Alias` to `T`.
        type Alias: ?Sized;
    }
    impl<T: ?Sized> AliasSelf for T {
        type Alias = T;
    }
}

/// [`TypeFunction`]s have the amazing property that they can be used to push the equality of a
/// type-level argument through to an equality of the type-level result.
///
/// In this crate, helper structs are defined that implement `TypeFunction` with various resulting
/// types. These structs are then supposed to be passed to [`substitute`], [`TypeEq::substitute`]
/// and [`TypeEq::lift_through`].
///
/// # Example
///
/// ```
/// # use type_equalities::{refl, TypeEq};
/// # use type_equalities::type_functions::RefF;
/// let eq: TypeEq<&u32, &u32> = refl::<u32>().lift_through::<RefF<'_>>();
/// ```
///
pub mod type_functions {
    use super::*;
    #[cfg(feature = "alloc")]
    use alloc::boxed::Box;

    /// A trait for type level functions, mapping type arguments to type results.
    ///
    /// Note that `Self` is used only as a marker. See also [`substitute`], which implements coercing of results.
    pub trait TypeFunction<Arg: ?Sized> {
        /// The type that `Arg` is mapped to by the implementor.
        type Result: ?Sized;
    }
    /// The result of applying the [`TypeFunction`] `F` to `T`.
    pub type ApF<F, T> = <F as TypeFunction<T>>::Result;

    /// The identity [`TypeFunction`], `ApF<IdF, T> == T`. Coercing through this gives
    /// us the basic safe transmute.
    pub struct IdF;
    impl<A: ?Sized> TypeFunction<A> for IdF {
        type Result = A;
    }
    /// The [`TypeFunction`] `ApF<BoxF, A> == Box<A>`
    #[cfg(feature = "alloc")]
    #[rustversion::attr(nightly, doc(cfg(feature = "alloc")))]
    pub struct BoxF;
    #[cfg(feature = "alloc")]
    impl<A: ?Sized> TypeFunction<A> for BoxF {
        type Result = Box<A>;
    }
    /// The [`TypeFunction`] `ApF<RefF<'a>, A> == &'a A`
    pub struct RefF<'a>(PhantomData<&'a ()>);
    impl<'a, A: ?Sized + 'a> TypeFunction<A> for RefF<'a> {
        type Result = &'a A;
    }

    /// The [`TypeFunction`] `ApF<MutRefF<'a>, A> == &'a mut A`
    pub struct MutRefF<'a>(PhantomData<&'a ()>);
    impl<'a, A: ?Sized + 'a> TypeFunction<A> for MutRefF<'a> {
        type Result = &'a mut A;
    }

    /// The [`TypeFunction`] `ApF<SliceF<N>, A> == [A; N]`
    pub struct SliceF<const N: usize>(PhantomData<*const [(); N]>);
    impl<A, const N: usize> TypeFunction<A> for SliceF<N> {
        type Result = [A; N];
    }

    /// A [`TypeFunction`] version of the Martin-L??f identity type:
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
}

mod kernel {
    use crate::details::Consumer;
    use core::{marker::PhantomData, mem::ManuallyDrop, ops::Deref};

    pub(crate) struct TheEq<T: ?Sized, U: ?Sized> {
        _phantomt: PhantomData<*const core::cell::Cell<T>>,
        _phantomu: PhantomData<*const core::cell::Cell<U>>,
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
        let the_c = ManuallyDrop::new(c);
        let ref_c: &dyn Consumer<T, U, Result = C::Result> = the_c.deref();
        let tref_c: &dyn Consumer<T, T, Result = C::Result> =
            unsafe { core::mem::transmute(ref_c) };
        tref_c.consume_eq()
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
/// # fn run() -> Option<()> {
/// assert_eq!(maybe_type_eq::<u32, u32>()?.coerce(42), 42);
/// # Some(()) }
/// # run().ok_or("failed to prove equality")?;
/// # Ok::<(), &'static str>(())
/// ```
#[cfg(feature = "test-for-type-equality")]
#[rustversion::attr(nightly, doc(cfg(feature = "test-for-type-equality")))]
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
    use crate::*;

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
