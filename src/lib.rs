//! Easily destructure an iterator as if it were an array.
//!
//! Provides the [`TakeExact`] trait, which implements two [`Iterator`] consumer methods:
//! - [`take_exact`]
//! - [`take_exact_else`]
//!
//! Both attempt to construct a fixed-size array from the iterator, but [`take_exact_else`] takes
//! closures to lazily generate its error values.
//!
//! [`take_exact`]: TakeExact::take_exact
//! [`take_exact_else`]: TakeExact::take_exact_else

use ::core::mem::{MaybeUninit, transmute_copy};

/// An iterator that can facilitate the fallible construction of a fixed-size array.
///
/// # Examples
///
/// ```
/// # use crate::take_exact::TakeExact;
/// let names = "John Adam Doe".split_whitespace();
///
/// assert_eq!(
///     names.clone().take_exact("too few", "too many"),
///     Ok(["John", "Adam", "Doe"]),
/// );
/// assert_eq!(
///     names.clone().take_exact::<4>("too few", "too many"),
///     Err("too few"),
/// );
/// assert_eq!(
///     names.clone().take_exact::<2>("too few", "too many"),
///     Err("too many"),
/// );
/// ```
///
/// In most reasonable situations, such as when destructuring into a pattern, `N` can be inferred.
///
/// ```
/// # use crate::take_exact::TakeExact;
/// let names = "John Adam Doe".split_whitespace();
/// let [first, middle, last] = names.take_exact("too few", "too many")?;
/// # Ok::<(), &'static str>(())
/// ```
///
/// If your error values are the results of function calls, consider using the
/// [`take_exact_else`](TakeExact::take_exact_else) method instead of
/// [`take_exact`](TakeExact::take_exact).
pub trait TakeExact<E>: Iterator + Sized {
    /// Attempts to construct a fixed-size array from this iterator.
    ///
    /// For this operation to succeed, the iterator must have exactly `N` elements left. If there
    /// are too few or too many, the corresponding error function is called.
    ///
    /// This is sort of analagous to collecting the elements of the iterator into a `Vec` and
    /// checking the length afterwards, but there are a few key differences:
    /// - Nothing is allocated on the heap.
    /// - The returned array is **guaranteed** to be `N` elements long at compile-time.
    ///   - This allows users to cleanly destructure the array into variables and whatnot.
    fn take_exact_else<const N: usize>(
        mut self,
        if_too_few: impl FnOnce() -> E,
        if_too_many: impl FnOnce() -> E,
    ) -> Result<[Self::Item; N], E> {
        let mut taken: [MaybeUninit<Self::Item>; N] = [const { MaybeUninit::uninit() }; N];
        for i in 0..N {
            if let Some(x) = self.next() {
                unsafe { taken.get_unchecked_mut(i) }.write(x);
            } else {
                for element in &mut taken[..i] {
                    unsafe { element.assume_init_drop() };
                }
                return Err(if_too_few());
            }
        }
        let taken = unsafe { transmute_copy::<_, [Self::Item; N]>(&taken) };
        if self.next().is_none() {
            Ok(taken)
        } else {
            Err(if_too_many())
        }
    }

    /// Attempts to construct a fixed-size array from this iterator.
    ///
    /// For this operation to succeed, the iterator must have exactly `N` elements left. If there
    /// are too few or too many, the corresponding error function is called.
    ///
    /// This is sort of analagous to collecting the elements of the iterator into a [`Vec`] and
    /// checking the length afterwards, but there are a few key differences:
    /// - Nothing is allocated on the heap.
    /// - The returned array is **guaranteed** to be `N` elements long at compile-time.
    ///   - This allows users to cleanly destructure the array into variables and whatnot.
    ///
    /// Errors are eagerly evaluated; if they are the results of function calls, consider using
    /// [`take_exact_else`](TakeExact::take_exact_else) instead.
    fn take_exact<const N: usize>(self, too_few: E, too_many: E) -> Result<[Self::Item; N], E> {
        self.take_exact_else(|| too_few, || too_many)
    }
}

pub trait TakeAtLeast<E>: Iterator {
    fn take_at_least_else<const N: usize>(
        &mut self,
        if_too_few: impl FnOnce() -> E,
    ) -> Result<[Self::Item; N], E> {
        let mut taken: [MaybeUninit<Self::Item>; N] = [const { MaybeUninit::uninit() }; N];
        for i in 0..N {
            if let Some(x) = self.next() {
                unsafe { taken.get_unchecked_mut(i) }.write(x);
            } else {
                for element in &mut taken[..i] {
                    unsafe { element.assume_init_drop() };
                }
                return Err(if_too_few());
            }
        }
        Ok(unsafe { transmute_copy::<_, [Self::Item; N]>(&taken) })
    }

    fn take_at_least<const N: usize>(&mut self, too_few: E) -> Result<[Self::Item; N], E> {
        self.take_at_least_else(|| too_few)
    }
}

impl<T: Iterator, E> TakeAtLeast<E> for T {}
impl<T: Sized + TakeAtLeast<E>, E> TakeExact<E> for T {
    fn take_exact_else<const N: usize>(
        mut self,
        if_too_few: impl FnOnce() -> E,
        if_too_many: impl FnOnce() -> E,
    ) -> Result<[Self::Item; N], E> {
        let taken = self.take_at_least_else(if_too_few)?;
        if self.next().is_none() {
            Ok(taken)
        } else {
            Err(if_too_many())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::TakeExact;

    #[test]
    fn good_abc() {
        assert_eq!(
            // the turbofish is unnecessary here, but it can be important in other situations
            "abc".chars().take_exact::<3>("too few", "too many"),
            Ok(['a', 'b', 'c'])
        );
    }

    #[test]
    fn bad_abc_too_few() {
        assert_eq!(
            "abc".chars().take_exact::<4>("too few", "too many"),
            Err("too few"),
        );
    }

    #[test]
    fn bad_abc_too_many() {
        assert_eq!(
            "abc".chars().take_exact::<2>("too few", "too many"),
            Err("too many"),
        );
    }
}
