//! The `GhostBorrowMut` trait, which allows mutably borrowing multiple `GhostCell`s simultaneously.
//!
//! This module implement the `GhostBorrowMut` trait for:
//!
//! -   A slice of `GhostCell`s.
//! -   An array of `GhostCell`s of any size.
//! -   A tuple of `GhostCell`s of up to 12 elements.
//! -   A tuple of references to `GhostCell`s of up to 12 elements.
//!
//! #   Performance
//!
//! In general borrowing is free of cost, however a special-case is necessary for the tuple of references, as then the
//! references may alias.
//!
//! #   Experimental
//!
//! The feature is experimental, to enable, use the feature "experimental-multiple-mutable-borrows".

use core::mem;
use core::ptr;

use crate::ghost_cell::*;

/// An error signifying that two `GhostCell`s that need to be distinct were actually the same cell.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct GhostAliasingError;

/// A void struct. Used as the error case when the error case is impossible.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum VoidError {}

impl VoidError {
    /// Returns any type. Can't happen since `VoidError` can't be constructed.
    pub fn absurd<T>(self) -> T {
        match self {}
        // could also be implemented as:
        // unsafe { core::hint::unreachable_unchecked() }
    }
}

// For uniformity, if anyone wants it. Can't do
// impl<T> From<VoidError> for T
// because of conflicting implementations.
impl From<VoidError> for GhostAliasingError {
    fn from(e: VoidError) -> Self {
        e.absurd()
    }
}

/// A trait for implementing multiple borrows for any number of arguments, using a `GhostToken<'a, 'brand>`.
///
/// Implemented for a mixture of tuple and array types.
///
/// #   Experimental
///
/// The feature is experimental, to enable, use the feature "experimental-multiple-mutable-borrows".
pub trait GhostBorrowMut<'a, 'brand> {
    /// The references you get as a result.
    ///
    /// For example, if `Self` is `(&'a GhostCell<'brand, T0>, &'a GhostCell<'brand, T1>)` then `Result` is
    /// `(&'a mut T0, &'a mut T1)`.
    type Result;

    /// The error case.
    ///
    /// Use a never type such as `!` or `VoidError` if an error is impossible, and `GhostAliasingError` otherwise.
    type Error: Into<GhostAliasingError>;

    /// Borrows any number of `GhostCell`s mutably at the same time.
    ///
    /// If any of them are the same `GhostCell`, returns `Error`.
    ///
    /// #   Performance
    ///
    /// In general, borrowing should be free of cost if possible. This can be ascertained by checking the error type:
    /// if it is a never type, then the operation is infallible, indicating no run-time check is necessary.
    ///
    /// If the operation is not infallible, then a runtime check is necessary, in which case the unchecked version of
    /// the operation may be used if performance matters and the caller is certain of the absence of problems.
    ///
    /// #   Example
    ///
    /// ```rust
    /// use ghost_cell::{GhostToken, GhostCell, GhostBorrowMut};
    ///
    /// let value = GhostToken::new(|mut token| {
    ///     let cell1 = GhostCell::new(42);
    ///     let cell2 = GhostCell::new(47);
    ///
    ///     let (reference1, reference2): (&mut i32, &mut i32)
    ///         = (&cell1, &cell2).borrow_mut(&mut token).unwrap();
    ///     *reference1 = 33;
    ///     *reference2 = 34;
    ///     // here we stop mutating, so the token isn't mutably borrowed anymore, and we can read again
    ///
    ///     (*cell1.borrow(&token), *cell2.borrow(&token))
    /// });
    ///
    /// assert_eq!((33, 34), value);
    /// ```
    fn borrow_mut(self, token: &'a mut GhostToken<'brand>) -> Result<Self::Result, Self::Error>;

    /// Borrows any number of `GhostCell`s at the same time, infallibly.
    ///
    /// #   Safety
    ///
    /// The caller guarantees that the various `GhostCell`s do not alias.
    unsafe fn borrow_mut_unchecked(self, token: &'a mut GhostToken<'brand>) -> Self::Result;
}

impl<'a, 'brand, T> GhostBorrowMut<'a, 'brand> for &'a [GhostCell<'brand, T>] {
    type Result = &'a mut [T];
    type Error = VoidError;

    fn borrow_mut(self, token: &'a mut GhostToken<'brand>) -> Result<Self::Result, Self::Error> {
        //  Safety:
        //  -   All cells are adjacent in memory, hence distinct from one another.
        Ok(unsafe { self.borrow_mut_unchecked(token) })
    }

    unsafe fn borrow_mut_unchecked(self, _: &'a mut GhostToken<'brand>) -> Self::Result {
        //  Safety:
        //  -   Exclusive access to the `GhostToken` ensures exclusive access to the cells' content, if unaliased.
        //  -   `GhostCell` is `repr(transparent)`, hence `T` and `GhostCell<T>` have the same memory representation.
        //  -   All cells are adjacent in memory, hence distinct from one another.
        #[allow(mutable_transmutes)]
        mem::transmute::<Self, Self::Result>(self)
    }
}

impl<'a, 'brand, T, const N: usize> GhostBorrowMut<'a, 'brand> for &'a [GhostCell<'brand, T>; N] {
    type Result = &'a mut [T; N];
    type Error = VoidError;

    fn borrow_mut(self, token: &'a mut GhostToken<'brand>) -> Result<Self::Result, Self::Error> {
        //  Safety:
        //  -   All cells are adjacent in memory, hence distinct from one another.
        Ok(unsafe { self.borrow_mut_unchecked(token) })
    }

    unsafe fn borrow_mut_unchecked(self, _: &'a mut GhostToken<'brand>) -> Self::Result {
        //  Safety:
        //  -   Exclusive access to the `GhostToken` ensures exclusive access to the cells' content, if unaliased.
        //  -   `GhostCell` is `repr(transparent)`, hence `T` and `GhostCell<T>` have the same memory representation.
        //  -   All cells are adjacent in memory, hence distinct from one another.
        #[allow(mutable_transmutes)]
        mem::transmute::<Self, Self::Result>(self)
    }
}


impl<'a, 'brand, T: ?Sized, const N: usize> GhostBorrowMut<'a, 'brand> for [&'a GhostCell<'brand, T>; N] {
    type Result = [&'a mut T; N];
    type Error = GhostAliasingError;

    fn borrow_mut(self, token: &'a mut GhostToken<'brand>) -> Result<Self::Result, Self::Error> {
        //  Safety:
        //  -   `[&'a GhostCell<'brand, T>; N]` and `[*const T; N]` have the same size.
        //  -   `[&'a GhostCell<'brand, T>; N]` implements `Copy`, so no `mem::forget` is needed.
        //  -   We can't use `mem::transmute`, because of https://github.com/rust-lang/rust/issues/61956.
        //  Note: We can't cast to a `*const [*const (); N]` to immediately extract addresses due to the size/layout of fat pointers;
        //        see https://github.com/matthieu-m/ghost-cell/pull/16#discussion_r884114694 for more details.
        check_distinct(unsafe { ptr::read(&self as *const _ as *const [*const T; N]) })?;

        //  Safety:
        //  -   The cells were checked to be distinct.
        Ok(unsafe { self.borrow_mut_unchecked(token) })
    }

    unsafe fn borrow_mut_unchecked(self, _: &'a mut GhostToken<'brand>) -> Self::Result {
        //  Safety:
        //  -   Exclusive access to the `GhostToken` ensures exclusive access to the cells' content, if unaliased.
        //  -   The caller guarantees the cells are not aliased.
        //  -   `[&'a GhostCell<'brand, T>; N]` and `[&'a mut T; N]` have the same size.
        //  -   `[&'a GhostCell<'brand, T>; N]` implements `Copy`, so no `mem::forget` is needed.
        //  -   We can't use `mem::transmute`, because of https://github.com/rust-lang/rust/issues/61956.
        ptr::read(&self as *const _ as *const Self::Result)
    }
}

macro_rules! last {
    () => {};
    ($head:ident $(,)?) => {
        $head
    };
    ($head:ident, $($tail:ident),+ $(,)?) => {
        last!($($tail),+)
    };
}

macro_rules! generate_public_instance {
    ( $($name:ident),* ; $($type_letter:ident),* ) => {
        impl<'a, 'brand, $($type_letter: ?Sized,)*> GhostBorrowMut<'a, 'brand>
            for ( $(&'a GhostCell<'brand, $type_letter>, )* )
        {
            type Result = ( $(&'a mut $type_letter, )* );
            type Error = GhostAliasingError;

            fn borrow_mut(self, token: &'a mut GhostToken<'brand>) -> Result<Self::Result, Self::Error> {
                let ($($name,)*) = self;

                //  We go ahead and convert to thin pointers here because unlike the `[&'a GhostCell<'brand, T>; N]` impl,
                //  we're constructing the array ourselves, so there's no layout issues to worry about.
                check_distinct([ $( $name as *const _ as *const (), )* ])?;

                //  Safety:
                //  -   The cells were checked to be distinct.
                Ok(unsafe { self.borrow_mut_unchecked(token) })
            }

            unsafe fn borrow_mut_unchecked(self, _: &'a mut GhostToken<'brand>) -> Self::Result {
                let ($($name,)*) = self;

                //  Safety:
                //  -   Exclusive access to the `GhostToken` ensures exclusive access to the cells' content, if unaliased.
                //  -   The caller guarantees the cells are not aliased.
                ( $( &mut * $name.as_ptr(),)* )
            }
        }

        impl<'a, 'brand, $($type_letter,)*> GhostBorrowMut<'a, 'brand>
            for &'a ( $(GhostCell<'brand, $type_letter>, )* )
        where
            last!( $($type_letter),* ): ?Sized
        {
            type Result = &'a mut ( $($type_letter, )* );
            type Error = VoidError;

            fn borrow_mut(self, token: &'a mut GhostToken<'brand>) -> Result<Self::Result, Self::Error> {
                //  Safety:
                //  -   All cells are adjacent in memory, hence distinct from one another.
                Ok(unsafe { self.borrow_mut_unchecked(token) })
            }

            unsafe fn borrow_mut_unchecked(self, _: &'a mut GhostToken<'brand>) -> Self::Result {
                //  Safety:
                //  -   Exclusive access to the `GhostToken` ensures exclusive access to the cells' content, if unaliased.
                //  -   `GhostCell` is `repr(transparent)`, hence `T` and `GhostCell<T>` have the same memory representation.
                //  -   All cells are adjacent in memory, hence distinct from one another.
                #[allow(mutable_transmutes)]
                core::mem::transmute::<Self, Self::Result>(self)
            }
        }
    };
}

generate_public_instance!(a ; T0);
generate_public_instance!(a, b ; T0, T1);
generate_public_instance!(a, b, c ; T0, T1, T2);
generate_public_instance!(a, b, c, d ; T0, T1, T2, T3);
generate_public_instance!(a, b, c, d, e ; T0, T1, T2, T3, T4);
generate_public_instance!(a, b, c, d, e, f ; T0, T1, T2, T3, T4, T5);
generate_public_instance!(a, b, c, d, e, f, g ; T0, T1, T2, T3, T4, T5, T6);
generate_public_instance!(a, b, c, d, e, f, g, h ; T0, T1, T2, T3, T4, T5, T6, T7);
generate_public_instance!(a, b, c, d, e, f, g, h, i ; T0, T1, T2, T3, T4, T5, T6, T7, T8);
generate_public_instance!(a, b, c, d, e, f, g, h, i, j ; T0, T1, T2, T3, T4, T5, T6, T7, T8, T9);
generate_public_instance!(a, b, c, d, e, f, g, h, i, j, k ; T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA);
generate_public_instance!(a, b, c, d, e, f, g, h, i, j, k, l ; T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB);

//
//  Implementation
//

/// Returns `Ok(())` if the inputs are distinct, and `Err(GhostAliasingError)` otherwise.
/// 
/// Ignores the metadata of the given pointers if they are fat, only comparing their addresses.
fn check_distinct<T: ?Sized, const N: usize>(mut arr: [*const T; N]) -> Result<(), GhostAliasingError> {
    if N <= 10 {
        for i in 0..N {
            for j in 0..i {
                if core::ptr::eq(arr[i] as *const (), arr[j] as *const ()) {
                    return Err(GhostAliasingError);
                }
            }
        }
    } else {
        arr.sort_unstable();
        for i in 0..(N - 1) {
            if core::ptr::eq(arr[i] as *const (), arr[i + 1] as *const ()) {
                return Err(GhostAliasingError);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {

use super::*;

#[test]
fn multiple_borrows_tuple() {
    let value = GhostToken::new(|mut token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let cell4 = GhostCell::new(9);

        let (reference1, reference2, reference3, reference4): (&mut i32, &mut i32, &mut i32, &mut i32)
            = (&cell1, &cell2, &cell3, &cell4).borrow_mut(&mut token).unwrap();
        *reference1 = 33;
        *reference2 = 34;
        *reference3 = 35;
        *reference4 = 36;

        // here we stop mutating, so the token isn't mutably borrowed anymore, and we can read again
        (*cell1.borrow(&token), *cell2.borrow(&token), *cell3.borrow(&token))
    });
    assert_eq!((33, 34, 35), value);
}

#[test]
#[should_panic]
fn multiple_borrows_tuple_aliased() {
    GhostToken::new(|mut token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let _: (&mut i32, &mut i32, &mut i32, &mut i32)
            = (&cell1, &cell2, &cell3, &cell2).borrow_mut(&mut token).unwrap();
    });
}

#[test]
fn multiple_borrows_tuple_ref() {
    let value = GhostToken::new(|mut token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let cell4 = GhostCell::new(9);
        let tuple = (cell1, cell2, cell3, cell4);

        let reference: &mut (i32, i32, i32, i32)
            = tuple.borrow_mut(&mut token).unwrap();
        reference.0 = 33;
        reference.1 = 34;
        reference.2 = 35;
        reference.3 = 36;

        // here we stop mutating, so the token isn't mutably borrowed anymore, and we can read again
        (*tuple.0.borrow(&token), *tuple.1.borrow(&token), *tuple.2.borrow(&token))
    });
    assert_eq!((33, 34, 35), value);
}

#[test]
fn multiple_borrows_array_ref() {
    let value = GhostToken::new(|mut token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let cell4 = GhostCell::new(9);
        let array = [cell1, cell2, cell3, cell4];

        let reference: &mut [i32; 4]
            = array.borrow_mut(&mut token).unwrap();
        reference[0] = 33;
        reference[1] = 34;
        reference[2] = 35;
        reference[3] = 36;

        // here we stop mutating, so the token isn't mutably borrowed anymore, and we can read again
        (*array[0].borrow(&token), *array[1].borrow(&token), *array[2].borrow(&token))
    });
    assert_eq!((33, 34, 35), value);
}

//  Trait suitable for testing the mutable borrowing of trait objects
trait Store {
    type Item;

    fn get(&self) -> Self::Item;

    fn set(&mut self, x: Self::Item);
}

impl Store for i32 {
    type Item = Self;

    fn get(&self) -> Self::Item {
        *self
    }

    fn set(&mut self, x: Self::Item) {
        *self = x;
    }
}

#[test]
fn multiple_borrows_tuple_unsized() {
    let value = GhostToken::new(|mut token| {
        let mut data1 = 42;
        let mut data2 = [47];
        let mut data3 = 7;
        let mut data4 = [9];

        let cell1 = &*GhostCell::from_mut(&mut data1 as &mut dyn Store<Item = i32>);
        let cell2 = &*GhostCell::from_mut(&mut data2 as &mut [i32]);
        let cell3 = &*GhostCell::from_mut(&mut data3 as &mut dyn Store<Item = i32>);
        let cell4 = &*GhostCell::from_mut(&mut data4 as &mut [i32]);

        let (reference1, reference2, reference3, reference4)
            = (cell1, cell2, cell3, cell4).borrow_mut(&mut token).unwrap();
        reference1.set(7);
        reference3.set(42);
        mem::swap(&mut reference2[0], &mut reference4[0]);

        (reference1.get(), reference2[0], reference3.get(), reference4[0])
    });
    assert_eq!((7, 9, 42, 47), value);
}

#[test]
fn multiple_borrows_array_unsized_slice() {
    let value = GhostToken::new(|mut token| {
        let mut data1 = [42];
        let mut data2 = [47];
        let mut data3 = [7];
        let mut data4 = [9];

        let cell1 = &*GhostCell::from_mut(&mut data1 as &mut [i32]);
        let cell2 = &*GhostCell::from_mut(&mut data2 as &mut [i32]);
        let cell3 = &*GhostCell::from_mut(&mut data3 as &mut [i32]);
        let cell4 = &*GhostCell::from_mut(&mut data4 as &mut [i32]);
        let array = [cell1, cell2, cell3, cell4];

        let reference: [&mut [i32]; 4] = array.borrow_mut(&mut token).unwrap();
        reference[0][0] = 33;
        reference[1][0] = 34;
        reference[2][0] = 35;
        reference[3][0] = 36;

        (array[0].borrow(&token)[0], array[1].borrow(&token)[0], array[2].borrow(&token)[0])
    });
    assert_eq!((33, 34, 35), value);
}

#[test]
fn multiple_borrows_array_unsized_dyn_trait() {
    let value = GhostToken::new(|mut token| {
        let mut data1 = 42;
        let mut data2 = 47;
        let mut data3 = 7;
        let mut data4 = 9;

        let cell1 = &*GhostCell::from_mut(&mut data1 as &mut dyn Store<Item = i32>);
        let cell2 = &*GhostCell::from_mut(&mut data2 as &mut dyn Store<Item = i32>);
        let cell3 = &*GhostCell::from_mut(&mut data3 as &mut dyn Store<Item = i32>);
        let cell4 = &*GhostCell::from_mut(&mut data4 as &mut dyn Store<Item = i32>);
        let array = [cell1, cell2, cell3, cell4];

        let reference: [&mut dyn Store<Item = i32>; 4] = array.borrow_mut(&mut token).unwrap();
        reference[0].set(33);
        reference[1].set(34);
        reference[2].set(35);
        reference[3].set(36);

        (array[0].borrow(&token).get(), array[1].borrow(&token).get(), array[2].borrow(&token).get())
    });
    assert_eq!((33, 34, 35), value);
}

#[test]
#[should_panic]
fn multiple_borrows_tuple_unsized_aliased() {
    GhostToken::new(|mut token| {
        let mut data1 = 42;
        let mut data2 = [47];
        let mut data3 = 7;

        let cell1 = &*GhostCell::from_mut(&mut data1 as &mut dyn Store<Item = i32>);
        let cell2 = &*GhostCell::from_mut(&mut data2 as &mut [i32]);
        let cell3 = &*GhostCell::from_mut(&mut data3 as &mut dyn ToString);

        let _: (&mut dyn Store<Item = i32>, &mut [i32], &mut dyn ToString, &mut [i32])
            = (cell1, cell2, cell3, cell2).borrow_mut(&mut token).unwrap();
    });
}

#[test]
#[should_panic]
fn multiple_borrows_array_unsized_slice_aliased() {
    GhostToken::new(|mut token| {
        let mut data1 = [42];
        let mut data2 = [47];
        let mut data3 = [7];

        let cell1 = &*GhostCell::from_mut(&mut data1 as &mut [i32]);
        let cell2 = &*GhostCell::from_mut(&mut data2 as &mut [i32]);
        let cell3 = &*GhostCell::from_mut(&mut data3 as &mut [i32]);
        let array = [cell1, cell2, cell3, cell2];

        let _: [&mut [i32]; 4] = array.borrow_mut(&mut token).unwrap();
    });
}

#[test]
#[should_panic]
fn multiple_borrows_array_unsized_dyn_trait_aliased() {
    GhostToken::new(|mut token| {
        let mut data1 = 42;
        let mut data2 = 47;
        let mut data3 = 7;

        let cell1 = &*GhostCell::from_mut(&mut data1 as &mut dyn Store<Item = i32>);
        let cell2 = &*GhostCell::from_mut(&mut data2 as &mut dyn Store<Item = i32>);
        let cell3 = &*GhostCell::from_mut(&mut data3 as &mut dyn Store<Item = i32>);
        let array = [cell1, cell2, cell3, cell2];

        let _: [&mut dyn Store<Item = i32>; 4] = array.borrow_mut(&mut token).unwrap();
    });
}

#[test]
fn check_distinct() {
    // small array
    GhostToken::new(|mut token| {
        let cells = [
            GhostCell::new(1),
            GhostCell::new(2),
            GhostCell::new(3),
            GhostCell::new(4),
            GhostCell::new(5),
            GhostCell::new(6),
        ];

        // no aliasing
        let tuple1 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5]);
        assert!(tuple1.borrow_mut(&mut token).is_ok());

        // aliasing at start/end
        let tuple2 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[0]);
        assert!(tuple2.borrow_mut(&mut token).is_err());
    });

    // big array
    GhostToken::new(|mut token| {
        let cells = [
            GhostCell::new(1),
            GhostCell::new(2),
            GhostCell::new(3),
            GhostCell::new(4),
            GhostCell::new(5),
            GhostCell::new(6),
            GhostCell::new(7),
            GhostCell::new(8),
            GhostCell::new(9),
            GhostCell::new(10),
            GhostCell::new(11),
            GhostCell::new(12),
        ];

        // no aliasing
        let tuple1 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5], &cells[6], &cells[7], &cells[8], &cells[9], &cells[10], &cells[11]);
        assert!(tuple1.borrow_mut(&mut token).is_ok());

        // aliasing at start/end
        let tuple2 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5], &cells[6], &cells[7], &cells[8], &cells[9], &cells[10], &cells[0]);
        assert!(tuple2.borrow_mut(&mut token).is_err());

        // aliasing at the start
        let tuple3 = (&cells[0], &cells[0], &cells[1], &cells[3], &cells[4], &cells[5], &cells[6], &cells[7], &cells[8], &cells[9], &cells[10], &cells[11]);
        assert!(tuple3.borrow_mut(&mut token).is_err());

        // aliasing at the end
        let tuple4 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5], &cells[6], &cells[7], &cells[8], &cells[9], &cells[10], &cells[10]);
        assert!(tuple4.borrow_mut(&mut token).is_err());

        // aliasing in the middle
        let tuple5 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5], &cells[5], &cells[7], &cells[8], &cells[9], &cells[10], &cells[11]);
        assert!(tuple5.borrow_mut(&mut token).is_err());
    });
}

} // mod tests
