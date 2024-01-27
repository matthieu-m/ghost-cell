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

use core::{convert::Infallible, mem, ptr};

use crate::ghost_cell::*;

/// An error signifying that two `GhostCell`s that need to be distinct were actually the same cell.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct GhostAliasingError;

// For uniformity, if anyone wants it. Can't do
// impl<T> From<Infallible> for T
// because of conflicting implementations.
impl From<Infallible> for GhostAliasingError {
    fn from(_: Infallible) -> Self {
        unreachable!("Infallible cannot be constructed")
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
    /// Use a never type such as `!` or `Infallible` if an error is impossible, and `GhostAliasingError` otherwise.
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
    type Error = Infallible;

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
    type Error = Infallible;

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
        check_distinct(self.map(get_span))?;

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

                check_distinct([ $( get_span($name), )* ])?;

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
            type Error = Infallible;

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

//  Why Address?
//
//  1.  Dynamically-sized types (DST) require checking for memory range overlap, not just pointer equality.
//  2.  A value may be allocated at the very edge of the memory range, so that one-past-the-end would overflow (and
//      wrap around) in address space.
//
//  By using an integer one size up from the pointer size, we can guarantee that an exclusive range can successfully
//  represent the range of memory covered by a value, without risking any overflow.
//
//  As an optimization, `u64` is used on 64-bits targets since for now no 64-bits target make use of the full address
//  width, and using `u128` would be more costly.

#[cfg(target_pointer_width = "16")]
type Address = u32;

#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
type Address = u64;

//  Returns the _exclusive_ range of memory covered by the value.
fn get_span<T: ?Sized>(value: &T) -> (Address, Address) {
    assert!(mem::size_of::<usize>() <= mem::size_of::<Address>());

    let value_size = mem::size_of_val(value) as Address;

    let start = value as *const T as *const u8 as usize as Address;

    (start, start + value_size)
}

//  Returns `Ok(())` if the exclusive ranges do not overlap, and `Err(GhostAliasingError)` otherwise.
//
//  Assumes that the ranges are _exclusive_.
fn check_distinct<const N: usize>(mut array: [(Address, Address); N]) -> Result<(), GhostAliasingError> {
    //  Remove ZSTs, if any.
    let slice = select(&mut array, |&(start, end)| start < end);

    //  Sort slices by their start pointer.
    slice.sort_unstable_by_key(|t| t.0);

    //  Overlap can then be detected by whether the end of a slice overtakes the start of the next slice.
    for window in slice.windows(2) {
        //  Safety:
        //  -   `window` is guaranteed to have exactly 2 elements.
        let (left, right) = unsafe { (window.get_unchecked(0), window.get_unchecked(1)) };

        //  Due to ranges being _exclusive_, we need >, not >=.
        if left.1 > right.0 {
            return Err(GhostAliasingError);
        }
    }

    Ok(())
}

//  Moves all elements of `slice` for which `predicate` is true to the start of `slice`.
//
//  Elements for which `predicate` is false are overwritten without a care in the world, the sub-slice of only-true
//  elements is returned for convenience.
fn select<T, F>(slice: &mut [T], predicate: F) -> &mut [T]
where
    T: Copy,
    F: Fn(&T) -> bool,
{
    let data = slice.as_mut_ptr();
    let length = slice.len();

    if length == 0 {
        return slice;
    }

    let mut write = 0;

    for read in 0..length {
        //  Safety:
        //  -   `read < slice.len()`.
        let element = unsafe { &*data.add(read) };

        if !predicate(element) {
            continue;
        }

        if read != write {
            //  Safety:
            //  -   `write < slice.len()`, since `write < read`.
            //  -   `read` != `write`.
            let slot = unsafe { &mut *data.add(write) };

            *slot = *element;
        }

        write += 1;
    }

    //  Safety:
    //  -   `write < slice.len()`.
    unsafe { slice.get_unchecked_mut(0..write) }
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

            let (reference1, reference2, reference3, reference4): (&mut i32, &mut i32, &mut i32, &mut i32) =
                (&cell1, &cell2, &cell3, &cell4).borrow_mut(&mut token).unwrap();
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
            let _: (&mut i32, &mut i32, &mut i32, &mut i32) =
                (&cell1, &cell2, &cell3, &cell2).borrow_mut(&mut token).unwrap();
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

            let reference: &mut (i32, i32, i32, i32) = tuple.borrow_mut(&mut token).unwrap();
            reference.0 = 33;
            reference.1 = 34;
            reference.2 = 35;
            reference.3 = 36;

            // here we stop mutating, so the token isn't mutably borrowed anymore, and we can read again
            (
                *tuple.0.borrow(&token),
                *tuple.1.borrow(&token),
                *tuple.2.borrow(&token),
            )
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

            let reference: &mut [i32; 4] = array.borrow_mut(&mut token).unwrap();
            reference[0] = 33;
            reference[1] = 34;
            reference[2] = 35;
            reference[3] = 36;

            // here we stop mutating, so the token isn't mutably borrowed anymore, and we can read again
            (
                *array[0].borrow(&token),
                *array[1].borrow(&token),
                *array[2].borrow(&token),
            )
        });
        assert_eq!((33, 34, 35), value);
    }

    #[test]
    #[should_panic]
    fn multiple_borrows_single_slice_overlap() {
        GhostToken::new(|mut token| {
            let mut array = [3, 7];
            let cell_of_slice = &*GhostCell::from_mut(&mut array[..]);
            let slice_of_cells = cell_of_slice.as_slice_of_cells();
            let second_cell = &slice_of_cells[1];

            let _ = (second_cell, cell_of_slice).borrow_mut(&mut token).unwrap();
        });
    }

    #[test]
    #[should_panic]
    fn multiple_borrows_single_array_overlap() {
        GhostToken::new(|mut token| {
            let cell_of_array = GhostCell::new([3, 7]);
            let slice_of_cells = (&cell_of_array as &GhostCell<[i32]>).as_slice_of_cells();
            let second_cell = &slice_of_cells[1];

            let _ = (second_cell, &cell_of_array).borrow_mut(&mut token).unwrap();
        });
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

            let (reference1, reference2, reference3, reference4) =
                (cell1, cell2, cell3, cell4).borrow_mut(&mut token).unwrap();
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

            (
                array[0].borrow(&token)[0],
                array[1].borrow(&token)[0],
                array[2].borrow(&token)[0],
            )
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

            (
                array[0].borrow(&token).get(),
                array[1].borrow(&token).get(),
                array[2].borrow(&token).get(),
            )
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

            let _: (&mut dyn Store<Item = i32>, &mut [i32], &mut dyn ToString, &mut [i32]) =
                (cell1, cell2, cell3, cell2).borrow_mut(&mut token).unwrap();
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
        //  Small Array.
        GhostToken::new(|mut token| {
            let cells = [
                GhostCell::new(1),
                GhostCell::new(2),
                GhostCell::new(3),
                GhostCell::new(4),
                GhostCell::new(5),
                GhostCell::new(6),
            ];

            //  No aliasing.
            let tuple1 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5]);
            assert!(tuple1.borrow_mut(&mut token).is_ok());

            //  Aliasing at start/end.
            let tuple2 = (&cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[0]);
            assert!(tuple2.borrow_mut(&mut token).is_err());
        });

        //  Big Array.
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

            //  No aliasing.
            let tuple1 = (
                &cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5], &cells[6], &cells[7], &cells[8],
                &cells[9], &cells[10], &cells[11],
            );
            assert!(tuple1.borrow_mut(&mut token).is_ok());

            //  Aliasing at start/end.
            let tuple2 = (
                &cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5], &cells[6], &cells[7], &cells[8],
                &cells[9], &cells[10], &cells[0],
            );
            assert!(tuple2.borrow_mut(&mut token).is_err());

            //  Aliasing at the start.
            let tuple3 = (
                &cells[0], &cells[0], &cells[1], &cells[3], &cells[4], &cells[5], &cells[6], &cells[7], &cells[8],
                &cells[9], &cells[10], &cells[11],
            );
            assert!(tuple3.borrow_mut(&mut token).is_err());

            //  Aliasing at the end.
            let tuple4 = (
                &cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5], &cells[6], &cells[7], &cells[8],
                &cells[9], &cells[10], &cells[10],
            );
            assert!(tuple4.borrow_mut(&mut token).is_err());

            //  Aliasing in the middle.
            let tuple5 = (
                &cells[0], &cells[1], &cells[2], &cells[3], &cells[4], &cells[5], &cells[5], &cells[7], &cells[8],
                &cells[9], &cells[10], &cells[11],
            );
            assert!(tuple5.borrow_mut(&mut token).is_err());
        });
    }

    #[test]
    fn check_distinct_zst() {
        //  Check that ZSTs are always considered distincts.
        GhostToken::new(|mut token| {
            let zst = GhostCell::new(());

            let tuple = (&zst, &zst);
            assert!(tuple.borrow_mut(&mut token).is_ok());
        });
    }

    #[test]
    fn check_distinct_inner_zst() {
        //  Check that an inner ZST is still considered distinct from its outer instance.
        GhostToken::new(|mut token| {
            let outer = GhostCell::new((1, (), 2));
            let (_, inner, _) = outer.as_tuple_of_cells();

            let tuple = (&outer, inner);
            assert!(tuple.borrow_mut(&mut token).is_ok());
        });
    }
} // mod tests
