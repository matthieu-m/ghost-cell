//! The `GhostBorrow` trait allows simultaneously borrowing multiple `GhostCell` immutably.
//!
//! Technically, this is already allowed, however it can be useful to do so as a single expression, which this trait
//! provides.

use core::mem;

use crate::ghost_cell::*;

/// A trait for implementing multiple borrows for any number of arguments, using a `GhostToken<'a, 'brand>`.
///
/// Implemented for a mixture of tuple and array types.
pub trait GhostBorrow<'a, 'brand> {
    /// The references you get as a result.
    ///
    /// For example, if `Self` is `(&'a GhostCell<'brand, T0>, &'a GhostCell<'brand, T1>)` then `Result` is
    /// `(&'a T0, &'a T1)`.
    type Result;

    /// Borrows any number of `GhostCell`s at the same time.
    ///
    /// #   Example
    ///
    /// ```rust
    /// use ghost_cell::{GhostToken, GhostCell, GhostBorrow};
    ///
    /// let value = GhostToken::new(|mut token| {
    ///     let cell1 = GhostCell::new(42);
    ///     let cell2 = GhostCell::new(47);
    ///
    ///     let (reference1, reference2): (&i32, &i32) = (&cell1, &cell2).borrow(&token);
    ///
    ///     (*reference1, *reference2)
    /// });
    ///
    /// assert_eq!((42, 47), value);
    /// ```
    fn borrow(self, token: &'a GhostToken<'brand>) -> Self::Result;
}

impl<'a, 'brand, T> GhostBorrow<'a, 'brand> for &'a [GhostCell<'brand, T>] {
    type Result = &'a [T];

    fn borrow(self, _: &'a GhostToken<'brand>) -> Self::Result {
        //  Safety:
        //  -   Shared access to the `GhostToken` ensures shared access to the cells' content.
        //  -   `GhostCell` is `repr(transparent)`, hence `T` and `GhostCell<T>` have the same memory representation.
        unsafe { mem::transmute::<Self, Self::Result>(self) }
    }
}

impl<'a, 'brand, T, const N: usize> GhostBorrow<'a, 'brand> for &'a [GhostCell<'brand, T>; N] {
    type Result = &'a [T; N];

    fn borrow(self, _: &'a GhostToken<'brand>) -> Self::Result {
        //  Safety:
        //  -   Exclusive access to the `GhostToken` ensures exclusive access to the cells' content.
        //  -   `GhostCell` is `repr(transparent)`, hence `T` and `GhostCell<T>` have the same memory representation.
        unsafe { mem::transmute::<Self, Self::Result>(self) }
    }
}

macro_rules! generate_public_instance {
    ( $($name:ident),* ; $($type_letter:ident),* ) => {
        impl<'a, 'brand, $($type_letter,)*> GhostBorrow<'a, 'brand> for
                ( $(&'a GhostCell<'brand, $type_letter>, )* )
        {
            type Result = ( $(&'a $type_letter, )* );

            fn borrow(self, token: &'a GhostToken<'brand>) -> Self::Result {
                let ($($name,)*) = self;

                ( $( $name.borrow(token),)* )
            }
        }

        impl<'a, 'brand, $($type_letter,)*> GhostBorrow<'a, 'brand> for
                &'a ( $(GhostCell<'brand, $type_letter>, )* )
        {
            type Result = &'a ( $($type_letter, )* );

            fn borrow(self, _: &'a GhostToken<'brand>) -> Self::Result {
                //  Safety:
                //  -   Exclusive access to the `GhostToken` ensures exclusive access to the cells' content.
                //  -   `GhostCell` is `repr(transparent)`, hence `T` and `GhostCell<T>` have the same memory representation.
                unsafe { core::mem::transmute::<Self, Self::Result>(self) }
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

#[cfg(test)]
mod tests {

use super::*;

#[test]
fn multiple_borrows_tuple() {
    let value = GhostToken::new(|token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let cell4 = GhostCell::new(9);

        let (reference1, reference2, reference3, reference4): (&i32, &i32, &i32, &i32)
            = (&cell1, &cell2, &cell3, &cell4).borrow(&token);

        (*reference1, *reference2, *reference3, *reference4)
    });
    assert_eq!((42, 47, 7, 9), value);
}

#[test]
fn multiple_borrows_tuple_ref() {
    let value = GhostToken::new(|token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let cell4 = GhostCell::new(9);
        let tuple = (cell1, cell2, cell3, cell4);

        let reference: &(i32, i32, i32, i32) = tuple.borrow(&token);

        (reference.0, reference.1, reference.2, reference.3)
    });
    assert_eq!((42, 47, 7, 9), value);
}

#[test]
fn multiple_borrows_array_ref() {
    let value = GhostToken::new(|token| {
        let cell1 = GhostCell::new(42);
        let cell2 = GhostCell::new(47);
        let cell3 = GhostCell::new(7);
        let cell4 = GhostCell::new(9);
        let array = [cell1, cell2, cell3, cell4];

        let reference: &[i32; 4] = array.borrow(&token);

        (reference[0], reference[1], reference[2], reference[3])
    });
    assert_eq!((42, 47, 7, 9), value);
}

} // mod tests
