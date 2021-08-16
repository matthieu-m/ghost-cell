//! `GhostCell` and `GhostToken`, as per http://plv.mpi-sws.org/rustbelt/ghostcell/.
//!
//! Reference implementation at https://gitlab.mpi-sws.org/FP/ghostcell/-/tree/master/ghostcell.

use core::{
    cell::UnsafeCell,
    marker::PhantomData,
    mem,
};

/// A `GhostToken<'x>` is _the_ key to access the content of any `&GhostCell<'x, _>` sharing the same brand.
///
/// Each `GhostToken<'x>` is created alongside a unique brand (its lifetime), and each `GhostCell<'x, T>` is associated
/// to one, and only one, `GhostToken` at a time via this brand. The entire set of `GhostCell<'x, T>` associated to a
/// given `GhostToken<'x>` creates a pool of cells all being accessible solely through the one token they are associated
/// to.
///
/// The pool of `GhostCell` associated to a token need not be homogeneous, each may own a value of a different type.
pub struct GhostToken<'brand> { _marker: InvariantLifetime<'brand> }

impl<'brand> GhostToken<'brand> {
    /// Creates a fresh token to which `GhostCell`s can be tied to later.
    ///
    /// Due to the use of a lifetime, the `GhostCell`s tied to a given token can only live within the confines of the
    /// invocation of the `fun` closure.
    ///
    /// #   Example
    ///
    /// ```rust
    /// use ghost_cell::{GhostToken, GhostCell};
    ///
    /// let n = 42;
    ///
    /// let value = GhostToken::new(|mut token| {
    ///     let cell = GhostCell::new(42);
    ///
    ///     let vec: Vec<_> = (0..n).map(|_| &cell).collect();
    ///
    ///     *vec[n / 2].borrow_mut(&mut token) = 33;
    ///
    ///     *cell.borrow(&token)
    /// });
    ///
    /// assert_eq!(33, value);
    /// ```
    #[allow(clippy::new_ret_no_self)]
    pub fn new<R, F>(fun: F) -> R
    where
        for <'new_brand> F: FnOnce(GhostToken<'new_brand>) -> R
    {
        let token = Self { _marker: InvariantLifetime::default() };
        fun(token)
    }
}

/// A `GhostToken` is stateless, therefore it can safely be passed across threads.
unsafe impl<'brand> Send for GhostToken<'brand> {}

/// A `GhostToken` is stateless, therefore it can safely be accessed from different threads.
unsafe impl<'brand> Sync for GhostToken<'brand> {}

/// Branded wrapper for the data structure's nodes, whose type is T.
///
/// A `GhostCell<'x, T>` owns an instance of type `T`:
/// -   Unique access to the cell allows unimpeded access to the contained value.
/// -   Shared access to the cell requires mediating access through the associated `GhostToken<'x, T>` which will
///     enforce at compile-time the Aliasing XOR Mutability safety property.
#[repr(transparent)]
pub struct GhostCell<'brand, T: ?Sized> {
    _marker: InvariantLifetime<'brand>,
    value: UnsafeCell<T>,
}

impl<'brand, T> GhostCell<'brand, T> {
    /// Wraps some data T into a GhostCell with brand `'brand` which associates it to one, and only one, `GhostToken`.
    ///
    /// #   Example
    ///
    /// ```rust
    /// use ghost_cell::{GhostToken, GhostCell};
    ///
    /// GhostToken::new(|token| {
    ///     let cell = GhostCell::new(42);
    ///
    ///     assert_eq!(42, *cell.borrow(&token));
    /// });
    /// ```
    pub fn new(value: T) -> Self {
        let _marker = InvariantLifetime::default();
        let value = UnsafeCell::new(value);

        Self { _marker, value, }
    }

    /// Turns an owned GhostCell back into owned data.
    ///
    /// #   Example
    ///
    /// ```rust
    /// use ghost_cell::{GhostToken, GhostCell};
    ///
    /// let value = GhostToken::new(|mut token| {
    ///     let cell = GhostCell::new(42);
    ///
    ///     cell.into_inner()
    /// });
    ///
    /// assert_eq!(42, value);
    /// ```
    pub fn into_inner(self) -> T { self.value.into_inner() }

    /// Immutably borrows the GhostCell with the same-branded token.
    ///
    /// #   Example
    ///
    /// ```rust
    /// use ghost_cell::{GhostToken, GhostCell};
    ///
    /// let n = 42;
    ///
    /// let value = GhostToken::new(|mut token| {
    ///     let cell = GhostCell::new(42);
    ///
    ///     let vec: Vec<_> = (0..n).map(|_| &cell).collect();
    ///
    ///     let one: &i32 = vec[1].borrow(&token);
    ///     let two: &i32 = vec[2].borrow(&token);
    ///
    ///     *one + *two
    /// });
    ///
    /// assert_eq!(84, value);
    /// ```
    pub fn borrow<'a>(&'a self, _: &'a GhostToken<'brand>) -> &'a T {
        //  Safety:
        //  -   The cell is borrowed immutably by this call, it therefore cannot already be borrowed mutably.
        //  -   The token is borrowed immutably by this call, it therefore cannot be already borrowed mutably.
        //  -   `self.value` therefore cannot be already borrowed mutably, as doing so requires calling either:
        //      -   `borrow_mut`, which would borrow the token mutably.
        //      -   `get_mut`, which would borrow the cell mutably.
        unsafe{ &*self.value.get() }
    }

    /// Mutably borrows the GhostCell with the same-branded token.
    ///
    /// #   Example
    ///
    /// ```rust
    /// use ghost_cell::{GhostToken, GhostCell};
    ///
    /// let n = 42;
    ///
    /// let value = GhostToken::new(|mut token| {
    ///     let cell = GhostCell::new(42);
    ///
    ///     let vec: Vec<_> = (0..n).map(|_| &cell).collect();
    ///
    ///     let reference: &mut i32 = vec[n / 2].borrow_mut(&mut token);
    ///     *reference = 33;
    ///
    ///     *cell.borrow(&token)
    /// });
    ///
    /// assert_eq!(33, value);
    /// ```
    pub fn borrow_mut<'a>(&'a self, _: &'a mut GhostToken<'brand>) -> &'a mut T {
        //  Safety:
        //  -   The cell is borrowed immutably by this call, it therefore cannot already be borrowed mutably.
        //  -   The token is borrowed mutably by this call, it therefore cannot be already borrowed.
        //  -   `self.value` therefore cannot already be borrowed, as doing so requires calling either:
        //      -   `borrow` or `borrow_mut`, which would borrow the token.
        //      -   `get_mut`, which would borrow the cell mutably.
        unsafe{ &mut *self.value.get() }
    }
}

impl<'brand, T: ?Sized> GhostCell<'brand, T> {
    /// Returns a raw pointer to the contained value.
    pub const fn as_ptr(&self) -> *mut T { self.value.get() }

    /// Turns a mutably borrowed GhostCell to mutably borrowed data.
    ///
    /// `self` is mutably borrowed for the lifetime of the result, ensuring the absence of aliasing.
    ///
    /// #   Example
    ///
    /// ```rust
    /// use ghost_cell::{GhostToken, GhostCell};
    ///
    /// let n = 42;
    ///
    /// let value = GhostToken::new(|mut token| {
    ///     let mut cell = GhostCell::new(42);
    ///
    ///     *cell.get_mut() = 33;
    ///
    ///     *cell.borrow(&token)
    /// });
    ///
    /// assert_eq!(33, value);
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        //  Safety:
        //  -   `self` is mutably borrowed for the duration.
        //  -   `GhostCell<'_, T>` has the same in-memory representation as `T`.
        unsafe { mem::transmute(self) }
    }

    /// Turns mutably borrowed data to a mutably borrowed GhostCell.
    ///
    /// `t` is mutably borrowed for the lifetime of the result, ensuring the absence of aliasing.
    ///
    /// #   Example
    ///
    /// ```rust
    /// use ghost_cell::{GhostToken, GhostCell};
    ///
    /// let n = 42;
    /// let mut value = 42;
    ///
    /// GhostToken::new(|mut token| {
    ///     let cell = GhostCell::from_mut(&mut value);
    ///
    ///     let vec: Vec<_> = (0..n).map(|_| &cell).collect();
    ///
    ///     *vec[n / 2].borrow_mut(&mut token) = 33;
    /// });
    ///
    /// assert_eq!(33, value);
    /// ```
    pub fn from_mut(t: &mut T) -> &mut Self {
        //  Safety:
        //  -   `t` is mutably borrowed for the duration.
        //  -   `GhostCell<'_, T>` has the same in-memory representation as `T`.
        unsafe { mem::transmute(t) }
    }
}

//  Safe, convenience methods
#[forbid(unsafe_code)]
impl<'brand, T> GhostCell<'brand, T> {
    /// Returns the value, replacing it by the supplied one.
    ///
    /// #   Example
    ///
    /// ```rust
    /// use ghost_cell::{GhostToken, GhostCell};
    ///
    /// let n = 42;
    ///
    /// let value = GhostToken::new(|mut token| {
    ///     let cell = GhostCell::new(42);
    ///
    ///     let vec: Vec<_> = (0..n).map(|_| &cell).collect();
    ///
    ///     let previous = vec[n / 2].replace(33, &mut token);
    ///     assert_eq!(42, previous);
    ///
    ///     *cell.borrow(&token)
    /// });
    ///
    /// assert_eq!(33, value);
    /// ```
    pub fn replace(&self, value: T, token: &mut GhostToken<'brand>) -> T {
        mem::replace(self.borrow_mut(token), value)
    }

    /// Returns the value, replacing it with the default value.
    ///
    /// #   Example
    ///
    /// ```rust
    /// use ghost_cell::{GhostToken, GhostCell};
    ///
    /// let n = 42;
    ///
    /// let value = GhostToken::new(|mut token| {
    ///     let cell = GhostCell::new(42);
    ///
    ///     let vec: Vec<_> = (0..n).map(|_| &cell).collect();
    ///
    ///     let previous = vec[n / 2].take(&mut token);
    ///     assert_eq!(42, previous);
    ///
    ///     *cell.borrow(&token)
    /// });
    ///
    /// assert_eq!(0, value);
    /// ```
    pub fn take(&self, token: &mut GhostToken<'brand>) -> T
    where
        T: Default,
    {
        self.replace(T::default(), token)
    }
}

impl<'brand, T: Default> Default for GhostCell<'brand, T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<'brand, T> GhostCell<'brand, [T]> {
    /// Returns a slice of cell from a cell of slice.
    ///
    /// #   Example
    ///
    /// ```rust
    /// use ghost_cell::{GhostToken, GhostCell};
    ///
    /// let n = 42;
    ///
    /// let value = GhostToken::new(|mut token| {
    ///     let mut vec: Vec<_> = (0..n).collect();
    ///     let cell = GhostCell::from_mut(&mut vec[..]);
    ///
    ///     let slice = cell.as_slice_of_cells();
    ///
    ///     *slice[n / 2].borrow_mut(&mut token) = 33;
    ///
    ///     vec[n / 2]
    /// });
    ///
    /// assert_eq!(33, value);
    /// ```
    pub fn as_slice_of_cells(&self) -> &[GhostCell<'brand, T>] {
        //  Safety:
        //  -   Same lifetime.
        //  -   `GhostCell<'_, T>` has the same in-memory representation as `T`.
        unsafe { &*(self.as_ptr() as *mut [GhostCell<'brand, T>]) }
    }
}

impl<'brand, T: ?Sized> AsMut<T> for GhostCell<'brand, T> {
    fn as_mut(&mut self) -> &mut T { self.get_mut() }
}

impl<'brand, T> From<T> for GhostCell<'brand, T> {
    fn from(t: T) -> Self { Self::new(t) }
}

/// A `GhostCell<'_, T>` owns a `T`, so cannot be sent across threads if `T` cannot.
///
/// Conversely, a `GhostCell` does not add any state on top of `T`, so if `T` can be sent across threads, so can
/// `GhostCell<'_, T>`
unsafe impl<'brand, T: Send> Send for GhostCell<'brand, T> {}

/// A `GhostCell<'_, T>` owns a `T`, so cannot be accessed from different threads if `T` cannot.
///
/// Conversely, a `GhostCell` does not add any state on top of `T`, so if `T` can be accessed from different threads,
/// so can `GhostCell<'_, T>`.
unsafe impl<'brand, T: Send + Sync> Sync for GhostCell<'brand, T> {}

//
//  Implementation
//

type InvariantLifetime<'brand> = PhantomData<fn(&'brand ()) -> &'brand ()>;

#[doc(hidden)]
pub mod compile_tests {

/// ```compile_fail
/// use ghost_cell::{GhostToken, GhostCell};
///
/// GhostToken::new(|token| token);
/// ```
pub fn token_noescape() {}

/// ```compile_fail
/// use ghost_cell::{GhostToken, GhostCell};
///
/// GhostToken::new(|mut token| {
///     let cell = GhostCell::new(42);
///
///     *cell.borrow_mut(&mut token) = 33;
///
///     cell
/// });
/// ```
pub fn cell_noescape() {}

/// ```compile_fail,E0505
/// use ghost_cell::{GhostToken, GhostCell};
///
/// GhostToken::new(|token| {
///     let cell = GhostCell::new(42);
///
///     let r = cell.borrow(&token);
///     std::mem::drop(token);
///
///     *r
/// });
/// ```
pub fn cell_borrow_borrows_token() {}

/// ```compile_fail,E0502
/// use ghost_cell::{GhostToken, GhostCell};
///
/// GhostToken::new(|mut token| {
///     let one = GhostCell::new(1);
///     let two = GhostCell::new(2);
///
///     let r = one.borrow_mut(&mut token);
///     assert_eq!(2, *two.borrow(&token));
///
///     *r = 33;
/// });
/// ```
pub fn cell_borrow_mut_borrows_token_mutably() {}

/// ```compile_fail,E0505
/// use ghost_cell::{GhostToken, GhostCell};
///
/// GhostToken::new(|token| {
///     let cell = GhostCell::new(42);
///
///     let r = cell.borrow(&token);
///     std::mem::drop(cell);
///
///     *r
/// });
/// ```
pub fn cell_borrow_borrows_cell() {}

/// ```compile_fail,E0505
/// use ghost_cell::{GhostToken, GhostCell};
///
/// GhostToken::new(|mut token| {
///     let cell = GhostCell::new(42);
///
///     let r = cell.borrow_mut(&mut token);
///     std::mem::drop(cell);
///
///     *r
/// });
/// ```
pub fn cell_borrow_mut_borrows_cell() {}

/// ```compile_fail,E0502
/// use ghost_cell::{GhostToken, GhostCell};
///
/// GhostToken::new(|token| {
///     let mut cell = GhostCell::new(42);
///
///     let r = cell.get_mut();
///     assert_eq!(42, *cell.borrow(&token));
///
///     *r = 33;
/// });
/// ```
pub fn cell_get_mut_borrows_cell_mutably() {}

/// ```compile_fail,E0502
/// use ghost_cell::{GhostToken, GhostCell};
///
/// GhostToken::new(|token| {
///     let mut value = 42;
///
///     let cell = GhostCell::from_mut(&mut value);
///
///     assert_eq!(42, value);
///     assert_eq!(42, *cell.borrow(&token));
/// });
/// ```
pub fn cell_from_mut_borrows_value_mutably() {}

} // mod compile_tests
