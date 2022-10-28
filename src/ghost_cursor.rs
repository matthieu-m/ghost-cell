//! A `GhostCursor` implements a cursor to navigate across a web of `GhostCell`s.
//!
//! #   Safety
//!
//! This is an untrodden path, here be dragons.
//!
//! ##  Safety: Aliasing.
//!
//! The `GhostCursor` trivially enforces safe aliasing by always tying the lifetime of the token it materializes to its
//! own lifetime.
//!
//! The `GhostCursor` itself is therefore borrowed mutably or immutably for the duration of the lifetime of the token,
//! preventing any abuse.
//!
//! ##  Safety: Lifetime
//!
//! This is the crux of the issue, and the most likely place for unsoundness in the whole scheme.
//!
//! Let us start by a broken example to better understand what we are looking for. Let us imagine a simple doubly linked
//! list data structure where each node has two optional fields, a previous and a next field, to point to the previous and next node,
//! respectively.
//!
//! Imagine the following set-up with 2 nodes `a` and `b`:
//!
//! -   On the stack is `root`, a pointer owning half of `a` -- the other half doesn't matter here.
//! -   `a.prev` and `a.next` are each a pointer owning half of `b`.
//!
//! Any method which allows both obtaining a reference to `b` and simultaneously a mutable reference to `a` is unsound,
//! for owning a mutable reference to `a` allows setting both of its `prev` and `next` fields to `None`, dropping `b`,
//! and of course retaining a reference to a dropped element is opening the door to undefined behavior.
//!
//! Hence, the very stringent invariant that the `GhostCursor` must enforce is that apart from the currently mutable
//! element, no reference to other elements with no _separate_ anchoring ownership paths to the stack can be observed.
//!
//! Or, in short, the `GhostCursor` may allow either:
//!
//! -   Observing multiple immutable references at a time.
//! -   Or observing a single mutable reference at a time.
//!
//! A familiar restriction for Rust programmers.

use core::ptr::NonNull;

use super::{GhostCell, GhostToken};

/// A `GhostCursor`, to navigate across a web of `GhostCell`s.
pub struct GhostCursor<'a, 'brand, T: ?Sized> {
    token: NonNull<GhostToken<'brand>>,
    cell: Option<&'a GhostCell<'brand, T>>,
}

impl<'a, 'brand, T: ?Sized> GhostCursor<'a, 'brand, T> {
    /// Creates a new instance of the cursor.
    pub fn new(token: &'a mut GhostToken<'brand>, cell: Option<&'a GhostCell<'brand, T>>) -> Self {
        let token = NonNull::from(token);

        Self { token, cell }
    }

    /// Returns a mutable reference to the current element, if any.
    ///
    /// #   Safety
    ///
    /// The token is still mutably borrowed for as long as the return value lives.
    pub fn into_inner(self) -> Option<&'a mut T> {
        //  Safety:
        //  -   `self` is not borrowed, therefore the token is not borrowed.
        //  -   The lifetime of the result ensures that the token remains mutably borrowed for as long as the result
        //      exists.
        let token = unsafe { as_mut(self.token) };

        self.cell.map(move |cell| cell.borrow_mut(token))
    }

    /// Returns the token and currently pointed to cell.
    ///
    /// #   Safety
    ///
    /// The token is still mutably borrowed for as long as the return value lives.
    pub fn into_parts(self) -> (&'a GhostToken<'brand>, Option<&'a GhostCell<'brand, T>>) {
        //  Why cannot `into_parts` returns a mutable reference to `GhostToken`?
        //
        //  This is a tempting option, as it would match the constructor (`new`) perfectly. It is also unsound,
        //  unfortunately, as demonstrated in #25.
        //
        //  The current reference pointed to by the cursor may be owned (transitively) by another `GhostCell`.
        //  Returning a mutable reference to the `GhostToken` allows mutating this other `GhostCell` in a way that may
        //  destroy (and free), the `GhostCell` this returned reference refers to, thereby allowing a use-after-free.
        //
        //  Therefore, this function needs to choose between returning a mutable reference to the token or returning
        //  a reference to the `GhostCell`; it cannot do both at once, not safely.

        //  Safety:
        //  -   `self` is not borrowed, therefore the token is not borrowed.
        //  -   The lifetime of the result ensures that the token and cell remain borrowed for as long as the result
        //      exists.
        (unsafe { as_ref(self.token) }, self.cell)
    }

    /// Returns a reference to the token.
    ///
    /// This borrows `self` immutably for the duration, preventing any materialization of a mutable token.
    ///
    /// #   Note
    ///
    /// There is no equivalent `token_mut` to avoid jeopardizing the anchoring path of the current reference within the
    /// cursor.
    pub fn token(&self) -> &GhostToken<'brand> {
        //  Safety:
        //  -   Borrows self, immutably, restricting uses of the cursor and token to immutable borrows.
        unsafe { as_ref(self.token) }
    }

    /// Returns a reference to the inner value of the current cell.
    ///
    /// #   Example
    ///
    /// ```
    /// use ghost_cell::{GhostCell, GhostCursor, GhostToken};
    ///
    /// GhostToken::new(|mut token| {
    ///     let cell = GhostCell::new(42);
    ///
    ///     let cursor = GhostCursor::new(&mut token, Some(&cell));
    ///
    ///     assert_eq!(Some(&42), cursor.borrow());
    /// });
    /// ```
    pub fn borrow(&self) -> Option<&T> {
        //  Safety:
        //  -   Borrows `self`, therefore ensuring that no mutable borrow of the token exists.
        //  -   Restricts the lifetime of `token` to that of `self`.
        let token = unsafe { as_ref(self.token) };

        self.cell.map(|cell| cell.borrow(token))
    }

    /// Returns a mutable reference to the inner value of the current cell.
    ///
    /// #   Example
    ///
    /// ```
    /// use ghost_cell::{GhostCell, GhostCursor, GhostToken};
    ///
    /// GhostToken::new(|mut token| {
    ///     let cell = GhostCell::new(42);
    ///
    ///     let mut cursor = GhostCursor::new(&mut token, Some(&cell));
    ///
    ///     if let Some(r) = cursor.borrow_mut() {
    ///         *r = 33;
    ///     }
    ///
    ///     assert_eq!(Some(&33), cursor.borrow());
    /// });
    /// ```
    pub fn borrow_mut(&mut self) -> Option<&mut T> {
        //  Safety:
        //  -   Borrows `self` mutably, therefore ensuring that no other borrow of the token exists.
        //  -   Restricts the lifetime of `token` to that of `self.`
        let token = unsafe { as_mut(self.token) };

        self.cell.map(move |cell| cell.borrow_mut(token))
    }

    /// Attempts to move from the current cell to another cell, derived from it.
    ///
    /// Returns an error if either:
    /// -   There is no current cell.
    /// -   `fun` returns no cell.
    ///
    /// In case of an error, the current cell is not modified.
    ///
    /// #   Example
    ///
    /// ```
    /// use ghost_cell::{GhostCell, GhostCursor, GhostToken};
    ///
    /// struct Link<'brand>(GhostCell<'brand, Option<Box<Self>>>);
    ///
    /// GhostToken::new(|mut token| {
    ///     let three = Link(GhostCell::new(None));
    ///     let two = Link(GhostCell::new(None));
    ///     let one = Link(GhostCell::new(Some(Box::new(two))));
    ///
    ///     let mut cursor = GhostCursor::new(&mut token, Some(&one.0));
    ///
    ///     cursor.move_mut(|option| option.as_ref().map(|boxed| &boxed.0))
    ///         .expect("one.0 points to two!");
    ///
    ///     if let Some(two) = cursor.borrow_mut() {
    ///         let previous = std::mem::replace(two, Some(Box::new(three)));
    ///         assert!(previous.is_none());
    ///     }
    /// });
    /// ```
    #[allow(clippy::result_unit_err)]
    pub fn move_mut<F>(&mut self, fun: F) -> Result<(), ()>
    where
        F: FnOnce(&T) -> Option<&GhostCell<'brand, T>>,
    {
        //  Safety:
        //  -   Borrows `self` mutably, therefore ensuring that no borrow of the token exists.
        //  -   Restricts the lifetime of the token to that of `self`, or less.
        let token = unsafe { as_ref(self.token) };

        let cell = self.cell.ok_or(())?;
        let cell = fun(cell.borrow(token)).ok_or(())?;

        self.cell = Some(cell);

        Ok(())
    }

    /// Attempts to move from the current cell to another cell, derived from it.
    ///
    /// Returns an error if either:
    /// -   There is no current cell.
    /// -   `fun` returns no cell.
    ///
    /// In case of an error, the current cursor is returned.
    ///
    /// #   Example
    ///
    /// ```
    /// use ghost_cell::{GhostCell, GhostCursor, GhostToken};
    ///
    /// struct Leaf<'brand>(GhostCell<'brand, String>);
    ///
    /// GhostToken::new(|mut token| {
    ///     let leaf = Leaf(GhostCell::new("Terminal".to_string()));
    ///     let inner = GhostCell::new(leaf);
    ///
    ///     let cursor = GhostCursor::new(&mut token, Some(&inner));
    ///
    ///     let mut cursor = cursor.move_into(|leaf| Some(&leaf.0))
    ///         .or(Err(()))
    ///         .expect("inner.0 points to leaf");
    ///
    ///     if let Some(s) = cursor.borrow_mut() {
    ///         let previous = std::mem::replace(s, "Station".to_string());
    ///         assert_eq!("Terminal", previous);
    ///     }
    /// });
    /// ```
    pub fn move_into<U, F>(mut self, fun: F) -> Result<GhostCursor<'a, 'brand, U>, Self>
    where
        F: FnOnce(&T) -> Option<&GhostCell<'brand, U>>,
    {
        let result = self.move_into_impl(fun);

        result.or(Err(self))
    }

    //  Internal.
    fn move_into_impl<U, F>(&mut self, fun: F) -> Result<GhostCursor<'a, 'brand, U>, ()>
    where
        F: FnOnce(&T) -> Option<&GhostCell<'brand, U>>,
    {
        //  Safety:
        //  -   Borrows `self` mutably, therefore ensuring that no borrow of the token exists.
        //  -   Restricts the lifetime of the token to that of `self`, or less.
        let token_mut = unsafe { as_mut(self.token) };

        let cell = self.cell.ok_or(())?;
        let cell = fun(cell.borrow(token_mut)).ok_or(())?;

        Ok(GhostCursor { token: self.token, cell: Some(cell) })
    }
}

//
//  Implementation
//

unsafe fn as_ref<'a, T: ?Sized>(ptr: NonNull<T>) -> &'a T {
    &*ptr.as_ptr()
}

unsafe fn as_mut<'a, T: ?Sized>(ptr: NonNull<T>) -> &'a mut T {
    &mut *ptr.as_ptr()
}

#[doc(hidden)]
pub mod compile_tests {

/// ```compile_fail,E0502
/// use ghost_cell::{GhostCell, GhostCursor, GhostToken};
///
/// GhostToken::new(|mut token| {
///     let cell = GhostCell::new(1);
///     let cursor = GhostCursor::new(&mut token, Some(&cell));
///
///     assert_eq!(1, *cell.borrow(&token));
///     assert_eq!(Some(&1), cursor.borrow());
/// })
/// ```
pub fn cursor_new_borrows_token_mutably() {}

/// ```compile_fail,E0502
/// use ghost_cell::{GhostCell, GhostCursor, GhostToken};
///
/// GhostToken::new(|mut token| {
///     let (one, two) = (GhostCell::new(1), GhostCell::new(2));
///
///     let cursor = GhostCursor::new(&mut token, Some(&one));
///     if let Some(one) = cursor.into_inner() {
///         assert_eq!(2, *two.borrow(&token));  //  Fail, token still borrowed by `one`.
///         *one = 3;
///     }
/// })
/// ```
pub fn cursor_into_inner_leaves_token_borrowed_mutably() {}

/// ```compile_fail,E0499
/// use ghost_cell::{GhostCell, GhostCursor, GhostToken};
///
/// GhostToken::new(|mut token| {
///     let (one, two) = (GhostCell::new(1), GhostCell::new(2));
///
///     let cursor = GhostCursor::new(&mut token, Some(&one));
///     let aliased_token = cursor.into_parts().0;
///     *two.borrow_mut(&mut token) = 4;   //  Fail, token still borrowed by `aliased_token`.
///     assert_eq!(1, *one.borrow(aliased_token));
/// })
/// ```
pub fn cursor_into_parts_first_part_leaves_token_borrowed_mutably() {}

/// ```compile_fail,E0502
/// use ghost_cell::{GhostCell, GhostCursor, GhostToken};
///
/// GhostToken::new(|mut token| {
///     let (one, two) = (GhostCell::new(1), GhostCell::new(2));
///
///     let cursor = GhostCursor::new(&mut token, Some(&one));
///     if let Some(one) = cursor.into_parts().1 {
///         *two.borrow_mut(&mut token) = 4;   //  Fail, token still borrowed by `one`.
///         assert_eq!(1, *one.borrow(&token));
///     }
/// })
/// ```
pub fn cursor_into_parts_second_part_leaves_token_borrowed_mutably() {}

/// ```compile_fail,E0521
/// use core::cell::Cell;
/// use ghost_cell::{GhostCell, GhostCursor, GhostToken};
///
/// GhostToken::new(|mut token| {
///     let cell = GhostCell::new(1);
///     let leak = Cell::new(None);
///     let mut cursor = GhostCursor::new(&mut token, Some(&cell));
///
///     let _ = cursor.move_mut(|cell_ref| {
///         leak.set(Some(cell_ref));   //  Fail, `cell_ref` cannot escape the closure body.
///         None
///     });
///
///     //  If `cell_ref` escaped, this would be a shared reference whose value can change -- this is unsound.
///     let cell_ref: &i32 = leak.get().unwrap();
///     assert_eq!(*cell_ref, 1);
///     *cursor.borrow_mut().unwrap() = 42;
///     assert_eq!(*cell_ref, 42);
/// })
/// ```
pub fn cursor_move_mut_noescape() {}

} // mod compile_tests
