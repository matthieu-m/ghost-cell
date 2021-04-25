use core::ptr::NonNull;

use super::{GhostCell, GhostToken};

/// A GhostCursor implements a Cursor to navigate across a web of GhostCells.
///
/// #   Safety
///
/// This is an untrodden path, here be dragons.
///
/// ##  Safety: Aliasing.
///
/// The `GhostCursor` trivially enforces safe aliasing by always tying the lifetime of the token it materializes to its
/// own lifetime.
///
/// The `GhostCursor` itself is therefore borrowed mutably or immutably for the duration of the lifetime of the token,
/// preventing any abuse.
///
/// ##  Safety: Lifetime
///
/// This is the crux of the issue, and the most likely place for unsoundness in the whole scheme.
///
/// Let us start by a broken example to better understand what we are looking for. Let us imagine a simple doubly linked
/// list data-structure where each node has an optional previous and next fields to point to the previous and next nodes
/// respectively.
///
/// Imagine the following set-up with 2 nodes `a` and `b`:
///
/// -   On the stack is `root`, a pointer owning half of `a` -- the other half doesn't matter here.
/// -   `a.prev` and `a.next` are each a pointer owning half of `b`.
///
/// Any method which allows both obtaining a reference to `b` and simultaneously a mutable reference to `a` is unsound,
/// for owning a mutable reference to `a` allows setting both of its `prev` and `next` fields to `None`, dropping `b`,
/// and of course retaining a reference to a dropped element is opening the door to Undefined Behavior.
///
/// Hence, the very stringent invariant that the `GhostCursor` must enforce is that apart from the currently mutable
/// element, no reference to other elements with no _separate_ anchoring ownership paths to the stack can be observed.
///
/// Or, in short, the `GhostCursor` may allow either:
///
/// -   Observing multiple immutable references at a time.
/// -   Or observing a single mutable reference at a time.
///
/// A familiar restriction for Rust programmers.
pub struct GhostCursor<'a, 'brand, T> {
    token: NonNull<GhostToken<'brand>>,
    cell: Option<&'a GhostCell<'brand, T>>,
}

impl<'a, 'brand, T> GhostCursor<'a, 'brand, T> {
    /// Creates a new instance of the cursor.
    pub fn new(token: &'a mut GhostToken<'brand>, cell: Option<&'a GhostCell<'brand, T>>) -> Self {
        let token = NonNull::from(token);

        Self { token, cell, }
    }

    /// Returns a mutable reference to the current element, if any.
    ///
    /// #   Safety
    ///
    /// The token is still mutably borrowed for as long as the return value lives.
    ///
    /// ```compile_fail
    /// use ghost_cell::{GhostCell, GhostCursor, GhostToken};
    ///
    /// GhostToken::new(|mut token| {
    ///     let (one, two) = (GhostCell::new("One".to_string()), GhostCell::new("Two".to_string()));
    ///
    ///     let cursor = GhostCursor::new(&mut token, Some(&one));
    ///     if let Some(one) = cursor.into_inner() {
    ///         println!("{?:}", two.borrow(&token));  //  Fail, token still borrowed by `one`.
    ///         *one = "Three".to_string();
    ///     }
    /// })
    /// ```
    pub fn into_inner(self) -> Option<&'a mut T> {
        let token = unsafe { as_mut(self.token) };

        self.cell.map(move |cell| cell.borrow_mut(token))
    }

    /// Returns the token and currently pointed to cell.
    ///
    /// #   Safety
    ///
    /// The token is still immutably borrowed for as long as the return value lives.
    ///
    /// ```compile_fail
    /// use ghost_cell::{GhostCell, GhostCursor, GhostToken};
    ///
    /// GhostToken::new(|mut token| {
    ///     let (one, two) = (GhostCell::new("One".to_string()), GhostCell::new("Two".to_string()));
    ///
    ///     let cursor = GhostCursor::new(&mut token, Some(&one));
    ///     let aliased_token = cursor.into_parts().0;
    ///     *two.borrow_mut(&mut token) = "Four".to_string();   //  Fail, token still borrowed by `aliased_token`.
    ///     println!("{:?}", one.borrow(aliased_token));
    /// })
    /// ```
    ///
    /// ```compile_fail
    /// use ghost_cell::{GhostCell, GhostCursor, GhostToken};
    ///
    /// GhostToken::new(|mut token| {
    ///     let (one, two) = (GhostCell::new("One".to_string()), GhostCell::new("Two".to_string()));
    ///
    ///     let cursor = GhostCursor::new(&mut token, Some(&one));
    ///     if let Some(one) = cursor.into_parts().1 {
    ///         *two.borrow_mut(&mut token) = "Four".to_string();   //  Fail, token still borrowed by `one`.
    ///         println!("{:?}", one);
    ///     }
    /// })
    /// ```
    pub fn into_parts(self) -> (&'a GhostToken<'brand>, Option<&'a GhostCell<'brand, T>>) {
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
    pub fn borrow(&self) -> Option<&T> {
        let token = unsafe { as_ref(self.token) };

        self.cell.map(|cell| cell.borrow(token))
    }

    /// Returns a mutable reference to the inner value of the current cell.
    pub fn borrow_mut(&mut self) -> Option<&mut T> {
        let token = unsafe { as_mut(self.token) };

        self.cell.map(move |cell| cell.borrow_mut(token))
    }

    /// Attempts to move from the current cell to another cell, derived from it.
    ///
    /// Returns an error if either:
    /// -   There is no current cell.
    /// -   `fun` returns no cell.
    ///
    /// In case of error, the current cell is not modified.
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
    pub fn move_mut<F>(&mut self, fun: F) -> Result<(), ()>
    where
        F: FnOnce(&'a T) -> Option<&'a GhostCell<'brand, T>>,
    {
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
    /// In case of error, the current cell is returned.
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
    pub fn move_into<U, F>(self, fun: F) -> Result<GhostCursor<'a, 'brand, U>, Self>
    where
        F: FnOnce(&'a T) -> Option<&'a GhostCell<'brand, U>>,
    {
        let result = self.move_into_impl(fun);

        result.or(Err(self))
    }

    //  Internal.
    fn move_into_impl<U, F>(&self, fun: F) -> Result<GhostCursor<'a, 'brand, U>, ()>
    where
        F: FnOnce(&'a T) -> Option<&'a GhostCell<'brand, U>>,
    {
        let token_mut = unsafe { as_mut(self.token) };

        let cell = self.cell.ok_or(())?;
        let cell = fun(cell.borrow(token_mut)).ok_or(())?;

        Ok(GhostCursor { token: self.token, cell: Some(cell), })
    }
}

//
//  Implementation
//

unsafe fn as_ref<'a, T>(ptr: NonNull<T>) -> &'a T {
    &*ptr.as_ptr()
}

unsafe fn as_mut<'a, T>(ptr: NonNull<T>) -> &'a mut T {
    &mut *ptr.as_ptr()
}
