use ghost_cell::GhostToken;

use super::{GhostNode, LinkedList};

#[cfg(feature = "experimental-ghost-cursor")]
use ghost_cell::GhostCursor;

#[cfg(feature = "experimental-ghost-cursor")]
use super::Node;

/// A Cursor over the LinkedList.
pub struct Cursor<'a, 'brand, T> {
    token: &'a GhostToken<'brand>,
    node: Option<&'a GhostNode<'brand, T>>,
}

impl<'a, 'brand, T> Cursor<'a, 'brand, T> {
    /// Creates a new instance pointing to the front element of the list, if any.
    pub fn new_front(token: &'a GhostToken<'brand>, list: &'a LinkedList<'brand, T>) -> Self {
        let node = list.head_tail.as_ref().map(|head_tail| &*head_tail.0);

        Self { token, node, }
    }

    /// Creates a new instance pointing to the back element of the list, if any.
    pub fn new_back(token: &'a GhostToken<'brand>, list: &'a LinkedList<'brand, T>) -> Self {
        let node = list.head_tail.as_ref().map(|head_tail| &*head_tail.1);

        Self { token, node, }
    }

    /// Moves the cursor to the next element, if any.
    ///
    /// If there is no next element, either because the list is empty, or because the current element is the back
    /// element, then an error is returned.
    pub fn move_next(&mut self) -> Result<(), ()> {
        if let Some(node) = self.peek_next_ghost() {
            self.node = Some(node);
            Ok(())
        } else {
            Err(())
        }
    }

    /// Moves the cursor to the previous element, if any.
    ///
    /// If there is no previous element, either because the list is empty, or because the current element is the front
    /// element, then an error is returned.
    pub fn move_prev(&mut self) -> Result<(), ()> {
        if let Some(node) = self.peek_prev_ghost() {
            self.node = Some(node);
            Ok(())
        } else {
            Err(())
        }
    }

    /// Returns a reference to the current element, if any.
    ///
    /// Unless the list is empty, there should always be a current element.
    pub fn current(&self) -> Option<&'a T> { self.node.map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the next element, if any.
    pub fn peek_next(&self) -> Option<&'a T> { self.peek_next_ghost().map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the next element, if any.
    pub fn peek_prev(&self) -> Option<&'a T> { self.peek_prev_ghost().map(|node| &node.borrow(self.token).value) }

    //  Internal: returns a reference to the next GhostNode.
    fn peek_next_ghost(&self) -> Option<&'a GhostNode<'brand, T>> {
        self.node?.borrow(self.token).next.as_ref().map(|n| &**n)
    }

    //  Internal: returns a reference to the previous GhostNode.
    fn peek_prev_ghost(&self) -> Option<&'a GhostNode<'brand, T>> {
        self.node?.borrow(self.token).prev.as_ref().map(|n| &**n)
    }
}

/// A mutable Cursor over a LinkedList.
#[cfg(feature = "experimental-ghost-cursor")]
pub struct CursorMut<'a, 'brand, T> {
    inner: GhostCursor<'a, 'brand, Node<'brand, T>>,
}

#[cfg(feature = "experimental-ghost-cursor")]
impl<'a, 'brand, T> CursorMut<'a, 'brand, T> {
    /// Creates a new instance pointing to the front element of the list, if any.
    pub fn new_front(token: &'a mut GhostToken<'brand>, list: &'a LinkedList<'brand, T>) -> Self {
        let node = list.head_tail.as_ref().map(|head_tail| &*head_tail.0);
        let inner = GhostCursor::new(token, node);

        Self { inner, }
    }

    /// Creates a new instance pointing to the back element of the list, if any.
    pub fn new_back(token: &'a mut GhostToken<'brand>, list: &'a LinkedList<'brand, T>) -> Self {
        let node = list.head_tail.as_ref().map(|head_tail| &*head_tail.1);
        let inner = GhostCursor::new(token, node);

        Self { inner, }
    }

    /// Returns a read-only cursor pointing to the current element.
    pub fn into_cursor(self) -> Cursor<'a, 'brand, T> {
        let (token, node) = self.inner.into_parts();

        Cursor { token, node, }
    }

    /// Moves the cursor to the next element, if any.
    ///
    /// If there is no next element, either because the list is empty, or because the current element is the back
    /// element, then an error is returned and the cursor is left unmodified.
    pub fn move_next(&mut self) -> Result<(), ()> {
        self.inner.move_mut(|node| node.next.as_ref().map(|n| &**n))
    }

    /// Moves the cursor to the previous element, if any.
    ///
    /// If there is no previous element, either because the list is empty, or because the current element is the front
    /// element, then an error is returned and the cursor is left unmodified.
    pub fn move_prev(&mut self) -> Result<(), ()> {
        self.inner.move_mut(|node| node.prev.as_ref().map(|n| &**n))
    }

    /// Returns a mutable reference to the current element, if any.
    ///
    /// Unless the list is empty, there should always be a current element.
    pub fn current(&mut self) -> Option<&mut T> { self.inner.borrow_mut().map(|node| &mut node.value) }

    /// Returns a reference to the next element, if any.
    ///
    /// #   Deviation
    ///
    /// In safe code, it is not possible to allow mutable access to another node than the one currently visited as this
    /// other node could be the anchor of the current node to the stack.
    pub fn peek_next(&self) -> Option<&T> {
        let token = self.inner.token();

        self.peek_next_ghost().map(|node| &node.borrow(token).value)
    }

    /// Returns a reference to the previous element, if any.
    ///
    /// #   Deviation
    ///
    /// In safe code, it is not possible to allow mutable access to another node than the one currently visited as this
    /// other node could be the anchor of the current node to the stack.
    pub fn peek_prev(&self) -> Option<&T> {
        let token = self.inner.token();

        self.peek_prev_ghost().map(|node| &node.borrow(token).value)
    }

    //  Internal: returns a reference to the next GhostNode.
    fn peek_next_ghost(&self) -> Option<&GhostNode<'brand, T>> {
        self.inner.borrow().and_then(|node| node.next.as_ref().map(|n| &**n))
    }

    //  Internal: returns a reference to the previous GhostNode.
    fn peek_prev_ghost(&self) -> Option<&GhostNode<'brand, T>> {
        self.inner.borrow().and_then(|node| node.prev.as_ref().map(|n| &**n))
    }
}

#[cfg(test)]
mod cursor_tests {

use std::fmt::Debug;

use super::super::tests::with_list;
use super::*;

#[track_caller]
fn cursor_assert_none<'a, 'brand, T>(cursor: &Cursor<'a, 'brand, T>)
where
    T: Debug + Eq,
{
    assert_eq!(None, cursor.current());
    assert_eq!(None, cursor.peek_next());
    assert_eq!(None, cursor.peek_prev());
}

#[test]
fn cursor_brush_front_empty() {
    //  Test all functions on empty list.
    with_list::<String, _, _>(vec!(), |token, list| {
        let mut cursor = Cursor::new_front(token, list);
        cursor_assert_none(&cursor);

        assert_eq!(Err(()), cursor.move_next());
        cursor_assert_none(&cursor);

        assert_eq!(Err(()), cursor.move_prev());
        cursor_assert_none(&cursor);
    });
}

#[test]
fn cursor_brush_back_empty() {
    //  Test all functions on empty list.
    with_list::<String, _, _>(vec!(), |token, list| {
        let mut cursor = Cursor::new_back(token, list);
        cursor_assert_none(&cursor);

        assert_eq!(Err(()), cursor.move_next());
        cursor_assert_none(&cursor);

        assert_eq!(Err(()), cursor.move_prev());
        cursor_assert_none(&cursor);
    });
}

#[test]
fn cursor_brush_move_next() {
    let vec: Vec<_> = (0..4).map(|n| n.to_string()).collect();

    with_list(vec, |token, list| {
        let mut cursor = Cursor::new_front(token, list);

        assert_eq!(None, cursor.peek_prev().map(String::as_str));
        assert_eq!(Some("0"), cursor.current().map(String::as_str));
        assert_eq!(Some("1"), cursor.peek_next().map(String::as_str));

        assert_eq!(Ok(()), cursor.move_next());

        assert_eq!(Some("0"), cursor.peek_prev().map(String::as_str));
        assert_eq!(Some("1"), cursor.current().map(String::as_str));
        assert_eq!(Some("2"), cursor.peek_next().map(String::as_str));

        assert_eq!(Ok(()), cursor.move_next());

        assert_eq!(Some("1"), cursor.peek_prev().map(String::as_str));
        assert_eq!(Some("2"), cursor.current().map(String::as_str));
        assert_eq!(Some("3"), cursor.peek_next().map(String::as_str));

        assert_eq!(Ok(()), cursor.move_next());

        assert_eq!(Some("2"), cursor.peek_prev().map(String::as_str));
        assert_eq!(Some("3"), cursor.current().map(String::as_str));
        assert_eq!(None, cursor.peek_next());

        assert_eq!(Err(()), cursor.move_next());

        assert_eq!(Some("2"), cursor.peek_prev().map(String::as_str));
        assert_eq!(Some("3"), cursor.current().map(String::as_str));
        assert_eq!(None, cursor.peek_next());

        assert_eq!(Err(()), cursor.move_next());

        assert_eq!(Some("2"), cursor.peek_prev().map(String::as_str));
        assert_eq!(Some("3"), cursor.current().map(String::as_str));
        assert_eq!(None, cursor.peek_next());
    });
}

#[test]
fn cursor_brush_move_prev() {
    let vec: Vec<_> = (0..4).map(|n| n.to_string()).collect();

    with_list(vec, |token, list| {
        let mut cursor = Cursor::new_back(token, list);

        assert_eq!(None, cursor.peek_next().map(String::as_str));
        assert_eq!(Some("3"), cursor.current().map(String::as_str));
        assert_eq!(Some("2"), cursor.peek_prev().map(String::as_str));

        assert_eq!(Ok(()), cursor.move_prev());

        assert_eq!(Some("3"), cursor.peek_next().map(String::as_str));
        assert_eq!(Some("2"), cursor.current().map(String::as_str));
        assert_eq!(Some("1"), cursor.peek_prev().map(String::as_str));

        assert_eq!(Ok(()), cursor.move_prev());

        assert_eq!(Some("2"), cursor.peek_next().map(String::as_str));
        assert_eq!(Some("1"), cursor.current().map(String::as_str));
        assert_eq!(Some("0"), cursor.peek_prev().map(String::as_str));

        assert_eq!(Ok(()), cursor.move_prev());

        assert_eq!(Some("1"), cursor.peek_next().map(String::as_str));
        assert_eq!(Some("0"), cursor.current().map(String::as_str));
        assert_eq!(None, cursor.peek_prev());

        assert_eq!(Err(()), cursor.move_prev());

        assert_eq!(Some("1"), cursor.peek_next().map(String::as_str));
        assert_eq!(Some("0"), cursor.current().map(String::as_str));
        assert_eq!(None, cursor.peek_prev());

        assert_eq!(Err(()), cursor.move_prev());

        assert_eq!(Some("1"), cursor.peek_next().map(String::as_str));
        assert_eq!(Some("0"), cursor.current().map(String::as_str));
        assert_eq!(None, cursor.peek_prev());
    });
}

} // mod cursor_tests

#[cfg(all(test, feature = "experimental-ghost-cursor"))]
mod cursor_mut_tests {

use std::fmt::Debug;

use super::super::tests::with_list;
use super::*;

#[track_caller]
fn cursor_mut_assert_none<'a, 'brand, T>(cursor: &mut CursorMut<'a, 'brand, T>)
where
    T: Debug + Eq,
{
    assert_eq!(None, cursor.current());
    assert_eq!(None, cursor.peek_next());
    assert_eq!(None, cursor.peek_prev());
}

#[test]
fn cursor_mut_brush_front_empty() {
    //  Test all functions on empty list.
    with_list::<String, _, _>(vec!(), |token, list| {
        let mut cursor = CursorMut::new_front(token, list);
        cursor_mut_assert_none(&mut cursor);

        assert_eq!(Err(()), cursor.move_next());
        cursor_mut_assert_none(&mut cursor);

        assert_eq!(Err(()), cursor.move_prev());
        cursor_mut_assert_none(&mut cursor);
    });
}

#[test]
fn cursor_mut_brush_back_empty() {
    //  Test all functions on empty list.
    with_list::<String, _, _>(vec!(), |token, list| {
        let mut cursor = CursorMut::new_back(token, list);
        cursor_mut_assert_none(&mut cursor);

        assert_eq!(Err(()), cursor.move_next());
        cursor_mut_assert_none(&mut cursor);

        assert_eq!(Err(()), cursor.move_prev());
        cursor_mut_assert_none(&mut cursor);
    });
}

#[test]
fn cursor_mut_brush_move_next() {
    let vec: Vec<_> = (0..4).map(|n| n.to_string()).collect();

    with_list(vec, |token, list| {
        let mut cursor = CursorMut::new_front(token, list);

        assert_eq!(None, cursor.peek_prev().map(String::as_str));
        assert_eq!(Some("0"), cursor.current().map(|s| &**s));
        assert_eq!(Some("1"), cursor.peek_next().map(String::as_str));

        assert_eq!(Ok(()), cursor.move_next());

        assert_eq!(Some("0"), cursor.peek_prev().map(String::as_str));
        assert_eq!(Some("1"), cursor.current().map(|s| &**s));
        assert_eq!(Some("2"), cursor.peek_next().map(String::as_str));

        assert_eq!(Ok(()), cursor.move_next());

        assert_eq!(Some("1"), cursor.peek_prev().map(String::as_str));
        assert_eq!(Some("2"), cursor.current().map(|s| &**s));
        assert_eq!(Some("3"), cursor.peek_next().map(String::as_str));

        assert_eq!(Ok(()), cursor.move_next());

        assert_eq!(Some("2"), cursor.peek_prev().map(String::as_str));
        assert_eq!(Some("3"), cursor.current().map(|s| &**s));
        assert_eq!(None, cursor.peek_next());

        assert_eq!(Err(()), cursor.move_next());

        assert_eq!(Some("2"), cursor.peek_prev().map(String::as_str));
        assert_eq!(Some("3"), cursor.current().map(|s| &**s));
        assert_eq!(None, cursor.peek_next());

        assert_eq!(Err(()), cursor.move_next());

        assert_eq!(Some("2"), cursor.peek_prev().map(String::as_str));
        assert_eq!(Some("3"), cursor.current().map(|s| &**s));
        assert_eq!(None, cursor.peek_next());
    });
}

#[test]
fn cursor_mut_brush_move_prev() {
    let vec: Vec<_> = (0..4).map(|n| n.to_string()).collect();

    with_list(vec, |token, list| {
        let mut cursor = CursorMut::new_back(token, list);

        assert_eq!(None, cursor.peek_next().map(String::as_str));
        assert_eq!(Some("3"), cursor.current().map(|s| &**s));
        assert_eq!(Some("2"), cursor.peek_prev().map(String::as_str));

        assert_eq!(Ok(()), cursor.move_prev());

        assert_eq!(Some("3"), cursor.peek_next().map(String::as_str));
        assert_eq!(Some("2"), cursor.current().map(|s| &**s));
        assert_eq!(Some("1"), cursor.peek_prev().map(String::as_str));

        assert_eq!(Ok(()), cursor.move_prev());

        assert_eq!(Some("2"), cursor.peek_next().map(String::as_str));
        assert_eq!(Some("1"), cursor.current().map(|s| &**s));
        assert_eq!(Some("0"), cursor.peek_prev().map(String::as_str));

        assert_eq!(Ok(()), cursor.move_prev());

        assert_eq!(Some("1"), cursor.peek_next().map(String::as_str));
        assert_eq!(Some("0"), cursor.current().map(|s| &**s));
        assert_eq!(None, cursor.peek_prev());

        assert_eq!(Err(()), cursor.move_prev());

        assert_eq!(Some("1"), cursor.peek_next().map(String::as_str));
        assert_eq!(Some("0"), cursor.current().map(|s| &**s));
        assert_eq!(None, cursor.peek_prev());

        assert_eq!(Err(()), cursor.move_prev());

        assert_eq!(Some("1"), cursor.peek_next().map(String::as_str));
        assert_eq!(Some("0"), cursor.current().map(|s| &**s));
        assert_eq!(None, cursor.peek_prev());
    });
}

} // mod cursor_mut_tests
