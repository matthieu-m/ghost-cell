use core::mem;

use ghost_cell::GhostToken;

use super::{GhostNode, Iter, ThirdNodePtr, TripodList};

/// A Cursor over the TripodList.
pub struct Cursor<'a, 'brand, T> {
    token: &'a GhostToken<'brand>,
    index: usize,
    node: Option<&'a GhostNode<'brand, T>>,
    list: &'a TripodList<'brand, T>,
}

impl<'a, 'brand, T> Cursor<'a, 'brand, T> {
    /// Creates a new instance pointing to the front element of the list, if any.
    pub fn new_front(token: &'a GhostToken<'brand>, list: &'a TripodList<'brand, T>) -> Self {
        let node = list.head_tail.as_ref().map(|head_tail| &*head_tail.0);

        Self { token, index: 0, node, list, }
    }

    /// Creates a new instance pointing to the back element of the list, if any.
    pub fn new_back(token: &'a GhostToken<'brand>, list: &'a TripodList<'brand, T>) -> Self {
        let node = list.head_tail.as_ref().map(|head_tail| &*head_tail.1);
        let index = list.len().checked_sub(1).unwrap_or(0);

        Self { token, index, node, list, }
    }

    /// Returns a triplet (iterator, iterator) in which:
    ///
    /// -   The first iterator is an iterator over all the elements before the cursor.
    /// -   The second iterator is an iterator over all the elements after the cursor.
    ///
    /// If the cursor currently points to the "twilight" non-element, all elements are considered to be before it.
    pub fn before_after(&self) -> (Iter<'a, 'brand, T>, Iter<'a, 'brand, T>) {
        if let Some(_) = self.node {
            let (head, tail) = self.list.head_tail.as_ref().expect("non-empty, node being non-null");

            let prev = self.peek_prev_node();
            let next = self.peek_next_node();

            let before = prev.map(|prev| (&**head, prev));
            let after = next.map(|next| (next, &**tail));

            (Iter::slice(self.token, before), Iter::slice(self.token, after))
        } else {
            (self.list.iter(self.token), Iter::empty(self.token))
        }
    }

    /// Returns the index of the element pointed to by the cursor in the list.
    ///
    /// If the cursor currently points to the "twilight" non-element, returns None.
    pub fn index(&self) -> Option<usize> { self.node.map(|_| self.index) }

    /// Moves the cursor to the next element, if any.
    ///
    /// If there is no next element, then the cursor moves to the "twilight" non-element, which exists between the front
    /// and back element.
    pub fn move_next(&mut self) {
        if self.node.is_some() {
            self.index += 1;
        } else {
            self.index = 0;
        }

        self.node = self.peek_next_node();
    }

    /// Moves the cursor to the previous element, if any.
    ///
    /// If there is no previous element, then the cursor moves to the "twilight" non-element, which exists between the front
    /// and back element.
    pub fn move_prev(&mut self) {
        if self.node.is_some() {
            self.index = self.index.checked_sub(1).unwrap_or_else(|| self.list.len());
        } else {
            self.index = self.list.len().checked_sub(1).unwrap_or(0);
        }

        self.node = self.peek_prev_node();
    }

    /// Returns a reference to the current element, if any.
    ///
    /// Unless the list is empty, there should always be a current element.
    pub fn current(&self) -> Option<&'a T> { self.node.map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the next element, if any.
    pub fn peek_next(&self) -> Option<&'a T> { self.peek_next_node().map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the previous element, if any.
    pub fn peek_prev(&self) -> Option<&'a T> { self.peek_prev_node().map(|node| &node.borrow(self.token).value) }

    //  Internal: returns a reference to the next GhostNode.
    fn peek_next_node(&self) -> Option<&'a GhostNode<'brand, T>> {
        if let Some(node) = self.node {
            node.borrow(self.token).next.as_ref().map(|n| &**n)
        } else {
            self.list.front_node()
        }
    }

    //  Internal: returns a reference to the previous GhostNode.
    fn peek_prev_node(&self) -> Option<&'a GhostNode<'brand, T>> {
        if let Some(node) = self.node {
            node.borrow(self.token).prev.as_ref().map(|n| &**n)
        } else {
            self.list.back_node()
        }
    }
}

impl<'a, 'brand, T> Clone for Cursor<'a, 'brand, T> {
    fn clone(&self) -> Self { *self }
}

impl<'a, 'brand, T> Copy for Cursor<'a, 'brand, T> {}

/// A mutable cursor over the TripodList.
///
/// A mutable cursor allows freely moving back-and-forth amongst the elements of the list, and mutate the list as any
/// point.
///
/// Cursors index the list in a logically circular way. To accomodate this, there is a "twilight" non-element that
/// `None` between the head and tail of the list.
///
/// #   Warning.
///
/// This cursor mutates the list as it iterates. Although the list is left in a safe state by construction, forgoing the
/// drop of this cursor -- unless it points to the "twilight" non-element -- will leave the list in and unusable state.
///
/// Any further mutable operation on the list, including calling `clear`, is at risk of panicking.
pub struct CursorMut<'a, 'brand, T> {
    token: &'a mut GhostToken<'brand>,
    index: usize,
    node: Option<ThirdNodePtr<'brand, T>>,
    list: &'a mut TripodList<'brand, T>,
}

impl<'a, 'brand, T> CursorMut<'a, 'brand, T> {
    /// Creates a new instance pointing to the front element of the list, if any.
    pub fn new_front(token: &'a mut GhostToken<'brand>, list: &'a mut TripodList<'brand, T>) -> Self {
        let node = list.head_tail.as_ref().map(|head_tail| head_tail.0.borrow(token).deploy());

        Self { token, index: 0, node, list, }
    }

    /// Creates a new instance pointing to the back element of the list, if any.
    pub fn new_back(token: &'a mut GhostToken<'brand>, list: &'a mut TripodList<'brand, T>) -> Self {
        let node = list.head_tail.as_ref().map(|head_tail| head_tail.1.borrow(token).deploy());
        let index = list.len().checked_sub(1).unwrap_or(0);

        Self { token, index, node, list, }
    }

    /// Returns a read-only cursor pointing to the current element.
    pub fn as_cursor(&self) -> Cursor<'_, 'brand, T> {
        let token = &*self.token;
        let index = self.index;
        let node = self.node.as_ref().map(|rc| &**rc);
        let list = &*self.list;

        Cursor { token, index, node, list, }
    } 

    /// Returns the index of the element pointed to by the cursor in the list.
    ///
    /// If the cursor currently points to the "twilight" non-element, returns None.
    pub fn index(&self) -> Option<usize> { self.node.as_ref().map(|_| self.index) }

    /// Moves the cursor to the next element, if any.
    ///
    /// If there is no next element, then the cursor moves to the "twilight" non-element, which exists between the front
    /// and back element.
    pub fn move_next(&mut self) {
        let new_tripod = self.peek_next_node().map(|node| node.borrow(self.token).deploy());

        if let Some(tripod) = mem::replace(&mut self.node, new_tripod) {
            super::retract(tripod, self.token);
            self.index += 1;
        } else {
            self.index = 0;
        }
    }

    /// Moves the cursor to the previous element, if any.
    ///
    /// If there is no previous element, then the cursor moves to the "twilight" non-element, which exists between the front
    /// and back element.
    pub fn move_prev(&mut self) {
        let new_tripod = self.peek_prev_node().map(|node| node.borrow(self.token).deploy());

        if let Some(tripod) = mem::replace(&mut self.node, new_tripod) {
            super::retract(tripod, self.token);
            self.index = self.index.checked_sub(1).unwrap_or(0);
        } else {
            self.index = self.list.len().checked_sub(1).unwrap_or(0);
        }
    }

    /// Returns a mutable reference to the current element, if any.
    ///
    /// Unless the list is empty, there should always be a current element.
    pub fn current(&mut self) -> Option<&mut T> {
        let tripod = self.node.as_ref()?;
        Some(&mut tripod.borrow_mut(self.token).value)
    }

    /// Returns a reference to the next element, if any.
    ///
    /// #   Deviation
    ///
    /// It is not possible to return a mutable reference, safely.
    pub fn peek_next(&self) -> Option<&T> { self.peek_next_node().map(|node| &node.borrow(self.token).value) }

    /// Returns a reference to the previous element, if any.
    ///
    /// #   Deviation
    ///
    /// It is not possible to return a mutable reference, safely.
    pub fn peek_prev(&self) -> Option<&T> { self.peek_prev_node().map(|node| &node.borrow(self.token).value) }

    //  Internal: returns a reference to the next GhostNode.
    fn peek_next_node(&self) -> Option<&GhostNode<'brand, T>> {
        if let Some(node) = self.node.as_ref() {
            node.borrow(self.token).next.as_ref().map(|n| &**n)
        } else {
            self.list.front_node()
        }
    }

    //  Internal: returns a reference to the previous GhostNode.
    fn peek_prev_node(&self) -> Option<&GhostNode<'brand, T>> {
        if let Some(node) = self.node.as_ref() {
            node.borrow(self.token).prev.as_ref().map(|n| &**n)
        } else {
            self.list.back_node()
        }
    }
}

impl<'a, 'brand, T> CursorMut<'a, 'brand, T> {
    /// Inserts a new element in the list after the current one.
    ///
    /// If the cursor is pointing at the "twilight" non-element, then the new element is inserted at the front of the
    /// list.
    ///
    /// #   Complexity
    ///
    /// This operation is O(1) in the number of elements.
    ///
    /// One memory allocation and no deallocation occur.
    pub fn insert_after(&mut self, item: T) {
        let mut list = TripodList::new();
        list.push_front(item, self.token);

        self.splice_after(&mut list);

        debug_assert!(list.is_empty());
    }

    /// Inserts a new element in the list before the current one.
    ///
    /// If the cursor is pointing at the "twilight" non-element, then the new element is inserted at the back of the
    /// list.
    ///
    /// #   Complexity
    ///
    /// This operation is O(1) in the number of elements.
    ///
    /// One memory allocation and no deallocation occur.
    pub fn insert_before(&mut self, item: T) {
        let mut list = TripodList::new();
        list.push_back(item, self.token);

        self.splice_before(&mut list);

        debug_assert!(list.is_empty());
    }

    /// Removes the current element from the list, and return it.
    ///
    /// If the cursor is pointing to the "twilight" non-element, then None is returned and the cursor is left unmodified.
    /// Otherwise, the element is returned and the cursor is moved to the next element.
    ///
    /// #   Complexity
    ///
    /// This operation is O(1) in the number of elements.
    ///
    /// No memory allocation or deallocation occurs.
    pub fn remove_current(&mut self) -> Option<T> {
        let mut list = self.remove_current_as_list()?;
        debug_assert_eq!(1, list.len());

        list.pop_front(self.token)
    }

    /// Removes the current element from the list, and return it as a list of its own.
    ///
    /// If the cursor is pointing to the "twilight" non-element, then None is returned and the cursor is left unmodified.
    /// Otherwise, the element is returned and the cursor is moved to the next element.
    ///
    /// #   Complexity
    ///
    /// This operation is O(1) in the number of elements.
    ///
    /// No memory allocation or deallocation occurs.
    pub fn remove_current_as_list(&mut self) -> Option<TripodList<'brand, T>> {
        let node = self.node.take()?;
        let (head, tail) = self.list.head_tail.take()?;

        let prev = node.borrow_mut(self.token).prev.take();
        let next = node.borrow_mut(self.token).next.take();

        let (new_head_tail, result_head_tail, next_node) = match (prev, next) {
            //  `node` is in the middle of the list, gotta splice the two bits together.
            (Some(prev), Some(next)) => {
                let next_node = next.borrow(self.token).deploy();

                let result_head = prev.borrow_mut(self.token).next.replace(next).expect("node.prev.next == node");
                let result_tail = next_node.borrow_mut(self.token).prev.replace(prev).expect("node.next.prev == node");

                (Some((head, tail)), Some((result_head, result_tail)), Some(next_node))
            },
            //  `node` is the current head of the list.
            (None, Some(next)) => {
                let next_node = next.borrow(self.token).deploy();

                let result_tail = next.borrow_mut(self.token).prev.take().expect("node.next.prev == node");

                (Some((next, tail)), Some((head, result_tail)), Some(next_node))
            },
            //  `node` is the current tail of the list.
            (Some(prev), None) => {
                let result_head = prev.borrow_mut(self.token).next.take().expect("node.prev.next == node");

                (Some((head, prev)), Some((result_head, tail)), None)
            },
            //  `node` is the only element of the list.
            (None, None) => {
                (None, Some((head, tail)), None)
            }
        };

        super::retract(node, self.token);

        self.node = next_node;
        self.list.length -= 1;
        self.list.head_tail = new_head_tail;

        Some(TripodList { length: 1, head_tail: result_head_tail }) 
    }

    /// Inserts the elements from the given list after the current one.
    ///
    /// If the cursor is pointing at the "twilight" non-element, then the new elements are inserted at the front of the
    /// list.
    ///
    /// #   Complexity
    ///
    /// This operation is O(1) in the number of elements.
    ///
    /// No memory allocation or deallocation occurs.
    pub fn splice_after(&mut self, other: &mut TripodList<'brand, T>) {
        if let Some(node) = self.node.as_ref() {
            let (other_head, other_tail) = if let Some(other_ht) = other.head_tail.take() {
                other_ht
            } else {
                return;
            };

            let other_head_tripod = other_head.borrow(self.token).deploy();

            if let Some(previous_next) = node.borrow_mut(self.token).next.replace(other_head) {
                let previous_next_tripod = previous_next.borrow(self.token).deploy();

                other_tail.borrow_mut(self.token).next = Some(previous_next);

                let previous_node = previous_next_tripod.borrow_mut(self.token).prev.replace(other_tail);
                super::retract(previous_next_tripod, self.token);

                debug_assert!(previous_node.is_some(), "node.next.prev == node");

                other_head_tripod.borrow_mut(self.token).prev = previous_node;
                super::retract(other_head_tripod, self.token);
            } else {
                let (head, tail) = self.list.head_tail.take().expect("Non-empty since self.node is non-null!");

                other_head_tripod.borrow_mut(self.token).prev = Some(tail);
                super::retract(other_head_tripod, self.token);

                self.list.head_tail = Some((head, other_tail));
            }

            self.list.length += other.length;
            other.length = 0;
        } else {
            self.list.prepend(other, self.token);
        }
    }

    /// Inserts the elements from the given list before the current one.
    ///
    /// If the cursor is pointing at the "twilight" non-element, then the new elements are inserted at the back of the
    /// list.
    ///
    /// #   Complexity
    ///
    /// This operation is O(1) in the number of elements.
    ///
    /// No memory allocation or deallocation occurs.
    pub fn splice_before(&mut self, other: &mut TripodList<'brand, T>) {
        if let Some(node) = self.node.as_ref() {
            let (other_head, other_tail) = if let Some(other_ht) = other.head_tail.take() {
                other_ht
            } else {
                return;
            };
    
            let other_tail_tripod = other_tail.borrow(self.token).deploy();

            if let Some(previous_prev) = node.borrow_mut(self.token).prev.replace(other_tail) {
                let previous_prev_tripod = previous_prev.borrow(self.token).deploy();

                other_head.borrow_mut(self.token).prev = Some(previous_prev);

                let previous_node = previous_prev_tripod.borrow_mut(self.token).next.replace(other_head);
                super::retract(previous_prev_tripod, self.token);

                debug_assert!(previous_node.is_some(), "node.prev.next == node");

                other_tail_tripod.borrow_mut(self.token).next = previous_node;
                super::retract(other_tail_tripod, self.token);
            } else {
                let (head, tail) = self.list.head_tail.take().expect("Non-empty since self.node is non-null!");

                other_tail_tripod.borrow_mut(self.token).next = Some(head);
                super::retract(other_tail_tripod, self.token);

                self.list.head_tail = Some((other_head, tail));
            }

            self.list.length += other.length;
            self.index += other.length;
            other.length = 0;
        } else {
            self.list.append(other, self.token);
        }
    }

    /// Splits the list into two after the current element.
    ///
    /// If the cursor is pointing at the "twilight" non-element, then the entire contents of the list are moved.
    ///
    /// #   Complexity
    ///
    /// This operation is O(1) in the number of elements.
    ///
    /// No memory allocation or deallocation occurs.
    pub fn split_after(&mut self) -> TripodList<'brand, T> {
        if let Some(node) = &self.node {
            let next = node.borrow_mut(self.token).next.take();

            //  node is not the tail of the current list.
            if let Some(next) = next {
                let (head, tail) = self.list.head_tail.take().expect("non-empty, node is non-null!");
    
                let new_tail = next.borrow_mut(self.token).prev.take().expect("node.next.prev == node");

                let remaining_length = self.index + 1;
                let result_length = self.list.length - remaining_length;

                self.list.length = remaining_length;
                self.list.head_tail = Some((head, new_tail));

                TripodList { length: result_length, head_tail: Some((next, tail)) }
            } else {
                TripodList::new()
            }
        } else {
            mem::replace(self.list, TripodList::new())
        }
    }

    /// Splits the list into two before the current element.
    ///
    /// If the cursor is pointing at the "twilight" non-element, then the entire contents of the list are moved.
    ///
    /// #   Complexity
    ///
    /// This operation is O(1) in the number of elements.
    ///
    /// No memory allocation or deallocation occurs.
    pub fn split_before(&mut self) -> TripodList<'brand, T> {
        if let Some(node) = &self.node {
            let prev = node.borrow_mut(self.token).prev.take();

            //  node is not the head of the current list.
            if let Some(prev) = prev {
                let (head, tail) = self.list.head_tail.take().expect("non-empty, node is non-null!");
    
                let new_head = prev.borrow_mut(self.token).next.take().expect("node.prev.next == node");

                let result_length = self.index;
                let remaining_length = self.list.length - result_length;

                self.index = 0;
                self.list.length = remaining_length;
                self.list.head_tail = Some((new_head, tail));

                TripodList { length: result_length, head_tail: Some((head, prev)) }
            } else {
                TripodList::new()
            }
        } else {
            mem::replace(self.list, TripodList::new())
        }
    }
}

impl<'a, 'brand, T> Drop for CursorMut<'a, 'brand, T> {
    fn drop(&mut self) {
        if let Some(tripod) = self.node.take() {
            super::retract(tripod, self.token);
        }
    }
}

#[cfg(test)]
mod tests {

use std::fmt::Debug;

use super::super::tests::*;
use super::*;

#[track_caller]
fn assert_none<'a, 'brand, T>(cursor: Cursor<'a, 'brand, T>)
where
    T: Debug + Eq,
{
    assert_eq!(None, cursor.index());
    assert_eq!(None, cursor.current());
    assert_eq!(None, cursor.peek_next());
    assert_eq!(None, cursor.peek_prev());
}

#[track_caller]
fn assert_cursor(before: &[&str], current: &str, after: &[&str], cursor: Cursor<'_, '_, String>) {
    assert_eq!(Some(before.len()), cursor.index());
    assert_eq!(before.last().copied(), cursor.peek_prev().map(String::as_str));
    assert_eq!(Some(current), cursor.current().map(String::as_str));
    assert_eq!(after.first().copied(), cursor.peek_next().map(String::as_str));
    
    let (actual_before, actual_after) = cursor.before_after();

    assert_eq!(before, collect(actual_before));
    assert_eq!(after, collect(actual_after));
}

#[track_caller]
fn assert_twilight(before: &[&str], cursor: Cursor<'_, '_, String>) {
    assert_eq!(None, cursor.index());
    assert_eq!(before.last().copied(), cursor.peek_prev().map(String::as_str));
    assert_eq!(None, cursor.current().map(String::as_str));
    assert_eq!(before.first().copied(), cursor.peek_next().map(String::as_str));

    let (actual_before, actual_after) = cursor.before_after();
    let (actual_before, actual_after) = (collect(actual_before), collect(actual_after));

    assert_eq!(before, actual_before);
    assert!(actual_after.is_empty(), "{:?}", actual_after);
}

//  Creates a cursor at the specified index.
fn place_cursor<'a, 'brand>(token: &'a mut GhostToken<'brand>, list: &'a mut TripodList<'brand, String>, at: usize)
    -> CursorMut<'a, 'brand, String>
{
    assert!(at <= list.len());

    let mut cursor = CursorMut::new_front(token, list);

    for _ in 0..at {
        cursor.move_next();
    }

    cursor
}

#[test]
fn cursor_front_empty() {
    //  Test all functions on empty list.
    with_list::<String, _, _>(vec!(), |token, list| {
        let mut cursor = Cursor::new_front(token, list);
        assert_none(cursor);

        cursor.move_next();
        assert_none(cursor);

        cursor.move_prev();
        assert_none(cursor);
    });
}

#[test]
fn cursor_back_empty() {
    //  Test all functions on empty list.
    with_list::<String, _, _>(vec!(), |token, list| {
        let mut cursor = Cursor::new_back(token, list);
        assert_none(cursor);

        cursor.move_next();
        assert_none(cursor);

        cursor.move_prev();
        assert_none(cursor);
    });
}

#[test]
fn cursor_move_next() {
    with_list(create(0..4), |token, list| {
        let mut cursor = Cursor::new_front(token, list);

        assert_cursor(&[], "0", &["1", "2", "3"], cursor);

        cursor.move_next();

        assert_cursor(&["0"], "1", &["2", "3"], cursor);

        cursor.move_next();

        assert_cursor(&["0", "1"], "2", &["3"], cursor);

        cursor.move_next();

        assert_cursor(&["0", "1", "2"], "3", &[], cursor);

        cursor.move_next();

        assert_twilight(&["0", "1", "2", "3"], cursor);

        cursor.move_next();

        assert_cursor(&[], "0", &["1", "2", "3"], cursor);
    });
}

#[test]
fn cursor_move_prev() {
    with_list(create(0..4), |token, list| {
        let mut cursor = Cursor::new_back(token, list);

        assert_cursor(&["0", "1", "2"], "3", &[], cursor);

        cursor.move_prev();

        assert_cursor(&["0", "1"], "2", &["3"], cursor);

        cursor.move_prev();

        assert_cursor(&["0"], "1", &["2", "3"], cursor);

        cursor.move_prev();

        assert_cursor(&[], "0", &["1", "2", "3"], cursor);

        cursor.move_prev();

        assert_twilight(&["0", "1", "2", "3"], cursor);

        cursor.move_prev();

        assert_cursor(&["0", "1", "2"], "3", &[], cursor);
    });
}

#[test]
fn cursor_mut_front_empty() {
    //  Test all functions on empty list.
    with_list::<String, _, _>(vec!(), |token, list| {
        let mut cursor = CursorMut::new_front(token, list);
        assert_none(cursor.as_cursor());

        cursor.move_next();
        assert_none(cursor.as_cursor());

        cursor.move_prev();
        assert_none(cursor.as_cursor());
    });
}

#[test]
fn cursor_mut_back_empty() {
    //  Test all functions on empty list.
    with_list::<String, _, _>(vec!(), |token, list| {
        let mut cursor = CursorMut::new_back(token, list);
        assert_none(cursor.as_cursor());

        cursor.move_next();
        assert_none(cursor.as_cursor());

        cursor.move_prev();
        assert_none(cursor.as_cursor());
    });
}

#[test]
fn cursor_mut_move_next() {
    with_list(create(0..4), |token, list| {
        let mut cursor = CursorMut::new_front(token, list);

        assert_cursor(&[], "0", &["1", "2", "3"], cursor.as_cursor());

        cursor.move_next();

        assert_cursor(&["0"], "1", &["2", "3"], cursor.as_cursor());

        cursor.move_next();

        assert_cursor(&["0", "1"], "2", &["3"], cursor.as_cursor());

        cursor.move_next();

        assert_cursor(&["0", "1", "2"], "3", &[], cursor.as_cursor());

        cursor.move_next();

        assert_twilight(&["0", "1", "2", "3"], cursor.as_cursor());

        cursor.move_next();

        assert_cursor(&[], "0", &["1", "2", "3"], cursor.as_cursor());
    });
}

#[test]
fn cursor_mut_move_prev() {
    with_list(create(0..4), |token, list| {
        let mut cursor = CursorMut::new_back(token, list);

        assert_cursor(&["0", "1", "2"], "3", &[], cursor.as_cursor());

        cursor.move_prev();

        assert_cursor(&["0", "1"], "2", &["3"], cursor.as_cursor());

        cursor.move_prev();

        assert_cursor(&["0"], "1", &["2", "3"], cursor.as_cursor());

        cursor.move_prev();

        assert_cursor(&[], "0", &["1", "2", "3"], cursor.as_cursor());

        cursor.move_prev();

        assert_twilight(&["0", "1", "2", "3"], cursor.as_cursor());

        cursor.move_prev();

        assert_cursor(&["0", "1", "2"], "3", &[], cursor.as_cursor());
    });
}

#[track_caller]
fn assert_insert_after(list: Vec<String>, element: String, at: usize, before: &[&str], current: &str, after: &[&str]) {
    with_list(list, |token, list| {
        let mut cursor = place_cursor(token, list, at);

        cursor.insert_after(element);

        assert_cursor(before, current, after, cursor.as_cursor());
    });
}

#[test]
fn cursor_mut_insert_after() {
    assert_insert_after(create(0..4), "4".to_string(), 0, &[], "0", &["4", "1", "2", "3"]);

    assert_insert_after(create(0..4), "4".to_string(), 1, &["0"], "1", &["4", "2", "3"]);

    assert_insert_after(create(0..4), "4".to_string(), 2, &["0", "1"], "2", &["4", "3"]);

    assert_insert_after(create(0..4), "4".to_string(), 3, &["0", "1", "2"], "3", &["4"]);

    //  Special case: "empty"
    with_list(create(0..0), |token, list| {
        let mut cursor = CursorMut::new_front(token, list);

        cursor.insert_after("4".to_string());

        assert_twilight(&["4"], cursor.as_cursor());
    });

    //  Special case: "twilight"
    with_list(create(0..4), |token, list| {
        let mut cursor = place_cursor(token, list, 4);

        cursor.insert_after("4".to_string());

        assert_twilight(&["4", "0", "1", "2", "3"], cursor.as_cursor());
    });
}

#[track_caller]
fn assert_insert_before(list: Vec<String>, element: String, at: usize, before: &[&str], current: &str, after: &[&str]) {
    with_list(list, |token, list| {
        let mut cursor = place_cursor(token, list, at);

        cursor.insert_before(element);

        assert_cursor(before, current, after, cursor.as_cursor());
    });
}

#[test]
fn cursor_mut_insert_before() {
    assert_insert_before(create(0..4), "4".to_string(), 0, &["4"], "0", &["1", "2", "3"]);

    assert_insert_before(create(0..4), "4".to_string(), 1, &["0", "4"], "1", &["2", "3"]);

    assert_insert_before(create(0..4), "4".to_string(), 2, &["0", "1", "4"], "2", &["3"]);

    assert_insert_before(create(0..4), "4".to_string(), 3, &["0", "1", "2", "4"], "3", &[]);

    //  Special case: "empty"
    with_list(create(0..0), |token, list| {
        let mut cursor = CursorMut::new_front(token, list);

        cursor.insert_before("4".to_string());

        assert_twilight(&["4"], cursor.as_cursor());
    });

    //  Special case: "twilight"
    with_list(create(0..4), |token, list| {
        let mut cursor = place_cursor(token, list, 4);

        cursor.insert_before("4".to_string());

        assert_twilight(&["0", "1", "2", "3", "4"], cursor.as_cursor());
    });
}

#[track_caller]
fn assert_splice_after(list: Vec<String>, other: Vec<String>, at: usize, before: &[&str], current: &str, after: &[&str]) {
    with_list_duo(list, other, |token, list, other| {
        let mut cursor = place_cursor(token, list, at);

        cursor.splice_after(other);
        assert!(other.is_empty(), "{} elements!", other.len());

        assert_cursor(before, current, after, cursor.as_cursor());
    });
}

#[track_caller]
fn assert_splice_after_twilight(list: Vec<String>, other: Vec<String>, before: &[&str]) {
    with_list_duo(list, other, |token, list, other| {
        let mut cursor = place_cursor(token, list, list.len());

        cursor.splice_after(other);
        assert!(other.is_empty(), "{} elements!", other.len());

        assert_twilight(before, cursor.as_cursor());
    });
}

#[test]
fn cursor_mut_splice_after() {
    //  Empty spliced
    {
        assert_splice_after(create(0..4), create(0..0), 0, &[], "0", &["1", "2", "3"]);
        assert_splice_after(create(0..4), create(0..0), 1, &["0"], "1", &["2", "3"]);
        assert_splice_after(create(0..4), create(0..0), 2, &["0", "1"], "2", &["3"]);
        assert_splice_after(create(0..4), create(0..0), 3, &["0", "1", "2"], "3", &[]);

        //  Special case: "empty"
        assert_splice_after_twilight(create(0..0), create(0..0), &[]);

        //  Special case: "twilight"
        assert_splice_after_twilight(create(0..4), create(0..0), &["0", "1", "2", "3"]);
    }

    //  Single-element spliced
    //  See insert_after.

    //  Multi-elements spliced
    {
        assert_splice_after(create(0..4), create(4..7), 0, &[], "0", &["4", "5", "6", "1", "2", "3"]);
        assert_splice_after(create(0..4), create(4..7), 1, &["0"], "1", &["4", "5", "6", "2", "3"]);
        assert_splice_after(create(0..4), create(4..7), 2, &["0", "1"], "2", &["4", "5", "6", "3"]);
        assert_splice_after(create(0..4), create(4..7), 3, &["0", "1", "2"], "3", &["4", "5", "6"]);

        //  Special case: "empty"
        assert_splice_after_twilight(create(0..0), create(4..7), &["4", "5", "6"]);

        //  Special case: "twilight"
        assert_splice_after_twilight(create(0..4), create(4..7), &["4", "5", "6", "0", "1", "2", "3"]);
    }
}

#[track_caller]
fn assert_splice_before(list: Vec<String>, other: Vec<String>, at: usize, before: &[&str], current: &str, after: &[&str]) {
    with_list_duo(list, other, |token, list, other| {
        let mut cursor = place_cursor(token, list, at);

        cursor.splice_before(other);
        assert!(other.is_empty(), "{} elements!", other.len());

        assert_cursor(before, current, after, cursor.as_cursor());
    });
}

#[track_caller]
fn assert_splice_before_twilight(list: Vec<String>, other: Vec<String>, before: &[&str]) {
    with_list_duo(list, other, |token, list, other| {
        let mut cursor = place_cursor(token, list, list.len());

        cursor.splice_before(other);
        assert!(other.is_empty(), "{} elements!", other.len());

        assert_twilight(before, cursor.as_cursor());
    });
}

#[test]
fn cursor_mut_splice_before() {
    //  Empty spliced
    {
        assert_splice_before(create(0..4), create(0..0), 0, &[], "0", &["1", "2", "3"]);
        assert_splice_before(create(0..4), create(0..0), 1, &["0"], "1", &["2", "3"]);
        assert_splice_before(create(0..4), create(0..0), 2, &["0", "1"], "2", &["3"]);
        assert_splice_before(create(0..4), create(0..0), 3, &["0", "1", "2"], "3", &[]);

        //  Special case: "empty"
        assert_splice_before_twilight(create(0..0), create(0..0), &[]);

        //  Special case: "twilight"
        assert_splice_before_twilight(create(0..4), create(0..0), &["0", "1", "2", "3"]);
    }

    //  Single-element spliced
    //  See insert_after.

    //  Multi-elements spliced
    {
        assert_splice_before(create(0..4), create(4..7), 0, &["4", "5", "6"], "0", &["1", "2", "3"]);
        assert_splice_before(create(0..4), create(4..7), 1, &["0", "4", "5", "6"], "1", &["2", "3"]);
        assert_splice_before(create(0..4), create(4..7), 2, &["0", "1", "4", "5", "6"], "2", &["3"]);
        assert_splice_before(create(0..4), create(4..7), 3, &["0", "1", "2", "4", "5", "6"], "3", &[]);

        //  Special case: "empty"
        assert_splice_before_twilight(create(0..0), create(4..7), &["4", "5", "6"]);

        //  Special case: "twilight"
        assert_splice_before_twilight(create(0..4), create(4..7), &["0", "1", "2", "3", "4", "5", "6"]);
    }
}

#[track_caller]
fn assert_remove_current(list: Vec<String>, at: usize, result: Option<&str>, before: &[&str], current: &str, after: &[&str]) {
    with_list(list, |token, list| {
        let mut cursor = place_cursor(token, list, at);

        let actual = cursor.remove_current();
        assert_eq!(result, actual.as_ref().map(String::as_str));

        assert_cursor(before, current, after, cursor.as_cursor());
    });
}

#[test]
fn cursor_mut_remove_current() {
    assert_remove_current(create(0..4), 0, Some("0"), &[], "1", &["2", "3"]);
    assert_remove_current(create(0..4), 1, Some("1"), &["0"], "2", &["3"]);
    assert_remove_current(create(0..4), 2, Some("2"), &["0", "1"], "3", &[]);

    //  Special-case: "empty"
    with_list(create(0..0), |token, list| {
        let mut cursor = CursorMut::new_front(token, list);

        let actual = cursor.remove_current();
        assert_eq!(None, actual);

        assert_twilight(&[], cursor.as_cursor());
    });

    //  Special-case: "twilight"
    with_list(create(0..4), |token, list| {
        let mut cursor = place_cursor(token, list, 4);

        let actual = cursor.remove_current();
        assert_eq!(None, actual);

        assert_twilight(&["0", "1", "2", "3"], cursor.as_cursor());
    });

    //  Special-case: "next twilight"
    with_list(create(0..4), |token, list| {
        let mut cursor = place_cursor(token, list, 3);

        let actual = cursor.remove_current();
        assert_eq!(Some("3"), actual.as_ref().map(String::as_str));

        assert_twilight(&["0", "1", "2"], cursor.as_cursor());
    });
}

#[track_caller]
fn assert_remove_current_as_list(list: Vec<String>, at: usize, result: Option<&str>, before: &[&str], current: &str, after: &[&str]) {
    let result: Vec<_> = result.iter().copied().collect();

    with_list(list, |token, list| {
        let mut cursor = place_cursor(token, list, at);

        let actual = cursor.remove_current_as_list();

        assert_cursor(before, current, after, cursor.as_cursor());

        mem::drop(cursor);

        assert_list(&result, token, actual.expect("Some"));
    });
}

#[test]
fn cursor_mut_remove_current_as_list() {
    assert_remove_current_as_list(create(0..4), 0, Some("0"), &[], "1", &["2", "3"]);
    assert_remove_current_as_list(create(0..4), 1, Some("1"), &["0"], "2", &["3"]);
    assert_remove_current_as_list(create(0..4), 2, Some("2"), &["0", "1"], "3", &[]);

    //  Special-case: "empty"
    with_list(create(0..0), |token, list| {
        let mut cursor = CursorMut::new_front(token, list);

        let actual = cursor.remove_current_as_list();
        assert!(actual.is_none());

        assert_twilight(&[], cursor.as_cursor());
    });

    //  Special-case: "twilight"
    with_list(create(0..4), |token, list| {
        let mut cursor = place_cursor(token, list, 4);

        let actual = cursor.remove_current_as_list();
        assert!(actual.is_none());

        assert_twilight(&["0", "1", "2", "3"], cursor.as_cursor());
    });

    //  Special-case: "next twilight"
    with_list(create(0..4), |token, list| {
        let mut cursor = place_cursor(token, list, 3);

        let actual = cursor.remove_current_as_list();

        assert_twilight(&["0", "1", "2"], cursor.as_cursor());

        mem::drop(cursor);

        assert_list(&["3"], token, actual.expect("Some"));
    });
}

#[track_caller]
fn assert_split_after(list: Vec<String>, at: usize, before: &[&str], current: &str, after: &[&str]) {
    with_list(list, |token, list| {
        let mut cursor = place_cursor(token, list, at);

        let actual = cursor.split_after();

        assert_cursor(before, current, &[], cursor.as_cursor());

        mem::drop(cursor);

        assert_list(after, token, actual);
    });
}

#[test]
fn cursor_mut_split_after() {
    assert_split_after(create(0..4), 0, &[], "0", &["1", "2", "3"]);
    assert_split_after(create(0..4), 1, &["0"], "1", &["2", "3"]);
    assert_split_after(create(0..4), 2, &["0", "1"], "2", &["3"]);
    assert_split_after(create(0..4), 3, &["0", "1", "2"], "3", &[]);

    //  Special-case: "empty"
    with_list(create(0..0), |token, list| {
        let mut cursor = CursorMut::new_front(token, list);

        let actual = cursor.split_after();

        assert_twilight(&[], cursor.as_cursor());

        mem::drop(cursor);

        assert_list(&[], token, actual);
    });

    //  Special-case: "twilight"
    with_list(create(0..4), |token, list| {
        let mut cursor = place_cursor(token, list, 4);

        let actual = cursor.split_after();

        assert_twilight(&[], cursor.as_cursor());

        mem::drop(cursor);

        assert_list(&["0", "1", "2", "3"], token, actual);
    });
}

#[track_caller]
fn assert_split_before(list: Vec<String>, at: usize, before: &[&str], current: &str, after: &[&str]) {
    with_list(list, |token, list| {
        let mut cursor = place_cursor(token, list, at);

        let actual = cursor.split_before();

        assert_cursor(&[], current, &after, cursor.as_cursor());

        mem::drop(cursor);

        assert_list(before, token, actual);
    });
}

#[test]
fn cursor_mut_split_before() {
    assert_split_before(create(0..4), 0, &[], "0", &["1", "2", "3"]);
    assert_split_before(create(0..4), 1, &["0"], "1", &["2", "3"]);
    assert_split_before(create(0..4), 2, &["0", "1"], "2", &["3"]);
    assert_split_before(create(0..4), 3, &["0", "1", "2"], "3", &[]);

    //  Special-case: "empty"
    with_list(create(0..0), |token, list| {
        let mut cursor = CursorMut::new_front(token, list);

        let actual = cursor.split_before();

        assert_twilight(&[], cursor.as_cursor());

        mem::drop(cursor);

        assert_list(&[], token, actual);
    });

    //  Special-case: "twilight"
    with_list(create(0..4), |token, list| {
        let mut cursor = place_cursor(token, list, 4);

        let actual = cursor.split_before();

        assert_twilight(&[], cursor.as_cursor());

        mem::drop(cursor);

        assert_list(&["0", "1", "2", "3"], token, actual);
    });
}

} // mod tests
