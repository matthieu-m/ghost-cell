//! A LinkedList, with externally supplied token.
//!
//! A number of operations normally implemented by traits cannot be successfully implemented on this collection due to
//! the requirement of supplying the GhostToken externally.

mod iter;
mod cursor;

pub use iter::Iter;
pub use cursor::Cursor;

#[cfg(feature = "experimental-ghost-cursor")]
pub use cursor::CursorMut;

use ghost_cell::{GhostCell, GhostToken};
use static_rc::StaticRc;

#[cfg(feature = "experimental-ghost-cursor")]
use core::mem;

#[cfg(feature = "experimental-ghost-cursor")]
use ghost_cell::GhostCursor;

/// A safe implementation of a linked-list build upon `GhostCell` and `StaticRc`.
///
/// The future is now!
pub struct LinkedList<'brand, T> {
    head_tail: Option<(HalfNodePtr<'brand, T>, HalfNodePtr<'brand, T>)>,
}

impl<'brand, T> LinkedList<'brand, T> {
    /// Creates an empty list.
    pub const fn new() -> Self { Self { head_tail: None } }

    /// Creates an iterator over self.
    pub fn iter<'a>(&'a self, token: &'a GhostToken<'brand>) -> Iter<'a, 'brand, T> {
        Iter::new(token, self)
    }

    /// Creates a cursor pointing to the front element, if any.
    pub fn cursor_front<'a>(&'a self, token: &'a GhostToken<'brand>) -> Cursor<'a, 'brand, T> {
        Cursor::new_front(token, self)
    }

    /// Creates a cursor pointing to the back element, if any.
    pub fn cursor_back<'a>(&'a self, token: &'a GhostToken<'brand>) -> Cursor<'a, 'brand, T> {
        Cursor::new_back(token, self)
    }

    /// Returns whether the list is empty, or not.
    pub fn is_empty(&self) -> bool { self.head_tail.is_none() }

    /// Returns the number of elements of the list.
    ///
    /// #   Complexity
    ///
    /// This operation is O(N).
    ///
    /// Maintaining a separate length field is incompatible with arbitrary splits at a given cursor position.
    pub fn len(&self, token: &GhostToken<'brand>) -> usize { self.iter(token).count() }

    /// Clears the list, making it empty.
    ///
    /// #   Complexity
    ///
    /// This operation is O(N), where N is the number of elements.
    pub fn clear(&mut self, token: &mut GhostToken<'brand>) {
        while let Some(_) = self.pop_back(token) {}
    }

    /// Returns a reference to the first element, if any.
    pub fn front<'a>(&'a self, token: &'a GhostToken<'brand>) -> Option<&'a T> {
        self.head_tail.as_ref().map(|(head, _)| {
            &head.borrow(token).value
        })
    }

    /// Returns a mutable reference to the first element, if any.
    pub fn front_mut<'a>(&'a mut self, token: &'a mut GhostToken<'brand>) -> Option<&'a mut T> {
        self.head_tail.as_mut().map(move |(head, _)| {
            &mut head.borrow_mut(token).value
        })
    }

    /// Returns a reference to the last element, if any.
    pub fn back<'a>(&'a self, token: &'a GhostToken<'brand>) -> Option<&'a T> {
        self.head_tail.as_ref().map(|(_, tail)| {
            &tail.borrow(token).value
        })
    }

    /// Returns a mutable reference to the last element, if any.
    pub fn back_mut<'a>(&'a mut self, token: &'a mut GhostToken<'brand>) -> Option<&'a mut T> {
        self.head_tail.as_mut().map(move |(_, tail)| {
            &mut tail.borrow_mut(token).value
        })
    }

    /// Prepends the given element at the front of the list.
    pub fn push_front(&mut self, value: T, token: &mut GhostToken<'brand>) {
        let (one, two) = Self::new_halves(value);

        let head_tail = if let Some((head, tail)) = self.head_tail.take() {
            head.borrow_mut(token).prev = Some(one);

            two.borrow_mut(token).next = Some(head);

            (two, tail)
        } else {
            (one, two)
        };

        self.head_tail = Some(head_tail);
    }

    /// Removes and returns the first element of the list, if any.
    pub fn pop_front(&mut self, token: &mut GhostToken<'brand>) -> Option<T> {
        let (head, tail) = self.head_tail.take()?;

        if StaticRc::as_ptr(&head) == StaticRc::as_ptr(&tail) {
            return Some(Self::into_inner(head, tail));
        }

        let next = head.borrow_mut(token).next.take()
            .expect("Non-tail should have a next node");
        let other_head = next.borrow_mut(token).prev.take()
            .expect("Non-head should have a previous node");

        self.head_tail = Some((next, tail));

        Some(Self::into_inner(head, other_head))
    }

    /// Appends the given element at the back of the list.
    pub fn push_back(&mut self, value: T, token: &mut GhostToken<'brand>) {
        let (one, two) = Self::new_halves(value);

        let head_tail = if let Some((head, tail)) = self.head_tail.take() {
            tail.borrow_mut(token).next = Some(one);

            two.borrow_mut(token).prev = Some(tail);

            (head, two)
        } else {
            (one, two)
        };

        self.head_tail = Some(head_tail);
    }

    /// Removes and returns the last element of the list, if any.
    pub fn pop_back(&mut self, token: &mut GhostToken<'brand>) -> Option<T> {
        let (head, tail) = self.head_tail.take()?;

        if StaticRc::as_ptr(&head) == StaticRc::as_ptr(&tail) {
            return Some(Self::into_inner(head, tail));
        }

        let prev = tail.borrow_mut(token).prev.take()
            .expect("Non-head should have a previous node");
        let other_tail = prev.borrow_mut(token).next.take()
            .expect("Non-tail should have a next node");

        self.head_tail = Some((head, prev));

        Some(Self::into_inner(tail, other_tail))
    }

    fn new_halves(value: T) -> (HalfNodePtr<'brand, T>, HalfNodePtr<'brand, T>) {
        let node = Node { value, prev: None, next: None, };
        let full = FullNodePtr::new(GhostNode::new(node));

        StaticRc::split::<1, 1>(full)
    }

    fn into_inner(left: HalfNodePtr<'brand, T>, right: HalfNodePtr<'brand, T>) -> T {
        let full = FullNodePtr::join(left, right);
        let ghost_cell = FullNodePtr::into_inner(full);
        let node = GhostNode::into_inner(ghost_cell);

        //  If the node still has a prev and next, they are leaked.
        debug_assert!(node.prev.is_none());
        debug_assert!(node.next.is_none());

        node.value
    }
}

#[cfg(feature = "experimental-ghost-cursor")]
impl<'brand, T> LinkedList<'brand, T> {
    /// Appends all elements of `other`, in order, to the back of this list.
    ///
    /// After this call, `other` is empty
    ///
    /// #   Complexity
    ///
    /// This operation is O(1) in the number of elements.
    ///
    /// No memory allocation or deallocation occurs.
    pub fn append(&mut self, other: &mut Self, token: &mut GhostToken<'brand>) {
        let other_ht = if let Some(other_ht) = other.head_tail.take() {
            other_ht
        } else {
            return;
        };

        if let Some(self_ht) = self.head_tail.take() {
            let (new_head, mid_tail) = self_ht;
            let (mid_head, new_tail) = other_ht;

            mid_tail.borrow_mut(token).next = Some(mid_head);

            let previous = static_rc::lift_with_mut(Some(mid_tail), token, |mid_tail: &Option<HalfNodePtr<'brand, T>>, token| {
                let mut cursor = GhostCursor::new(token, Some(mid_tail.as_ref().unwrap()));

                cursor.move_mut(|mid_tail| mid_tail.next.as_ref().map(core::borrow::Borrow::borrow))
                    .expect("mid_tail.next was just set!");

                let mid_head = cursor.into_inner().expect("mid_head was just computed!");

                &mut mid_head.prev
            });

            debug_assert!(previous.is_none(), "mid_head should not have had any previous!");

            self.head_tail = Some((new_head, new_tail));
        } else {
            self.head_tail = Some(other_ht);
        }
    }

    /// Prepends all elements of `other`, in order, to the front of this list.
    ///
    /// After this call, `other` is empty
    ///
    /// #   Complexity
    ///
    /// This operation is O(1) in the number of elements.
    ///
    /// No memory allocation or deallocation occurs.
    pub fn prepend(&mut self, other: &mut Self, token: &mut GhostToken<'brand>) {
        other.append(self, token);
        mem::swap(self, other);
    }

    /// Creates a cursor pointing to the front element, if any.
    pub fn cursor_front_mut<'a>(&'a mut self, token: &'a mut GhostToken<'brand>) -> CursorMut<'a, 'brand, T> {
        CursorMut::new_front(token, self)
    }

    /// Creates a cursor pointing to the back element, if any.
    pub fn cursor_back_mut<'a>(&'a mut self, token: &'a mut GhostToken<'brand>) -> CursorMut<'a, 'brand, T> {
        CursorMut::new_back(token, self)
    }

    /// Splits the list in two at the given index. Returns a list containing everything after the given index, inclusive.
    ///
    /// Returns None if the given index is out of bounds.
    ///
    /// #   Complexity
    ///
    /// This operations is O(min(`at`, N)), where N is the number of elements.
    ///
    /// No memory allocation or deallocation occurs.
    pub fn split_off(&mut self, at: usize, token: &mut GhostToken<'brand>) -> Option<Self> {
        //  This is not the most optimal implementation, but it works, and respects the promised algorithmic complexity.
        let mut head = LinkedList::new();

        for _ in 0..at {
            let element = if let Some(element) = self.pop_front(token) {
                element
            } else {
                //  Restore popped elements, and pretend that nothing happened.
                self.prepend(&mut head, token);
                return None;
            };
            head.push_back(element, token);
        }

        mem::swap(self, &mut head);

        Some(head)
    }

    /// Removes the element at the given index, and returns it, if the index is within bounds.
    ///
    /// #   Complexity
    ///
    /// This operations is O(min(`at`, N)), where N is the number of elements.
    ///
    /// No memory allocation occurs, and a single memory deallocation occurs.
    pub fn remove(&mut self, at: usize, token: &mut GhostToken<'brand>) -> Option<T> {
        //  This is not the most optimal implementation, but it works, and respects the promised algorithmic complexity.
        let mut head = LinkedList::new();

        for _ in 0..at {
            let element = if let Some(element) = self.pop_front(token) {
                element
            } else {
                //  Restore popped elements, and pretend that nothing happened.
                self.prepend(&mut head, token);
                return None;
            };
            head.push_back(element, token);
        }

        let result = self.pop_front(token);

        //  Restore popped elements!
        self.prepend(&mut head, token);

        result
    }

}

impl<'brand, T> Default for LinkedList<'brand, T> {
    fn default() -> Self { Self::new() }
}

//
//  Implementation
//

struct Node<'brand, T> {
    value: T,
    prev: Option<HalfNodePtr<'brand, T>>,
    next: Option<HalfNodePtr<'brand, T>>,
}

type GhostNode<'brand, T> = GhostCell<'brand, Node<'brand, T>>;
type HalfNodePtr<'brand, T> = StaticRc<GhostNode<'brand, T>, 1, 2>;
type FullNodePtr<'brand, T> = StaticRc<GhostNode<'brand, T>, 2, 2>;

#[cfg(test)]
mod tests {

use std::panic::{self, AssertUnwindSafe};

use super::*;

pub(crate) fn with_list<T, R, F>(initial: Vec<T>, fun: F) -> R
where
    F: for<'brand> FnOnce(&mut GhostToken<'brand>, &mut LinkedList<'brand, T>) -> R,
{
    GhostToken::new(|mut token| {
        let mut list = LinkedList::new();
        
        for value in initial {
            list.push_back(value, &mut token);
        }

        let result = panic::catch_unwind(AssertUnwindSafe(|| fun(&mut token, &mut list)));

        list.clear(&mut token);

        result.expect("No Panic")
    })
}

} // mod tests
