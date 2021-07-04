//! This library provides an implementation of `GhostCell` and its `GhostToken` as per
//! http://plv.mpi-sws.org/rustbelt/ghostcell/ as well as some extensions.
//!
//! #   Safety
//!
//! The actual implementation of `GhostCell` is found at https://gitlab.mpi-sws.org/FP/ghostcell/-/tree/master/ghostcell
//! and has been proven safe. I have carefully checked that this implementation faithfully reproduces the safety
//! guarantees.
//!
//! Extensions to `GhostCell`, such as `GhostCursor`, are not proven, neither at the design nor implementation level.
//! As such, they are only available if the appropriate Cargo features are enabled.
//!
//! #   Example
//!
//! A simple self-contained example:
//!
//! ```rust
//! use ghost_cell::{GhostToken, GhostCell};
//!
//! let n = 42;
//!
//! let value = GhostToken::new(|mut token| {
//!     let cell = GhostCell::new(42);
//!
//!     let vec: Vec<_> = (0..n).map(|_| &cell).collect();
//!
//!     *vec[n / 2].borrow_mut(&mut token) = 33;
//!
//!     *cell.borrow(&token)
//! });
//!
//! assert_eq!(33, value);
//! ```

//  Generic features.
#![cfg_attr(not(test), no_std)]

//  Lints.
#![deny(missing_docs)]

pub mod ghost_cell;

pub use self::ghost_cell::{GhostCell, GhostToken};

pub mod ghost_borrow;

pub use self::ghost_borrow::GhostBorrow;

#[cfg(feature = "experimental-multiple-mutable-borrows")]
pub mod ghost_borrow_mut;

#[cfg(feature = "experimental-multiple-mutable-borrows")]
pub use self::ghost_borrow_mut::{GhostBorrowMut, GhostAliasingError, VoidError};

#[cfg(feature = "experimental-ghost-cursor")]
pub mod ghost_cursor;

#[cfg(feature = "experimental-ghost-cursor")]
pub use self::ghost_cursor::GhostCursor;
