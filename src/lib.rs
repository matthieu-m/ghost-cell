//! This library provides an implementation of `GhostCell` and its `GhostToken`:
//!
//! The implementation is based on http://plv.mpi-sws.org/rustbelt/ghostcell/.
//!
//! #   Safety
//!
//! http://plv.mpi-sws.org/rustbelt/ghostcell/ left some blanks in the implementation of `GhostCell` and `GhostToken`
//! that I have filled in myself. I hopefully didn't make a mistake, hopefully.
//!
//! Use at your own risk!
//!
//!
//! #   Example
//!
//! A simple self-contained example:
//!
//! ```rust
//! use ghost_cell::{GhostToken, GhostCell};
//!
//! fn demo(n: usize) {
//!     let value = GhostToken::new(|mut token| {
//!         let cell = GhostCell::new(42);
//!
//!         let vec: Vec<_> = (0..n).map(|_| &cell).collect();
//!
//!         *vec[n / 2].borrow_mut(&mut token) = 33;
//!
//!         *cell.borrow(&token)
//!     });
//!
//!     assert_eq!(value, 33);
//! }
//! ```

//  Generic features.
#![cfg_attr(not(test), no_std)]

//  Lints.
#![deny(missing_docs)]

mod ghost_cell;

pub use self::ghost_cell::{GhostCell, GhostToken};
