//! A repository of collections written entirely in safe, zero-cost, stable, Rust.
//!
//! #   Safety
//!
//! This repository is built upon 2 crates:
//!
//! -   `ghost-cell`: which provides safe borrow-checking of aliases, with zero runtime overhead.
//! -   `static-rc`: which provides safe reference-counting of aliases, with zero runtime overhead.
//!
//! Additionally, this repository builds upon the `core` and `alloc` crates.
//!
//! The safety of this library depends, entirely, and only, on the safety of those 4 foundational libraries.

//  Generic features.
#![cfg_attr(not(test), no_std)]
#![forbid(unsafe_code)]

//  Lints.
#![deny(missing_docs)]

pub mod linked_list;
pub mod tripod_list;
