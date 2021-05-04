#![cfg_attr(not(test), no_std)]

pub use ghost_cell as cell;
#[cfg(feature = "collections")]
pub use ghost_collections as collections;
pub use static_rc as rc;
