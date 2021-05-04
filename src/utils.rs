/// A work-around arithmetic conditions in `where` clauses.

#[cfg(feature = "compile-time-ratio")]
macro_rules! AssertLeType {
    ($left:expr, $right:expr) => {
        [(); $right - $left]
    };
}

#[cfg(not(feature = "compile-time-ratio"))]
macro_rules! AssertLeType {
    ($left:expr, $right:expr) => {
        ()
    };
}

macro_rules! AssertEqType {
    ($left:expr, $right: expr) => {
        (AssertLeType!($left, $right), AssertLeType!($right, $left))
    };
}
