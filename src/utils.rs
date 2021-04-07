
#[cfg(feature = "compile-time-ratio")]
macro_rules! AssertEqType {
    ($n:expr, $m: expr) => {
        ([(); $n - $m], [(); $m - $n])
    };
}

#[cfg(not(feature = "compile-time-ratio"))]
macro_rules! AssertEqType {
    ($n: expr, $m: expr) => {
        ()
    };
}
