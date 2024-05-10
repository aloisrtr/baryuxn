//! # BaryUxn: the baremetal Uxn stack machine
//! An implementation of the [Uxn stack machine](https://wiki.xxiivv.com/site/uxn.html)
//! designed to not rely on `std`.
//!
//! This means it can run on baremetal, and is thoroughly adaptable to any plateform.
//!
//! The source is also designed to be as readable as possible, while compiling
//! down to efficient code regardless of the target plateform.

pub mod bus;
pub mod machine;
pub mod stack;

#[cfg(test)]
mod test;
