//! # Uxn stack machine
//! Represents a fully functional [Uxn stack-machine](https://wiki.xxiivv.com/site/uxn.html).
//!
//! Execution of code is done using the [`UxnVector`] abstraction. It is an iterator
//! requiring a starting address. It then runs until encountering a `BRK` instruction.
//! Using iterators eases up the interaction.
//! ```ignore
//! # use baryuxn::machine::*;
//! # let mut machine = UxnMachineState::new();
//! for pc in UxnVector::new(0x100, &mut machine, &mut memory, &mut devices) {
//!     println!("{pc}");
//! }
//! ```

use crate::stack::UxnStack;

/// The Uxn machine, able to execute [Uxntal instructions](https://wiki.xxiivv.com/site/uxntal_opcodes.html).
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash, Default)]
pub struct UxnMachineState {
    pub work_stack: UxnStack,
    pub return_stack: UxnStack,
}
impl UxnMachineState {
    /// Creates a new [`UxnMachine`] with empty stacks.
    pub fn new() -> Self {
        Self::default()
    }
}
