//! # Uxn stacks
//! Uxn uses [circular stacks](https://wiki.xxiivv.com/site/uxntal_stacks.html)
//! to hold temporary values.
//!
//! There are two such stacks per machine, called the *working* and *return* stacks.
//! Items can be moved from one to the other using the `STH` operation.
//!
//! Values on the stacks can be read as bytes ([`u8`]) or shorts ([`u16`]) stored as
//! two bytes interpreted in big endian fashion.

use core::{
    fmt::{Debug, Display},
    iter::FusedIterator,
    ops::{Index, IndexMut},
};

/// Circular stack used by the [`UxnMachine`](crate::machine::UxnMachine) to hold 256 bytes of data.
///
/// This interface is provided for implementors who'd want to meddle with said stacks!
///
/// Most methods are provided with alternatives that work on shorts ([`u16`]) instead
/// of bytes ([`u8`]). These are postfixed by `short`, e.g `get` -> `get_short`.
///
/// Indexing is done using signed bytes ([`i8`]). Negative values access elements
/// before the pointer, and vice-versa.
///
/// | **Index** | ... | -2 | -1 | **0** | 1 | 2 | 3 | ... |
/// | ----- | --- | -- | -- | - | - | - | - | --- |
/// | **Value** | ... | 0xf0 | 0x0a | 0xab | 0x00 | 0x10 | 0xaa | ... |
///
/// One can also index on shorts. Shorts can be indexed in an unaligned fashion:
/// <table>
///   <tr>
///     <td>Odd indices</td>
///     <td colspan="2">...</td>
///     <td colspan="2">-1</td>
///     <td colspan="2">1</td>
///     <td colspan="3">...</td>
///   </tr>
///   <tr>
///     <td>Even indices</td>
///     <td colspan="1">...</td>
///     <td colspan="2">-2</td>
///     <td colspan="2">0</td>
///     <td colspan="2">2</td>
///     <td colspan="1">...</td>
///   </tr>
///   <tr>
///     <td>Value</td>
///     <td>...</td>
///     <td>0xf0</td>
///     <td>0x0a</td>
///     <td>0xab</td>
///     <td>0x00</td>
///     <td>0x10</td>
///     <td>0xaa</td>
///     <td>...</td>
///   </tr>
/// </table>

#[derive(Clone, Copy, Eq, PartialEq, Hash, PartialOrd, Ord, Debug)]
pub struct UxnStack {
    pub data: [u8; 0x100],
    pub pointer: u8,
}
impl Default for UxnStack {
    /// Returns an empty [`UxnStack`].
    /// Same as [`UxnStack::new`].
    fn default() -> Self {
        Self::new()
    }
}
impl UxnStack {
    /// Returns an empty `UxnStack`.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// let stack = UxnStack::new();
    /// assert_eq!(stack, [0u8; 0x100])
    /// ```
    pub const fn new() -> Self {
        Self {
            pointer: 0,
            data: [0u8; 0x100],
        }
    }

    /// Returns an iterator over the bytes of this stack, starting at the current
    /// position of the pointer.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let stack = UxnStack::new();
    /// // Checks that all elements of the stack are zero.
    /// assert!(stack.iter().all(|&b| b == 0))
    /// ```
    pub fn iter(&self) -> UxnStackIter<'_> {
        UxnStackIter::new(self)
    }

    /// Returns a mutable iterator over the bytes of this stack, starting at the current
    /// position of the pointer.
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// // Increments all elements of the stack by 1.
    /// stack.iter_mut().for_each(|byte| *byte += 1);
    /// assert!(stack.iter().all(|&b| b == 1))
    /// ```
    pub fn iter_mut(&mut self) -> UxnStackIterMut<'_> {
        UxnStackIterMut::new(self)
    }

    /// Returns the byte at the current pointer location.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push(4);
    /// assert_eq!(stack.top(), 4);
    /// ```
    pub fn top(&self) -> u8 {
        self.data[self.pointer.wrapping_sub(1) as usize]
    }
    /// Returns a mutable reference to the byte at the current pointer location.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push(4);
    /// *stack.top_mut() = 10;
    /// assert_eq!(stack.top(), 10);
    /// ```
    pub fn top_mut(&mut self) -> &mut u8 {
        &mut self.data[self.pointer.wrapping_sub(1) as usize]
    }

    /// Returns the short at the current pointer location.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push_short(0xabcd);
    /// assert_eq!(stack.top_short(), 0xabcd);
    ///
    /// // Two separate bytes pushed can be accessed as one short, so this is equivalent
    /// stack.push(0xab);
    /// stack.push(0xcd);
    ///
    /// assert_eq!(stack.top_short(), 0xabcd);
    /// ```
    pub fn top_short(&self) -> u16 {
        u16::from_be_bytes([self[-1], self[0]])
    }
    /// Sets the value of the short on top of the stack.
    ///
    /// It is not possible to return a mutable reference to said short for easy
    /// in-place manipulation.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push_short(0xabcd);
    /// stack.set_top_short(stack.top_short() + 1);
    /// assert_eq!(stack.top_short(), 0xabce);
    ///
    /// // Two separate bytes pushed can be accessed as one short, so this is equivalent
    /// stack.push(0xab);
    /// stack.push(0xcd);
    /// assert_eq!(stack.top_short(), 0xabcd);
    /// stack.set_top_short(stack.top_short() + 1);
    ///
    /// assert_eq!(stack.top_short(), 0xabce);
    /// ```
    pub fn set_top_short(&mut self, value: u16) {
        let [msb, lsb] = value.to_be_bytes();
        self[-1] = msb;
        self[0] = lsb;
    }

    /// Returns the byte at the given index, offset by the current pointer
    /// location.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push(1);
    /// stack.push(4);
    /// stack.push(10);
    /// stack.pop();
    ///
    /// assert_eq!(stack.get(0), stack.top()); // The top of the stack is at index 0
    /// assert_eq!(stack.get(0), 4);
    /// assert_eq!(stack.get(-1), 1); // Accesses one before the top of the stack
    /// assert_eq!(stack.get(1), 10); // Accesses after the top of the stack
    /// ```
    pub fn get(&self, index: i8) -> u8 {
        self.data[self.pointer.wrapping_add_signed(index).wrapping_sub(1) as usize]
    }

    /// Returns a mutable reference to the byte at the given index, offset by
    /// the current pointer location.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push(1);
    /// stack.push(4);
    /// stack.push(10);
    /// stack.pop();
    ///
    /// *stack.get_mut(-1) = 25;
    /// *stack.get_mut(2) = 30;
    ///
    /// assert_eq!(stack.get(0), 4);
    /// assert_eq!(stack.get(-1), 25); // Accesses one before the top of the stack
    /// assert_eq!(stack.get(1), 10); // Accesses after the top of the stack
    /// assert_eq!(stack.get(2), 30);
    /// ```
    pub fn get_mut(&mut self, index: i8) -> &mut u8 {
        &mut self.data[self.pointer.wrapping_add_signed(index).wrapping_sub(1) as usize]
    }

    /// Returns the short at the given index, offset by the current pointer
    /// location.
    ///
    /// # Example
    /// Shorts are indexed in an unaligned fashion, this example shows the intricacies
    /// to avoid tripping up:
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push_short(0x004a);
    /// stack.push_short(0x1003);
    /// stack.push_short(0xff00);
    /// stack.pop_short();
    ///
    /// // At this point, our stack looks like this, with `|` indicating the position of
    /// // the stack pointer:
    /// // 0x00 0x4a 0x10 0x03 | 0xff 0x00
    /// //  -3   -2   -1   0       1    2
    ///
    /// assert_eq!(stack.get_short(0), stack.top_short()); // The top of the stack is at index 0
    /// assert_eq!(stack.get_short(0), 0x1003);
    /// assert_eq!(stack.get_short(-1), 0x4a10); // We're accessing a short we never pushed, but this is valid!
    /// assert_eq!(stack.get_short(-2), 0x004a); // Accessing pushed shorts is done using even indices
    /// ```
    pub fn get_short(&self, index: i8) -> u16 {
        u16::from_be_bytes([self[index.wrapping_sub(1)], self[index]])
    }

    /// Sets the value of the short at the given index, offset by the current
    /// pointer location.
    ///
    /// It is not possible to return a mutable reference to said short for easy
    /// in-place manipulation.
    ///
    /// Shorts are indexed in an unaligned fashion, see the example in [`UxnStack::get_short`]
    /// to avoid errors.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.set_short(-1, 0x25);
    /// stack.set_short(2, 0x30);
    ///
    /// assert_eq!(stack.get_short(-1), 0x25);
    /// assert_eq!(stack.get_short(2), 0x30);
    /// ```
    pub fn set_short(&mut self, index: i8, value: u16) {
        let [msb, lsb] = value.to_be_bytes();
        self[index.wrapping_sub(1)] = msb;
        self[index] = lsb;
    }

    /// Pushes a byte on top of the stack.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push(3);
    /// assert_eq!(stack.top(), 3);
    /// ```
    pub fn push(&mut self, value: u8) {
        self[1] = value;
        self.pointer = self.pointer.wrapping_add(1);
    }

    /// Pops a byte from the top of the stack.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push(2);
    /// stack.push(3);
    ///
    /// assert_eq!(stack.pop(), 3);
    /// assert_eq!(stack.pop(), 2);
    /// ```
    pub fn pop(&mut self) -> u8 {
        self.pointer = self.pointer.wrapping_sub(1);
        self[1]
    }

    /// Pushes a short on top of the stack.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push_short(0xabcd);
    /// assert_eq!(stack.top_short(), 0xabcd);
    /// ```
    pub fn push_short(&mut self, value: u16) {
        let [msb, lsb] = value.to_be_bytes();
        self[1] = msb;
        self[2] = lsb;
        self.pointer = self.pointer.wrapping_add(2);
    }

    /// Pops a short from the top of the stack.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push_short(0xabcd);
    /// stack.push_short(0xabce);
    ///
    /// assert_eq!(stack.pop_short(), 0xabce);
    /// assert_eq!(stack.pop_short(), 0xabcd);
    /// ```
    pub fn pop_short(&mut self) -> u16 {
        self.pointer = self.pointer.wrapping_sub(2);
        u16::from_be_bytes([self[1], self[2]])
    }

    /// Removes a byte at the given index. This moves all elements above it downwards, equivalent
    /// to popping an element at the given index instead of at the top of the stack.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push(0xab);
    /// stack.push(0xcd);
    ///
    /// assert_eq!(stack.remove(-1), 0xab);
    /// assert_eq!(stack.top(), 0xcd);
    /// ```
    pub fn remove(&mut self, index: i8) -> u8 {
        let value = self.get(index);
        // TODO: this can be optimized
        let mut ptr = self.pointer.wrapping_add_signed(index).wrapping_sub(1);
        loop {
            self.data[ptr as usize] = self.data[ptr.wrapping_add(1) as usize];
            ptr = ptr.wrapping_add(1);
            if ptr == self.pointer {
                break;
            }
        }
        self.pointer = self.pointer.wrapping_sub(1);
        value
    }

    /// Inserts a byte at the given index. This moves all elements above it upwards, equivalent
    /// to pushing an element at the given index instead of at the top of the stack.
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push(0xab);
    /// stack.push(0xcd);
    /// stack.insert(-1, 0x01);
    ///
    /// assert_eq!(stack.get(-1), 0x01);
    /// ```
    pub fn insert(&mut self, index: i8, value: u8) {
        // TODO: this can be optimized
        let mut ptr = self.pointer.wrapping_add_signed(index);
        loop {
            self.data[ptr.wrapping_add(1) as usize] = self.data[ptr as usize];
            ptr = ptr.wrapping_add(1);
            if ptr == self.pointer {
                break;
            }
        }
        self[index.wrapping_add(1)] = value;
        self.pointer = self.pointer.wrapping_add(1);
    }

    /// Removes a short at the given index. This moves all elements above it downwards, equivalent
    /// to popping an element at the given index instead of at the top of the stack.
    ///
    /// Shorts are indexed in an unaligned fashion, see the example in [`UxnStack::get_short`]
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push_short(0xffff);
    /// stack.push(0x01);
    ///
    /// assert_eq!(stack.remove_short(-1), 0xffff);
    /// assert_eq!(stack.top(), 0x01);
    /// ```
    pub fn remove_short(&mut self, index: i8) -> u16 {
        let value = self.get_short(index);
        // TODO: this can be optimized
        let mut ptr = self.pointer.wrapping_add_signed(index).wrapping_sub(2);
        loop {
            self.data[ptr as usize] = self.data[ptr.wrapping_add(2) as usize];
            ptr = ptr.wrapping_add(1);
            if ptr == self.pointer {
                break;
            }
        }
        self.pointer = self.pointer.wrapping_sub(2);
        value
    }

    /// Inserts a short at the given index. This moves all elements above it upwards, equivalent
    /// to pushing an element at the given index instead of at the top of the stack.
    ///
    /// Shorts are indexed in an unaligned fashion, see the example in [`UxnStack::get_short`]
    /// # Example
    /// ```rust
    /// # use baryuxn::stack::UxnStack;
    /// # let mut stack = UxnStack::new();
    /// stack.push(0xab);
    /// stack.push(0xcd);
    ///
    /// stack.insert_short(-1, 0xeeff);
    ///
    /// assert_eq!(stack.get(-1), 0xff);
    /// ```
    pub fn insert_short(&mut self, index: i8, value: u16) {
        // TODO: this can be optimized
        let mut ptr = self.pointer.wrapping_add_signed(index);
        loop {
            self.data[ptr.wrapping_add(2) as usize] = self.data[ptr as usize];
            ptr = ptr.wrapping_add(1);
            if ptr == self.pointer {
                break;
            }
        }
        self.set_short(index.wrapping_add(2), value);
        self.pointer = self.pointer.wrapping_add(2);
    }
}
impl Index<i8> for UxnStack {
    type Output = u8;

    /// Returns a reference to the byte stored at the given index in the stack.
    fn index(&self, index: i8) -> &Self::Output {
        &self.data[self.pointer.wrapping_add_signed(index).wrapping_sub(1) as usize]
    }
}
impl IndexMut<i8> for UxnStack {
    /// Returns a mutable reference to the byte stored at the given index in the stack.
    fn index_mut(&mut self, index: i8) -> &mut Self::Output {
        self.get_mut(index)
    }
}
impl PartialEq<[u8; 0x100]> for UxnStack {
    /// Partial equality between the elements stored in this stack and an array
    /// of 256 bytes.
    ///
    /// This does not care about current top of the stack location.
    fn eq(&self, other: &[u8; 0x100]) -> bool {
        &self.data == other
    }
}
impl Display for UxnStack {
    /// Pretty printing for Uxn stacks.
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for i in -7..=1 {
            write!(f, "{:#04x}{} ", self.get(i), if i == 0 { "|" } else { "" })?
        }
        Ok(())
    }
}

/// Iterator over the values of a [`UxnStack`], starting from the current stack pointer
/// and going back up the stack until it loops.
/// # Example
/// ```rust
/// # use baryuxn::stack::UxnStack;
/// let mut stack = UxnStack::new();
///
/// // Checks that all elements of the stack are zero.
/// assert!(stack.iter().all(|&b| b == 0))
/// ```
pub struct UxnStackIter<'a> {
    left: &'a [u8],
    right: &'a [u8],
}
impl<'a> UxnStackIter<'a> {
    pub fn new(stack: &'a UxnStack) -> Self {
        let (left, right) = stack.data.split_at(stack.pointer as usize);
        Self { left, right }
    }
}
impl<'a> Iterator for UxnStackIter<'a> {
    type Item = &'a u8;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((last, rest)) = self.left.split_last() {
            self.left = rest;
            Some(last)
        } else if let Some((last, rest)) = self.right.split_last() {
            self.right = rest;
            Some(last)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (256, Some(256))
    }
}
impl DoubleEndedIterator for UxnStackIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some((first, rest)) = self.right.split_first() {
            self.right = rest;
            Some(first)
        } else if let Some((first, rest)) = self.left.split_first() {
            self.left = rest;
            Some(first)
        } else {
            None
        }
    }
}
impl ExactSizeIterator for UxnStackIter<'_> {
    fn len(&self) -> usize {
        256
    }
}
impl FusedIterator for UxnStackIter<'_> {}

/// Iterator over the values of a [`UxnStack`], starting from the current stack pointer
/// and going back up the stack until it loops. Elements can be modified individually.
/// # Example
/// ```rust
/// # use baryuxn::stack::UxnStack;
/// let mut stack = UxnStack::new();
///
/// // Increments all elements of the stack by 1.
/// stack.iter_mut().for_each(|byte| *byte += 1);
/// assert!(stack.iter().all(|&b| b == 1))
/// ```
pub struct UxnStackIterMut<'a> {
    left: &'a mut [u8],
    right: &'a mut [u8],
}
impl<'a> UxnStackIterMut<'a> {
    pub fn new(stack: &'a mut UxnStack) -> Self {
        let (left, right) = stack.data.split_at_mut(stack.pointer as usize);
        Self { left, right }
    }
}
impl<'a> Iterator for UxnStackIterMut<'a> {
    type Item = &'a mut u8;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((last, rest)) = core::mem::take(&mut self.left).split_last_mut() {
            self.left = rest;
            Some(last)
        } else if let Some((last, rest)) = core::mem::take(&mut self.right).split_last_mut() {
            self.right = rest;
            Some(last)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (256, Some(256))
    }
}
impl DoubleEndedIterator for UxnStackIterMut<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some((first, rest)) = core::mem::take(&mut self.right).split_first_mut() {
            self.right = rest;
            Some(first)
        } else if let Some((first, rest)) = core::mem::take(&mut self.left).split_first_mut() {
            self.left = rest;
            Some(first)
        } else {
            None
        }
    }
}
impl ExactSizeIterator for UxnStackIterMut<'_> {
    fn len(&self) -> usize {
        256
    }
}
impl FusedIterator for UxnStackIterMut<'_> {}
