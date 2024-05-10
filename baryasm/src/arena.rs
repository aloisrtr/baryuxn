//! # Arena allocator
//! Allows allocating chunks of memory up to a certain compile-time set size
//! constraint.
//!
//! For now, this implementation is heavily toned down feature-wise. We only need
//! to save data, not deallocate, reallocate, or anything fancy like that.
//!
//! The API looks similar to that of the [`allocator_api`]() nightly feature, and
//! will comply to it fully once said feature gets stabilized.

use core::{alloc::Layout, ptr::NonNull};

#[derive(Clone, Debug)]
pub(crate) struct ArenaAllocator<const BYTES: usize> {
    storage: [u8; BYTES],
    free: NonNull<u8>,
}
impl<const BYTES: usize> Default for ArenaAllocator<BYTES> {
    fn default() -> Self {
        let mut arena = Self {
            storage: [0; BYTES],
            free: NonNull::dangling(),
        };
        arena.free = NonNull::new(arena.storage.as_mut_ptr()).unwrap();
        arena
    }
}
impl<const BYTES: usize> ArenaAllocator<BYTES> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn allocate(&self, layout: Layout) -> Result<&mut [u8], ()> {
        let size = layout.size();
        let left = unsafe { self.free.as_ptr().offset_from(self.storage.as_ptr()) };
        if size < left.abs() as usize {
            // No space left
            return Err(());
        }

        Ok(unsafe { core::slice::from_raw_parts_mut(self.free.as_ptr(), size) })
    }
}
