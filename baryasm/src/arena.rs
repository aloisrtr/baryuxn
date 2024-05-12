//! # Arena allocator
//! Allows allocating chunks of memory up to a certain compile-time set size
//! constraint.
//!
//! For now, this implementation is heavily toned down feature-wise. We only need
//! to save data, not deallocate, reallocate, or anything fancy like that.
//!
//! The API looks similar to that of the [`allocator_api`]() nightly feature, and
//! will comply to it fully once said feature gets stabilized.

use core::{marker::PhantomData, ptr::NonNull};

#[derive(Clone, Debug)]
pub(crate) struct ArenaAllocator<'this, const BYTES: usize> {
    storage: [u8; BYTES],
    free: NonNull<u8>,
    registration_start: Option<NonNull<u8>>,
    _marker: PhantomData<&'this ()>,
}
impl<'this, const BYTES: usize> Default for ArenaAllocator<'this, BYTES> {
    fn default() -> Self {
        let mut arena = Self {
            storage: [0; BYTES],
            free: NonNull::dangling(),
            registration_start: None,
            _marker: PhantomData,
        };
        arena.free = NonNull::new(arena.storage.as_mut_ptr()).unwrap();
        arena
    }
}
impl<'this, const BYTES: usize> ArenaAllocator<'this, BYTES> {
    pub fn start_registering(&mut self) {
        self.registration_start = Some(self.free);
    }

    pub fn register(&mut self, byte: u8) {
        unsafe {
            *self.free.as_mut() = byte;
            self.free = NonNull::new(self.free.as_ptr().add(1)).unwrap()
        }
    }

    pub fn end_registering(&mut self) -> Option<&'this [u8]> {
        if let Some(start) = self.registration_start {
            unsafe {
                let size = self.free.as_ptr().offset_from(start.as_ptr());
                assert!(size >= 0, "size was {size}");
                Some(core::slice::from_raw_parts(start.as_ptr(), size as usize))
            }
        } else {
            return None;
        }
    }
}
