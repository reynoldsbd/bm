//! Simple bitmaps for Rust
//!
//! Bitmaps are arrays of boolean values where each value is represented in memory by a single
//! bit. Because of their relative memory-efficiency and simple semantics, they are a popular choice
//! in embedded or memory-constrained contexts.
//!
//! The [`Bitmap`](::Bitmap) trait defines core bitmap operations and is implemented for some common
//! types. [`AtomicBitmap`](::AtomicBitmap) supplements `Bitmap` by defining a thread-safe (i.e.
//! `Sync`-compatible) bitmap API.


#![cfg_attr(not(test), no_std)]

#[cfg(test)]
extern crate core;

use core::{
    mem,
    sync::atomic::{
        AtomicUsize,
        Ordering,
    },
};


/// An array of boolean values
///
/// This trait defines the core API of a bitmap. In essence, bitmaps are arrays of `bool`. `Bitmap`
/// methods allow you to interact with that array by getting or setting individual bits or querying
/// the overall length of the array.
pub trait Bitmap {

    /// Gets the number of bits in this bitmap
    ///
    /// # Examples
    ///
    /// ```
    /// use bm::Bitmap;
    ///
    /// let bitmap = 0u8;
    ///
    /// assert_eq!(8, bitmap.bit_count());
    /// ```
    fn bit_count(&self) -> usize;

    /// Gets the value of the specified bit.
    ///
    /// # Panics
    ///
    /// Panics if `index >= self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bm::Bitmap;
    ///
    /// let bitmap = 0u8;
    ///
    /// assert_eq!(false, bitmap.get_bit(0));
    /// ```
    fn get_bit(&self, index: usize) -> bool;

    /// Sets the value of the specified bit.
    ///
    /// # Panics
    ///
    /// Panics if `index >= self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bm::Bitmap;
    ///
    /// let mut bitmap = 0u8;
    /// bitmap.set_bit(3, true);
    ///
    /// assert_eq!(true, bitmap.get_bit(3));
    /// ```
    fn set_bit(&mut self, index: usize, value: bool);
}

impl Bitmap for u8 {
    fn bit_count(&self) -> usize { 8 }

    fn get_bit(&self, index: usize) -> bool { 1 == 1 & (*self >> index) }

    fn set_bit(&mut self, index: usize, value: bool) {
        *self = match value {
            true => *self | (1 << index),
            false => *self & !(1 << index),
        }
    }
}

impl Bitmap for usize {
    fn bit_count(&self) -> usize { mem::size_of::<usize>() }

    fn get_bit(&self, index: usize) -> bool { 1 == 1 & (*self >> index) }

    fn set_bit(&mut self, index: usize, value: bool) {
        *self = match value {
            true => *self | (1 << index),
            false => *self & !(1 << index),
        }
    }
}

impl Bitmap for AtomicUsize {
    fn bit_count(&self) -> usize { 8 * mem::size_of::<AtomicUsize>() }

    fn get_bit(&self, index: usize) -> bool {
        self.load_bit(index, Ordering::Acquire)
    }

    fn set_bit(&mut self, index: usize, value: bool) {
        let cell = self.get_mut();
        *cell = match value {
            true => *cell | (1 << index),
            false => *cell & !(1 << index),
        };
    }
}

/// A slice of any type that implements `Bitmap` and [`BitmapCell`](::BitmapCell) may be treated as
/// one big bitmap.
impl<T: Bitmap + BitmapCell> Bitmap for [T] {
    fn bit_count(&self) -> usize { self.len() * T::capacity() }

    fn get_bit(&self, index: usize) -> bool {
        self[index / T::capacity()].get_bit(index % T::capacity())
    }

    fn set_bit(&mut self, index: usize, value: bool) {
        self[index / T::capacity()].set_bit(index % T::capacity(), value);
    }
}


/// Slice of this type may be treated as a single bitmap
///
/// To allow slices of `Bitmap` types to be treated as one giant `Bitmap` in an efficient manner,
/// each instance of that type must have *the same* length. This requirement is expressed by the
/// `BitmapCell` trait, and `Bitmap` is only implemented for slices of `T` where `T: BitmapCell`.
pub trait BitmapCell {

    /// Fixed length of this type
    fn capacity() -> usize;
}

impl BitmapCell for u8 {
    fn capacity() -> usize { 8 * mem::size_of::<u8>() }
}

impl BitmapCell for usize {
    fn capacity() -> usize { 8 * mem::size_of::<usize>() }
}

impl BitmapCell for AtomicUsize {
    fn capacity() -> usize { 8 * mem::size_of::<AtomicUsize>() }
}


/// Atomic variant of `Bitmap`
///
/// This trait supplements [`Bitmap`](::Bitmap) by providing an API for concurrent bitmap access. In
/// other words, `AtomicBitmap` methods can be easily implemented for thread-safe `Sync` types.
///
/// This crate provides an implementation of `AtomicBitmap` for
/// [`AtomicUsize`](core::sync::atomic::AtomicUsize) that is *lock-free*.
pub trait AtomicBitmap: Bitmap {

    /// Atomically retrieves the value of the specified bit.
    ///
    /// `order` specifies the memory ordering of this operation.
    ///
    /// # Panics
    ///
    /// Panics if `index > self.len()` or if `order` is `Release` or `AcqRel`.
    fn load_bit(&self, index: usize, order: Ordering) -> bool;

    /// Stores a value into the specified bit if its current value is the same as `current`.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was updated. `order` specifies the memory ordering of this operation.
    ///
    /// # Panics
    ///
    /// Panics if `index > self.len()`.
    fn compare_and_swap(&self, index: usize, current: bool, new: bool, order: Ordering) -> bool;
}

/// Lock-free implementation for `AtomicUsize`.
impl AtomicBitmap for AtomicUsize {
    fn load_bit(&self, index: usize, order: Ordering) -> bool {
        assert!(index < 8 * mem::size_of::<AtomicUsize>());
        1 == 1 & (self.load(order) >> index)
    }

    fn compare_and_swap(&self, index: usize, current: bool, new: bool, order: Ordering) -> bool {
        assert!(index < 8 * mem::size_of::<AtomicUsize>());
        // This cell stores multiple bits, but we can only compare/swap on the whole cell at once,
        // so it's possible for compare/swap to fail because a different bit in the cell has been
        // modified by another thread. In such a case, continue trying to compare/swap until either
        // we are successful or another thread modifies the specified bit before we do.
        loop {
            // Load the current cell value, and stop early if the bit we're trying to set has
            // already been changed on another thread
            let cur_cell_val = self.load(Ordering::Acquire);
            let cur_val = 1 == 1 & (cur_cell_val >> index);
            if cur_val != current {
                return cur_val;
            }

            // Decide what the new cell value should be after setting/unsetting the specified bit
            let new_cell_val = match new {
                true => cur_cell_val | (1 << index),
                false => cur_cell_val & !(1 << index),
            };

            // Try to swap in the new cell value. If successful, we can signal success. Otherwise,
            // check whether the failure was because the targeted bit was flipped by another thread.
            // If so, then stop early and indicate failure. Otherwise, try again.
            let old_cell_val = self.compare_and_swap(cur_cell_val, new_cell_val, order);
            if old_cell_val == cur_cell_val {
                return current;
            }
        }
    }
}

impl<T: AtomicBitmap + BitmapCell> AtomicBitmap for [T] {
    fn load_bit(&self, index: usize, order: Ordering) -> bool {
        self[index / T::capacity()].load_bit(index % T::capacity(), order)
    }

    fn compare_and_swap(&self, index: usize, current: bool, new: bool, order: Ordering) -> bool {
        self[index / T::capacity()].compare_and_swap(index % T::capacity(), current, new, order)
    }
}


#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::thread;
    use super::*;

    #[test]
    fn bit_count_for_u8() {
        assert_eq!(8, 0u8.bit_count());
    }

    #[test]
    fn bit_count_for_usize() {
        assert_eq!(mem::size_of::<usize>(), 0usize.bit_count());
    }

    #[test]
    fn bit_count_for_atomic_usize() {
        assert_eq!(8 * mem::size_of::<AtomicUsize>(), AtomicUsize::new(0).bit_count());
    }

    #[test]
    fn bit_count_for_u8_slice() {
        let bm = &[0u8; 10][..];

        assert_eq!(80, bm.bit_count());
    }

    #[test]
    fn bit_count_for_usize_slice() {
        let bm = &[0usize; 10][..];

        assert_eq!(8 * mem::size_of::<usize>() * 10, bm.bit_count());
    }

    #[test]
    fn bit_count_for_atomic_usize_slice() {
        let bm: [AtomicUsize; 10] = Default::default();
        let bm = &bm[..];

        assert_eq!(8 * mem::size_of::<AtomicUsize>() * 10, bm.bit_count());
    }

    #[test]
    fn get_bit_for_u8() {
        let bm = 0xf0u8;

        for i in 0..4 {
            assert_eq!(false, bm.get_bit(i));
        }
        for i in 4..8 {
            assert_eq!(true, bm.get_bit(i));
        }
    }

    #[test]
    fn get_bit_for_usize() {
        let bm = 0xff00usize;

        for i in 0..8 {
            assert_eq!(false, bm.get_bit(i));
        }
        for i in 8..16 {
            assert_eq!(true, bm.get_bit(i));
        }
        for i in 16..bm.bit_count() {
            assert_eq!(false, bm.get_bit(i));
        }
    }

    #[test]
    fn get_bit_for_atomic_usize() {
        let bm = AtomicUsize::new(0xff00);

        for i in 0..8 {
            assert_eq!(false, bm.get_bit(i));
        }
        for i in 8..16 {
            assert_eq!(true, bm.get_bit(i));
        }
        for i in 16..bm.bit_count() {
            assert_eq!(false, bm.get_bit(i));
        }
    }

    #[test]
    fn get_bit_for_u8_slice() {
        let bm = &[0xaa_u8; 10][..];

        for i in 0..bm.bit_count() {
            if i % 2 == 0 {
                assert_eq!(false, bm.get_bit(i));
            } else {
                assert_eq!(true, bm.get_bit(i));
            }
        }
    }

    #[test]
    fn get_bit_for_usize_slice() {
        let bm = &[0xaaaa_aaaa_aaaa_aaaa_usize; 10][..];

        for i in 0..bm.bit_count() {
            if i % 2 == 0 {
                assert_eq!(false, bm.get_bit(i));
            } else {
                assert_eq!(true, bm.get_bit(i));
            }
        }
    }

    #[test]
    fn get_bit_for_atomic_usize_slice() {
        let bm: [AtomicUsize; 10] = Default::default();
        let bm = &bm[..];

        for i in 0..bm.bit_count() {
            assert_eq!(false, bm.get_bit(i));
        }
    }

    #[test]
    fn set_bit_for_u8() {
        let mut bm = 0u8;

        bm.set_bit(0, true);
        bm.set_bit(1, true);

        assert_eq!(true, bm.get_bit(0));
        assert_eq!(true, bm.get_bit(1));
        for i in 2..bm.bit_count() {
            assert_eq!(false, bm.get_bit(i));
        }
        assert_eq!(3, bm);

        bm.set_bit(0, false);
        bm.set_bit(1, false);

        assert_eq!(false, bm.get_bit(0));
        assert_eq!(false, bm.get_bit(1));
        for i in 2..bm.bit_count() {
            assert_eq!(false, bm.get_bit(i));
        }
        assert_eq!(0, bm);
    }

    #[test]
    fn set_bit_for_usize() {
        let mut bm = 0usize;

        bm.set_bit(0, true);
        bm.set_bit(1, true);

        assert_eq!(true, bm.get_bit(0));
        assert_eq!(true, bm.get_bit(1));
        for i in 2..bm.bit_count() {
            assert_eq!(false, bm.get_bit(i));
        }
        assert_eq!(3, bm);

        bm.set_bit(0, false);
        bm.set_bit(1, false);

        assert_eq!(false, bm.get_bit(0));
        assert_eq!(false, bm.get_bit(1));
        for i in 2..bm.bit_count() {
            assert_eq!(false, bm.get_bit(i));
        }
        assert_eq!(0, bm);
    }

    #[test]
    fn set_bit_for_atomic_usize() {
        let mut bm = AtomicUsize::new(0);

        bm.set_bit(0, true);
        bm.set_bit(1, true);

        assert_eq!(true, bm.get_bit(0));
        assert_eq!(true, bm.get_bit(1));
        for i in 2..bm.bit_count() {
            assert_eq!(false, bm.get_bit(i));
        }
        assert_eq!(3, bm.load(Ordering::Acquire));

        bm.set_bit(0, false);
        bm.set_bit(1, false);

        assert_eq!(false, bm.get_bit(0));
        assert_eq!(false, bm.get_bit(1));
        for i in 2..bm.bit_count() {
            assert_eq!(false, bm.get_bit(i));
        }
        assert_eq!(0, bm.load(Ordering::Acquire));
    }

    #[test]
    fn set_bit_for_u8_slice() {
        let bm = &mut [0u8; 10][..];

        for i in 0..bm.bit_count() {
            bm.set_bit(i, true);
        }

        for i in 0..bm.bit_count() {
            assert_eq!(true, bm.get_bit(i));
        }

        for i in 0..bm.bit_count() {
            bm.set_bit(i, false);
        }

        for i in 0..bm.bit_count() {
            assert_eq!(false, bm.get_bit(i));
        }
    }

    #[test]
    fn set_bit_for_usize_slice() {
        let bm = &mut [0usize; 10][..];

        for i in 0..bm.bit_count() {
            bm.set_bit(i, true);
        }

        for i in 0..bm.bit_count() {
            assert_eq!(true, bm.get_bit(i));
        }

        for i in 0..bm.bit_count() {
            bm.set_bit(i, false);
        }

        for i in 0..bm.bit_count() {
            assert_eq!(false, bm.get_bit(i));
        }
    }

    #[test]
    fn set_bit_for_atomic_usize_slice() {
        let mut bm: [AtomicUsize; 10] = Default::default();
        let bm = &mut bm[..];

        for i in 0..bm.bit_count() {
            bm.set_bit(i, true);
        }

        for i in 0..bm.bit_count() {
            assert_eq!(true, bm.get_bit(i));
        }

        for i in 0..bm.bit_count() {
            bm.set_bit(i, false);
        }

        for i in 0..bm.bit_count() {
            assert_eq!(false, bm.get_bit(i));
        }
    }

    #[test]
    fn load_bit_for_atomic_usize() {
        let bm = AtomicUsize::new(0xFF00);

        for i in 0..8 {
            assert_eq!(false, bm.load_bit(i, Ordering::Acquire));
        }
        for i in 8..16 {
            assert_eq!(true, bm.load_bit(i, Ordering::Acquire));
        }
        for i in 16..bm.bit_count() {
            assert_eq!(false, bm.load_bit(i, Ordering::Acquire));
        }
    }

    #[test]
    fn load_bit_for_atomic_usize_slice() {
        let bm: [AtomicUsize; 10] = Default::default();
        let bm = &bm[..];

        for i in 0..bm.bit_count() {
            assert_eq!(false, bm.load_bit(i, Ordering::Acquire));
        }
    }

    #[test]
    fn compare_and_swap_for_atomic_usize() {
        let bm = Arc::new(AtomicUsize::new(0));

        let handles = (0..bm.bit_count())
            .map(|i| {
                let bm = Arc::clone(&bm);
                thread::spawn(move || {
                    let res = AtomicBitmap::compare_and_swap(&*bm, i, false, true, Ordering::Release);
                    assert_eq!(false, res);
                })
            });
        for handle in handles {
            handle.join().unwrap();
        }

        for i in 0..bm.bit_count() {
            assert_eq!(true, bm.load_bit(i, Ordering::Acquire));
        }
    }

    #[test]
    fn compare_and_swap_for_atomic_usize_slice() {
        let bm: Arc<[AtomicUsize; 10]> = Default::default();
        let bm = bm as Arc<[AtomicUsize]>;

        let handles = (0..bm.bit_count())
            .map(|i| {
                let bm = Arc::clone(&bm);
                thread::spawn(move || {
                    let res = AtomicBitmap::compare_and_swap(&*bm, i, false, true, Ordering::Release);
                    assert_eq!(false, res);
                })
            });
        for handle in handles {
            handle.join().unwrap();
        }

        for i in 0..bm.bit_count() {
            assert_eq!(true, bm.load_bit(i, Ordering::Acquire));
        }
    }
}
