//! A simple bitmap for Rust
//!
//! Bitmaps are logical arrays of boolean values. Traditionally, each value is represented as an
//! individual bit in memory, allowing many entries to be stored in a relatively small amount of
//! space. This crate provides a trait to support most common bitmap operations, as well as an
//! implementation of that trait for `&[u8]`. This allows you to treat any slice of bytes as a
//! bitmap.


#![no_std]


/// A type tht can act as a bitmap
///
/// A bitmap is, logically, an array of boolean values. Traditionally, these values are represented
/// as individual bits in memory, allowing a many entries to be stored in a relatively small amount
/// of space.
pub trait Bitmap {

    /// Sets the first unset bit and returns its index
    fn alloc_bit(&mut self) -> Option<usize> {
        for i in 0..self.num_bits() {
            if !self.get_bit(i) {
                self.set_bit(i, true);
                return Some(i);
            }
        }

        None
    }

    /// Gets the value of the specified bit
    fn get_bit(&self, index: usize) -> bool;

    /// Gets the length of this bitmap
    fn num_bits(&self) -> usize;

    /// Returns the number of set bits
    fn num_set_bits(&self) -> usize {
        let mut num = 0;
        for i in 0..self.num_bits() {
            if self.get_bit(i) {
                num += 1;
            }
        }

        num
    }

    /// Sets the value of all bits
    fn set_all_bits(&mut self, value: bool) {
        for i in 0..self.num_bits() {
            self.set_bit(i, value);
        }
    }

    /// Sets the value of the specified bit
    fn set_bit(&mut self, index: usize, value: bool);
}

impl Bitmap for [u8] {
    fn get_bit(&self, index: usize) -> bool {
        let byte = index >> 3;
        let bit = index & 0x07;

        if byte >= self.len() {
            panic!("Bitmap index out of range");
        }

        1 == 0x01 & (self[byte] >> bit)
    }

    fn num_bits(&self) -> usize {
        self.len() * 8
    }

    fn set_bit(&mut self, index: usize, value: bool) {
        let byte = index >> 3;
        let bit = (index & 0x07) as u32;

        if byte >= self.len() {
            panic!("Bitmap index out of range");
        }

        if value {
            self[byte] |= 1 << bit;
        } else {
            self[byte] &= 0x7fu8.rotate_left(bit);
        }
    }
}
