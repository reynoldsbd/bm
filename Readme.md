# bm

`bm` provides simple bitmaps for Rust.

# Quick start

Add `bm` to *Cargo.toml*:

```toml
[dependencies]
bm = { git = "https://github.com/reynoldsbd/bm" }
```

*(`bm` does not depend on `std` or any other crate)*

The `Bitmap` trait is implemented for several types and slice-types. For instance, you can treat any
byte-slice as a bitmap just by importing `Bitmap`:

```rust
use bm::Bitmap;
let mut bitmap = &[0u8; 10][..];

// Check how many bits are available
assert_eq!(80, bitmap.bit_count());

// Retrieve the value of bit 0
assert_eq!(false, bitmap.get_bit(0));

// Set the value of bit 5
bitmap.set_bit(5, true);
assert_eq!(true, bitmap.get_bit(5));
```

The `AtomicBitmap` trait defines a `Sync`-friendly bitmap API, and this crate provides a lock-free
implementation of `AtomicBitmap` for `AtomicUsize` and slices thereof:

```rust
use bm::AtomicBitmap;
use std::sync::atomic::{ AtomicUsize, Ordering };
let bitmap = AtomicUsize::new(0); // No mut needed!

// Atomically load the value of a bit
assert_eq!(false, bitmap.load_bit(0, Ordering::Acquire));

// Atomically set the value of the bit
if !bitmap.compare_and_swap(5, false, true, Ordering::Release) {
    // Return value was the same as the `current` parameter, meaning the swap was successful
    assert_eq!(true, bitmap.load_bit(5));
} else {
    // Failed to swap; `current` was not correct value
    println!("Oh no!");
}
```
