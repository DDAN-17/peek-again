A performant iterator providing double peek functionality.

This crate provides a [`Peekable`](https://docs.rs/peek_again/latest/peek_again/struct.Peekable.html) 
iterator adapter that allows looking ahead by up to two elements without advancing the 
iterator. It maintains performance parity with [`core::iter::Peekable`](https://doc.rust-lang.org/core/iter/struct.Peekable.html) 
for single peek operations, with only a minimal 90 picosecond overhead for double peek operations.

# Key Features

- **Double Peek**: Look ahead by up to two elements while maintaining iterator position.
- **Performance**: Single peek operations are as fast or faster than `core::iter::Peekable`.
- **Greater Control**: Enhanced functionality for conditional iteration and element consumption.

# Basic Usage

```rust
use peek_again::Peekable;

let mut iter = Peekable::new([1, 2, 3].into_iter());

assert_eq!(iter.peek().get(), Some(&1));  // Look at next element
assert_eq!(iter.peek_2(), Some(&2));      // Look two elements ahead
assert_eq!(iter.next(), Some(1));         // Iterator position unchanged
```

# Enhanced Peek Control

The [`Peek`](https://docs.rs/peek_again/latest/peek_again/struct.Peek.html) type returned by 
[`peek`](https://docs.rs/peek_again/latest/peek_again/struct.Peekable.html#method.peek) provides 
additional control over iteration:

```rust
# use peek_again::Peekable;
let mut iter = Peekable::new([1, 2, 3].into_iter());
let mut peek = iter.peek();

// Examine current and next elements
assert_eq!(peek, Some(&1));
assert_eq!(peek.peek(), Some(&2));

// Conditionally consume elements (moving the iterator forward)
if peek == Some(&1) {
    assert_eq!(peek.consume(), Some(1));
}
```

# Conditional Draining

The [`drain_if`](https://docs.rs/peek_again/latest/peek_again/struct.Peek.html#method.drain_if) method 
allows consuming multiple elements based on lookahead:

```rust
# use peek_again::Peekable;
let mut iter = Peekable::new([1, 2, 3].into_iter());
let peek = iter.peek();

peek.drain_if(|&next| next == 2)
    .map_or_else(
        |_peek| unreachable!("The second element is two."),
        |(curr, next)| {
            assert_eq!(curr, Some(1));
            assert_eq!(next, 2);
        }
    );
```

# Performance Considerations

- Single peek operations (`peek()`) are optimized to match or exceed the performance of
  `core::iter::Peekable`.
- Double peek operations (`peek_2()`) incur only a 90 picosecond overhead compared to
  single peek operations.
- State transitions and element storage are designed to minimize memory operations.

# Safety

This crate is marked with `#![forbid(unsafe_code)]` and employs design by contract 
principles, making the property tests far more meaningful.

