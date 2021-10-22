This crate strives to provide a fast implementation of `Decimal` fixed-point 
arithmetics.

It is targeted at typical business applications, dealing with numbers 
representing quantities, money and the like, not at scientific computations,
for which the accuracy of floating point math is - in most cases - sufficient.

### Objectives

* "Exact" representation of decimal numbers (no deviation as with binary
  floating point numbers)
* No hidden rounding errors (as inherent to floating point math)
* Very fast operations (by mapping them to integer ops) 
* Range of representable decimal numbers sufficient for typical business
  applications

At the binary level a Decimal number is represented as a coefficient (stored 
as an `i128` value) combined with a type parameter specifying the number of 
fractional decimal digits. I. e., the whole implementation is based on "const 
generics" and needs a rust version supporting this feature.

### Status

Experimental (work in progess)

## Getting started

Add `rust-fixed-point-decimal` to your `Cargo.toml`:

```toml
[dependencies]
rust-fixed-point-decimal = "0.1"
```

### Note:

Because the implementation of "const generics" is still incomplete, you have 
to put the following at the start of your main.rs or lib.rs file:

```rust
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
```

## Usage

A `Decimal` number can be created in different ways. 

The easiest method is to use the procedural macro `Dec`:

```rust
# use rust_fixed_point_decimal::Dec;
let d = Dec!(-17.5);
assert_eq!(d.to_string(), "-17.5");
```

Alternatively you can convert an integer or a string to a `Decimal`:

```rust
# #![allow(incomplete_features)]
# #![feature(generic_const_exprs)]
# use rust_fixed_point_decimal::{Decimal, ParseDecimalError};
# use std::str::FromStr;
let d = Decimal::<2>::from(297_i32);
assert_eq!(d.to_string(), "297.00");

let d = Decimal::<4>::from_str("38.207")?;
assert_eq!(d.to_string(), "38.2070");
# Ok::<(), ParseDecimalError>(())
```
