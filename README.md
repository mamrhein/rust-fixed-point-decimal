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

Alternatively you can convert an integer, a float or a string to a `Decimal`:

```rust
# use rust_fixed_point_decimal::Decimal;
let d = Decimal::<2>::from(297_i32);
assert_eq!(d.to_string(), "297.00");
```

```rust
# #![allow(incomplete_features)]
# #![feature(generic_const_exprs)]
# use rust_fixed_point_decimal::{Decimal, DecimalError};
# use std::convert::TryFrom;
let d = Decimal::<5>::try_from(83.0025)?;
assert_eq!(d.to_string(), "83.00250");
# Ok::<(), DecimalError>(())
```

```rust
# #![allow(incomplete_features)]
# #![feature(generic_const_exprs)]
# use rust_fixed_point_decimal::{Decimal, ParseDecimalError};
# use std::str::FromStr;
let d = Decimal::<4>::from_str("38.207")?;
assert_eq!(d.to_string(), "38.2070");
# Ok::<(), ParseDecimalError>(())
```

The sign of a `Decimal` can be inverted using the unary minus operator and a
`Decimal` instance can be compared to other instances of type `Decimal` or all
basic types of integers (besides u128 and atm besides u8, which causes a 
compiler error):

```rust
# #![allow(incomplete_features)]
# #![feature(generic_const_exprs)]
# use rust_fixed_point_decimal::{Dec, Decimal};
let x = Dec!(129.24);
let y = -x;
assert_eq!(y.to_string(), "-129.24");
assert!(-129_i64 > y);
let z = -y;
assert_eq!(x, z);
let z = Dec!(0.00097);
assert!(x > z);
assert!(y <= z);
assert!(z != 7_u32);
assert!(7_u32 == Dec!(7.00));
```

`Decimal` supports all five binary numerical operators +, -, *, /, and %, with
two `Decimal`s or with a `Decimal` and a basic integer (besides u128):

```rust
# #![allow(incomplete_features)]
# #![feature(generic_const_exprs)]
# use rust_fixed_point_decimal::{Dec, Decimal};
let x = Dec!(17.5);
let y = Dec!(6.40);
let z = x + y;
assert_eq!(z.to_string(), "23.90");
let z = x - y;
assert_eq!(z.to_string(), "11.10");
let z = x * y;
assert_eq!(z.to_string(), "112.000");
let z = x / y;
assert_eq!(z.to_string(), "2.734375000");
let z = x % y;
assert_eq!(z.to_string(), "4.70");
```

```rust
# #![allow(incomplete_features)]
# #![feature(generic_const_exprs)]
# use rust_fixed_point_decimal::{Dec, Decimal};
let x = Dec!(17.5);
let y = -5_i64;
let z = x + y;
assert_eq!(z.to_string(), "12.5");
let z = x - y;
assert_eq!(z.to_string(), "22.5");
let z = y * x;
assert_eq!(z.to_string(), "-87.5");
let z = x / y;
assert_eq!(z.to_string(), "-3.500000000");
let z = x % y;
assert_eq!(z.to_string(), "2.5");
```

All these binary numeric operators panic if the result is not representable as 
a `Decimal` according to the constraints stated above. In addition there are
functions implementing "checked" variants of the operators which return 
`Option::None` instead of panicking.

For Multiplication and Division there are also functions which return a result
rounded to a number of fractional digits determined by the target type:

```rust
# #![allow(incomplete_features)]
# #![feature(generic_const_exprs)]
# use rust_fixed_point_decimal::{Dec, Decimal, DivRounded, MulRounded};
let x = Dec!(17.5);
let y = Dec!(6.47);
let z: Decimal<1> = x.mul_rounded(y);
assert_eq!(z.to_string(), "113.2");
let z: Decimal<3> = x.div_rounded(y);
assert_eq!(z.to_string(), "2.705");
```
