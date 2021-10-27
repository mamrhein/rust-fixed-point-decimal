// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::cmp::Ordering;

use rust_fixed_point_decimal_core::{checked_adjust_prec, checked_mul_pow_ten};

use crate::{
    prec_constraints::{PrecLimitCheck, True},
    Decimal, MAX_PREC,
};

impl<const P: u8, const Q: u8> PartialEq<Decimal<Q>> for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= MAX_PREC }>: True,
{
    fn eq(&self, other: &Decimal<Q>) -> bool {
        match checked_adjust_prec(self.coeff, P, other.coeff, Q) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        }
    }
}

impl<const P: u8, const Q: u8> PartialOrd<Decimal<Q>> for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= MAX_PREC }>: True,
{
    fn partial_cmp(&self, other: &Decimal<Q>) -> Option<Ordering> {
        match checked_adjust_prec(self.coeff, P, other.coeff, Q) {
            (Some(a), Some(b)) => a.partial_cmp(&b),
            (None, Some(_)) => {
                if self.coeff > 0 {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Less)
                }
            }
            (Some(_), None) => {
                if other.coeff < 0 {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Less)
                }
            }
            // Should never happen:
            (None, None) => None,
        }
    }
}

impl<const P: u8> Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
{
    /// Returns true if self is equal to zero.
    #[inline(always)]
    pub fn eq_zero(&self) -> bool {
        self.coeff == 0
    }

    /// Returns true if self is equal to one.
    #[inline(always)]
    pub fn eq_one(&self) -> bool {
        self.coeff == Self::ONE.coeff
    }

    /// Returns true if self is less than zero.
    #[inline(always)]
    pub fn is_negative(&self) -> bool {
        self.coeff < 0
    }

    /// Returns true if self is greater than zero.
    #[inline(always)]
    pub fn is_positive(&self) -> bool {
        self.coeff > 0
    }
}

#[cfg(test)]
mod cmp_decimals_tests {
    use std::cmp::{max, min, Ordering};

    use crate::Decimal;

    #[test]
    fn test_eq_same_prec() {
        let x = Decimal::<1>::new_raw(178);
        assert!(x.eq(&x));
        let y = x.clone();
        assert!(x.eq(&y));
        assert_eq!(x, y);
        assert_eq!(y, x);
        assert!(!(y.ne(&x)));
    }

    #[test]
    fn test_eq_different_prec() {
        let x = Decimal::<1>::new_raw(178);
        let y = Decimal::<4>::new_raw(178000);
        assert!(x.eq(&y));
        assert_eq!(x, y);
        assert_eq!(y, x);
        assert!(!(y.ne(&x)));
    }

    #[test]
    fn test_ne_same_prec() {
        let x = Decimal::<7>::new_raw(-178000);
        let y = Decimal::<7>::new_raw(178000);
        assert_ne!(x, y);
        assert_eq!(x.partial_cmp(&y), Some(Ordering::Less));
        assert_eq!(x.cmp(&y), Ordering::Less);
        assert!(x < y);
        assert!(y > x);
    }

    #[test]
    fn test_ne_different_prec() {
        let x = Decimal::<7>::new_raw(178001);
        let y = Decimal::<4>::new_raw(178);
        assert_ne!(x, y);
        assert_eq!(x.partial_cmp(&y), Some(Ordering::Greater));
        assert!(x > y);
        assert!(y < x);
    }

    #[test]
    fn test_cmp_max() {
        assert_eq!(Decimal::<5>::MAX, Decimal::<5>::MAX);
        assert_ne!(Decimal::<2>::MAX, Decimal::<9>::MAX);
        assert!(Decimal::<2>::MAX > Decimal::<3>::MAX);
        assert!(Decimal::<6>::MAX < Decimal::<4>::MAX);
    }

    #[test]
    fn test_cmp_min() {
        assert_eq!(Decimal::<5>::MIN, Decimal::<5>::MIN);
        assert_ne!(Decimal::<2>::MIN, Decimal::<9>::MIN);
        assert!(Decimal::<2>::MIN < Decimal::<3>::MIN);
        assert!(Decimal::<6>::MIN > Decimal::<4>::MIN);
    }

    #[test]
    fn test_min_max() {
        let x = Decimal::<2>::new_raw(12345);
        let y = Decimal::<2>::new_raw(12344);
        assert_eq!(min(x, y), y);
        assert_eq!(min(x, x), x);
        assert_eq!(max(x, y), x);
        assert_eq!(max(x, x), x);
    }

    #[test]
    fn test_eq_zero() {
        assert!(Decimal::<0>::eq_zero(&Decimal::<0>::ZERO));
        assert!(Decimal::<1>::eq_zero(&Decimal::<1>::ZERO));
        assert!(Decimal::<2>::eq_zero(&Decimal::<2>::ZERO));
        assert!(Decimal::<3>::eq_zero(&Decimal::<3>::ZERO));
        assert!(Decimal::<4>::eq_zero(&Decimal::<4>::ZERO));
        assert!(Decimal::<5>::eq_zero(&Decimal::<5>::ZERO));
        assert!(Decimal::<6>::eq_zero(&Decimal::<6>::ZERO));
        assert!(Decimal::<7>::eq_zero(&Decimal::<7>::ZERO));
        assert!(Decimal::<8>::eq_zero(&Decimal::<8>::ZERO));
        assert!(Decimal::<9>::eq_zero(&Decimal::<9>::ZERO));
        assert!(!Decimal::<0>::eq_zero(&Decimal::<0>::ONE));
        assert!(!Decimal::<1>::eq_zero(&Decimal::<1>::ONE));
        assert!(!Decimal::<2>::eq_zero(&Decimal::<2>::ONE));
        assert!(!Decimal::<3>::eq_zero(&Decimal::<3>::ONE));
        assert!(!Decimal::<4>::eq_zero(&Decimal::<4>::ONE));
        assert!(!Decimal::<5>::eq_zero(&Decimal::<5>::ONE));
        assert!(!Decimal::<6>::eq_zero(&Decimal::<6>::ONE));
        assert!(!Decimal::<7>::eq_zero(&Decimal::<7>::ONE));
        assert!(!Decimal::<8>::eq_zero(&Decimal::<8>::ONE));
        assert!(!Decimal::<9>::eq_zero(&Decimal::<9>::ONE));
    }

    #[test]
    fn test_eq_one() {
        assert!(Decimal::<0>::eq_one(&Decimal::<0>::ONE));
        assert!(Decimal::<1>::eq_one(&Decimal::<1>::ONE));
        assert!(Decimal::<2>::eq_one(&Decimal::<2>::ONE));
        assert!(Decimal::<3>::eq_one(&Decimal::<3>::ONE));
        assert!(Decimal::<4>::eq_one(&Decimal::<4>::ONE));
        assert!(Decimal::<5>::eq_one(&Decimal::<5>::ONE));
        assert!(Decimal::<6>::eq_one(&Decimal::<6>::ONE));
        assert!(Decimal::<7>::eq_one(&Decimal::<7>::ONE));
        assert!(Decimal::<8>::eq_one(&Decimal::<8>::ONE));
        assert!(Decimal::<9>::eq_one(&Decimal::<9>::ONE));
        assert!(!Decimal::<0>::eq_one(&Decimal::<0>::ZERO));
        assert!(!Decimal::<1>::eq_one(&Decimal::<1>::ZERO));
        assert!(!Decimal::<2>::eq_one(&Decimal::<2>::ZERO));
        assert!(!Decimal::<3>::eq_one(&Decimal::<3>::ZERO));
        assert!(!Decimal::<4>::eq_one(&Decimal::<4>::ZERO));
        assert!(!Decimal::<5>::eq_one(&Decimal::<5>::ZERO));
        assert!(!Decimal::<6>::eq_one(&Decimal::<6>::ZERO));
        assert!(!Decimal::<7>::eq_one(&Decimal::<7>::ZERO));
        assert!(!Decimal::<8>::eq_one(&Decimal::<8>::ZERO));
        assert!(!Decimal::<9>::eq_one(&Decimal::<9>::ZERO));
    }
}

// Implementing the symmetric comparison using the following macros also for
// `u8` causes a compiler error[E0391]:
// cycle detected when building an abstract representation for the const
// argument ...
// So for now it's left out.
// TODO: check with next rustc version!

macro_rules! impl_decimal_eq_uint {
    () => {
        impl_decimal_eq_uint!(u16, u32, u64);
    };
    ($($t:ty),*) => {
        $(
        impl<const P: u8> PartialEq<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            #[inline(always)]
            fn eq(&self, other: &$t) -> bool {
                if self.is_negative() {
                    return false;
                }
                match checked_mul_pow_ten((*other) as i128, P) {
                    Some(coeff) => self.coeff == coeff,
                    None => false,
                }
            }
        }
        )*
    }
}

impl_decimal_eq_uint!();

macro_rules! impl_decimal_eq_signed_int {
    () => {
        impl_decimal_eq_signed_int!(i8, i16, i32, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl<const P: u8> PartialEq<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            #[inline(always)]
            fn eq(&self, other: &$t) -> bool {
                match checked_mul_pow_ten((*other) as i128, P) {
                    Some(coeff) => self.coeff == coeff,
                    None => false,
                }
            }
        }
        )*
    }
}

impl_decimal_eq_signed_int!();

macro_rules! impl_int_eq_decimal {
    () => {
        impl_int_eq_decimal!(i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl<const Q: u8> PartialEq<Decimal<Q>> for $t
        where
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            Decimal<Q>: PartialEq<$t>,
        {
            #[inline(always)]
            fn eq(&self, other: &Decimal<Q>) -> bool {
                PartialEq::eq(other, self)
            }
        }
        )*
    }
}

impl_int_eq_decimal!();

macro_rules! impl_decimal_cmp_signed_int {
    () => {
        impl_decimal_cmp_signed_int!(i8, i16, i32, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl<const P: u8> PartialOrd<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            #[inline(always)]
            fn partial_cmp(&self, other: &$t) -> Option<Ordering> {
                match checked_mul_pow_ten((*other) as i128, P) {
                    Some(coeff) => self.coeff.partial_cmp(&coeff),
                    None => {
                        if *other >= 0 {
                            Some(Ordering::Less)
                        } else {
                            Some(Ordering::Greater)
                        }
                    },
                }
            }
        }
        )*
    }
}

impl_decimal_cmp_signed_int!();

macro_rules! impl_signed_int_cmp_decimal {
    () => {
        impl_signed_int_cmp_decimal!(i8, i16, i32, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl<const Q: u8> PartialOrd<Decimal<Q>> for $t
        where
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
        {
            #[inline(always)]
            fn partial_cmp(&self, other: &Decimal<Q>) -> Option<Ordering> {
                match checked_mul_pow_ten((*self) as i128, Q) {
                    Some(coeff) => coeff.partial_cmp(&other.coeff),
                    None => {
                        if *self < 0 {
                            Some(Ordering::Less)
                        } else {
                            Some(Ordering::Greater)
                        }
                    },
                }
            }
        }
        )*
    }
}

impl_signed_int_cmp_decimal!();

macro_rules! impl_decimal_cmp_uint {
    () => {
        impl_decimal_cmp_uint!(u16, u32, u64);
    };
    ($($t:ty),*) => {
        $(
        impl<const P: u8> PartialOrd<$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
        {
            #[inline(always)]
            fn partial_cmp(&self, other: &$t) -> Option<Ordering> {
                if self.is_negative() {
                    return Some(Ordering::Less);
                }
                match checked_mul_pow_ten((*other) as i128, P) {
                    Some(coeff) => self.coeff.partial_cmp(&coeff),
                    None => Some(Ordering::Less),
                }
            }
        }
        )*
    }
}

impl_decimal_cmp_uint!();

macro_rules! impl_uint_cmp_decimal {
    () => {
        impl_uint_cmp_decimal!(u16, u32, u64);
    };
    ($($t:ty),*) => {
        $(
        impl<const Q: u8> PartialOrd<Decimal<Q>> for $t
        where
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
        {
            #[inline(always)]
            fn partial_cmp(&self, other: &Decimal<Q>) -> Option<Ordering> {
                if other.is_negative() {
                    return Some(Ordering::Greater);
                }
                match checked_mul_pow_ten((*self) as i128, Q) {
                    Some(coeff) => coeff.partial_cmp(&other.coeff),
                    None => Some(Ordering::Greater),
                }
            }
        }
        )*
    }
}

impl_uint_cmp_decimal!();

#[cfg(test)]
mod cmp_decimals_and_ints_tests {
    use std::cmp::Ordering;

    use crate::Decimal;

    #[test]
    fn test_eq() {
        let x = Decimal::<1>::new_raw(170);
        assert!(x.eq(&x));
        let y = 17_u32;
        assert!(x.eq(&y));
        assert!(y.eq(&x));
        let y = 17_i128;
        assert_eq!(x, y);
        assert_eq!(y, x);
    }

    #[test]
    fn test_ne() {
        let x = Decimal::<7>::new_raw(-178000);
        let y = 0_i8;
        assert_ne!(x, y);
        assert_eq!(x.partial_cmp(&y), Some(Ordering::Less));
        assert!(x < y);
        assert!(y > x);
        let y = 1_u32;
        assert_ne!(x, y);
        assert_eq!(x.partial_cmp(&y), Some(Ordering::Less));
        assert!(x < y);
        assert!(y > x);
        let x = Decimal::<1>::new_raw(178);
        let y = 18_u64;
        assert_ne!(x, y);
        assert!(x <= y);
        assert!(y >= x);
    }
}
