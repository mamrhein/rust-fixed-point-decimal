// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::cmp::Ordering;

use rust_fixed_point_decimal_core::checked_adjust_prec;

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

#[cfg(test)]
mod tests {
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
}
