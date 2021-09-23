// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::{
    cmp::{min, Ordering},
    fmt,
};

use num::{integer::div_mod_floor, Integer};
use rust_fixed_point_decimal_core::ten_pow;

use crate::{
    prec_constraints::{PrecLimitCheck, True},
    rounding::div_rounded,
    Decimal, MAX_PREC,
};

impl<const P: u8> fmt::Debug for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
{
    fn fmt(&self, form: &mut fmt::Formatter<'_>) -> fmt::Result {
        if P == 0 {
            write!(form, "Dec!({})", self.coeff)
        } else {
            let (int, frac) = div_mod_floor(self.coeff, ten_pow(P));
            write!(form, "Dec!({}.{:0width$})", int, frac, width = P as usize)
        }
    }
}

#[cfg(test)]
mod test_fmt_debug {
    use super::*;

    #[test]
    fn test_fmt() {
        let d = Decimal::<3>::new_raw(1234567890002);
        assert_eq!(format!("{:?}", d), "Dec!(1234567890.002)");
        let d = Decimal::<9>::new_raw(-1230000000000);
        assert_eq!(format!("{:?}", d), "Dec!(-1230.000000000)");
        let d = Decimal::<0>::new_raw(1234567890002);
        assert_eq!(format!("{:?}", d), "Dec!(1234567890002)");
    }
}

impl<const P: u8> fmt::Display for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
{
    fn fmt(&self, form: &mut fmt::Formatter<'_>) -> fmt::Result {
        let tmp: String;
        let prec = match form.precision() {
            Some(prec) => min(prec, MAX_PREC as usize),
            None => P as usize,
        };
        if P == 0 {
            if prec > 0 {
                tmp =
                    format!("{}.{:0width$}", self.coeff.abs(), 0, width = prec);
            } else {
                tmp = self.coeff.abs().to_string();
            }
        } else {
            let (int, frac) = match prec.cmp(&(P as usize)) {
                Ordering::Equal => self.coeff.abs().div_mod_floor(&ten_pow(P)),
                Ordering::Less => {
                    // Important: first round, then take abs() !
                    let coeff =
                        div_rounded(self.coeff, ten_pow(P - prec as u8), None);
                    coeff.abs().div_mod_floor(&ten_pow(prec as u8))
                }
                Ordering::Greater => {
                    let (int, frac) =
                        self.coeff.abs().div_mod_floor(&ten_pow(P));
                    (int, frac * ten_pow(prec as u8 - P))
                }
            };
            if prec > 0 {
                tmp = format!("{}.{:0width$}", int, frac, width = prec);
            } else {
                tmp = int.to_string();
            }
        }
        form.pad_integral(!self.is_negative(), "", &tmp)
    }
}

#[cfg(test)]
mod test_fmt_display {
    use super::*;

    #[test]
    fn test_fmt_decimal_0() {
        let d = Decimal::<0>::new_raw(1234567890002);
        assert_eq!(d.to_string(), "1234567890002");
        assert_eq!(format!("{}", d), "1234567890002");
        assert_eq!(format!("{:<15}", d), "1234567890002  ");
        assert_eq!(format!("{:^15}", d), " 1234567890002 ");
        assert_eq!(format!("{:>15}", d), "  1234567890002");
        assert_eq!(format!("{:15}", d), "  1234567890002");
        assert_eq!(format!("{:015}", d), "001234567890002");
        assert_eq!(format!("{:010.2}", d), "1234567890002.00");
        let d = Decimal::<0>::new_raw(-12345);
        assert_eq!(d.to_string(), "-12345");
        assert_eq!(format!("{}", d), "-12345");
        assert_eq!(format!("{:10}", d), "    -12345");
        assert_eq!(format!("{:010}", d), "-000012345");
        assert_eq!(format!("{:012.3}", d), "-0012345.000");
    }

    #[test]
    fn test_fmt_decimal_without_rounding() {
        let d = Decimal::<4>::new_raw(1234567890002);
        assert_eq!(d.to_string(), "123456789.0002");
        assert_eq!(format!("{}", d), "123456789.0002");
        assert_eq!(format!("{:<15}", d), "123456789.0002 ");
        assert_eq!(format!("{:^17}", d), " 123456789.0002  ");
        assert_eq!(format!("{:>15}", d), " 123456789.0002");
        assert_eq!(format!("{:15}", d), " 123456789.0002");
        assert_eq!(format!("{:015}", d), "0123456789.0002");
        assert_eq!(format!("{:010.7}", d), "123456789.0002000");
        let d = Decimal::<2>::new_raw(-12345);
        assert_eq!(d.to_string(), "-123.45");
        assert_eq!(format!("{}", d), "-123.45");
        assert_eq!(format!("{:10}", d), "   -123.45");
        assert_eq!(format!("{:010}", d), "-000123.45");
        assert_eq!(format!("{:012.3}", d), "-0000123.450");
        let d = Decimal::<7>::new_raw(-12345);
        assert_eq!(d.to_string(), "-0.0012345");
        assert_eq!(format!("{}", d), "-0.0012345");
    }

    #[test]
    fn test_fmt_decimal_with_rounding() {
        let d = Decimal::<5>::new_raw(1234567890002);
        assert_eq!(format!("{:.4}", d), "12345678.9000");
        assert_eq!(format!("{:<15.2}", d), "12345678.90    ");
        assert_eq!(format!("{:.0}", d), "12345679");
        let d = Decimal::<7>::new_raw(-12347);
        assert_eq!(format!("{:.3}", d), "-0.001");
        assert_eq!(format!("{:10.5}", d), "  -0.00123");
        assert_eq!(format!("{:010.6}", d), "-00.001235");
    }
}
