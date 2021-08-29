// ----------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ----------------------------------------------------------------------------
// $Source$
// $Revision$

use std::ops::Shl;

use num::{FromPrimitive, Integer};

use crate::{
    powers_of_ten::ten_pow,
    prec_constraints::{PrecLimitCheck, True},
    Decimal,
};

#[derive(Clone, Copy, Debug)]
pub enum RoundingMode {
    /// Round away from zero if last digit after rounding towards zero would
    /// have been 0 or 5; otherwise round towards zero.
    Round05Up,
    /// Round towards Infinity.
    RoundCeiling,
    /// Round towards zero.
    RoundDown,
    /// Round towards -Infinity.
    RoundFloor,
    /// Round to nearest with ties going towards zero.
    RoundHalfDown,
    /// Round to nearest with ties going to nearest even integer.
    RoundHalfEven,
    /// Round to nearest with ties going away from zero.
    RoundHalfUp,
    /// Round away from zero.
    RoundUp,
}

impl Default for RoundingMode {
    fn default() -> Self {
        RoundingMode::RoundHalfEven
    }
}

pub trait Round
where
    Self: Sized,
{
    fn round(self: Self, n_frac_digits: i8) -> Self;
    fn checked_round(self: Self, n_frac_digits: i8) -> Option<Self>;
}

impl<const P: u8> Round for Decimal<P>
where
    PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
{
    fn round(self, n_frac_digits: i8) -> Self {
        if n_frac_digits >= P as i8 {
            self.clone()
        } else if n_frac_digits < P as i8 - 38 {
            Self::ZERO
        } else {
            // n_frac_digits < P
            let shift: u8 = (P as i8 - n_frac_digits) as u8;
            let divisor = ten_pow(shift);
            Self::new_raw(div_rounded(self.coeff, divisor, None) * divisor)
        }
    }

    fn checked_round(self, n_frac_digits: i8) -> Option<Self> {
        if n_frac_digits >= P as i8 {
            Some(self.clone())
        } else if n_frac_digits < P as i8 - 38 {
            Some(Self::ZERO)
        } else {
            // n_frac_digits < P
            let shift: u8 = (P as i8 - n_frac_digits) as u8;
            let divisor = ten_pow(shift);
            match div_rounded(self.coeff, divisor, None).checked_mul(divisor) {
                None => None,
                Some(coeff) => Some(Self::new_raw(coeff)),
            }
        }
    }
}

pub trait RoundInto<T>
where
    Self: Sized,
    T: Sized,
{
    fn round_into(self: Self) -> T;
}

impl<const P: u8> RoundInto<i128> for Decimal<P>
where
    PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
{
    fn round_into(self: Self) -> i128 {
        div_rounded(self.coeff, ten_pow(P), None)
    }
}

impl<const P: u8, const Q: u8> RoundInto<Decimal<Q>> for Decimal<P>
where
    PrecLimitCheck<{ P <= crate::MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= crate::MAX_PREC }>: True,
    PrecLimitCheck<{ Q < P }>: True,
{
    fn round_into(self: Self) -> Decimal<Q> {
        let divisor = ten_pow(P - Q);
        let coeff = div_rounded(self.coeff, divisor, None);
        Decimal::<Q>::new_raw(coeff)
    }
}

// rounding helper

/// Divide 'divident' by 'divisor' and round result according to 'mode'.
///
/// divisor must be >= 0 !
pub(crate) fn div_rounded<T>(
    divident: T,
    divisor: T,
    mode: Option<RoundingMode>,
) -> T
where
    T: Copy + Integer + FromPrimitive + Shl<u8, Output = T>,
{
    let zero = T::zero();
    assert!(divisor > zero);
    let one = T::one();
    let five = T::from_u8(5).unwrap();
    let (quot, rem) = divident.div_mod_floor(&divisor);
    // div_mod_floor => rem >= 0
    if rem == zero {
        // no need for rounding
        return quot;
    }
    // here: divisor >= 2 => rem <= divident / 2,
    // therefor it's safe to use rem << 1
    let mode = match mode {
        None => RoundingMode::default(),
        Some(mode) => mode,
    };
    match mode {
        RoundingMode::Round05Up => {
            // Round down unless last digit is 0 or 5:
            // quotient not negativ and quotient divisible by 5 w/o remainder or
            // quotient negativ and (quotient + 1) not divisible by 5 w/o rem.
            // => add 1
            if quot >= zero && quot % five == zero
                || quot < zero && (quot + one) % five != zero
            {
                return quot + one;
            }
        }
        RoundingMode::RoundCeiling => {
            // Round towards Infinity (i. e. not away from 0 if negative):
            // => always add 1
            return quot + one;
        }
        RoundingMode::RoundDown => {
            // Round towards 0 (aka truncate):
            // quotient negativ => add 1
            if quot < zero {
                return quot + one;
            }
        }
        RoundingMode::RoundFloor => {
            // Round towards -Infinity (i.e. not towards 0 if negative):
            // => never add 1
            return quot;
        }
        RoundingMode::RoundHalfDown => {
            // Round 5 down, rest to nearest:
            // remainder > divisor / 2 or
            // remainder = divisor / 2 and quotient < 0
            // => add 1
            let rem_doubled: T = rem << 1;
            if rem_doubled > divisor || rem_doubled == divisor && quot < zero {
                return quot + one;
            }
        }
        RoundingMode::RoundHalfEven => {
            // Round 5 to nearest even, rest to nearest:
            // remainder > divisor / 2 or
            // remainder = divisor / 2 and quotient not even
            // => add 1
            let rem_doubled = rem << 1;
            if rem_doubled > divisor
                || rem_doubled == divisor && !quot.is_even()
            {
                return quot + one;
            }
        }
        RoundingMode::RoundHalfUp => {
            // Round 5 up (away from 0), rest to nearest:
            // remainder > divisor / 2 or
            // remainder = divisor / 2 and quotient >= 0
            // => add 1
            let rem_doubled = rem << 1;
            if rem_doubled > divisor || rem_doubled == divisor && quot >= zero {
                return quot + one;
            }
        }
        RoundingMode::RoundUp => {
            // Round away from 0:
            // quotient not negative => add 1
            if quot >= zero {
                return quot + one;
            }
        }
    }
    // fall-through: round towards 0
    quot
}

#[cfg(test)]
mod helper_tests {
    use std::convert::TryInto;

    use super::*;

    const TESTDATA: [(i32, i32, RoundingMode, i32); 33] = [
        (17, 5, RoundingMode::Round05Up, 3),
        (27, 5, RoundingMode::Round05Up, 6),
        (-17, 5, RoundingMode::Round05Up, -3),
        (-27, 5, RoundingMode::Round05Up, -6),
        (17, 5, RoundingMode::RoundCeiling, 4),
        (15, 5, RoundingMode::RoundCeiling, 3),
        (-17, 5, RoundingMode::RoundCeiling, -3),
        (-15, 5, RoundingMode::RoundCeiling, -3),
        (19, 5, RoundingMode::RoundDown, 3),
        (15, 5, RoundingMode::RoundDown, 3),
        (-18, 5, RoundingMode::RoundDown, -3),
        (-15, 5, RoundingMode::RoundDown, -3),
        (19, 5, RoundingMode::RoundFloor, 3),
        (15, 5, RoundingMode::RoundFloor, 3),
        (-18, 5, RoundingMode::RoundFloor, -4),
        (-15, 5, RoundingMode::RoundFloor, -3),
        (19, 2, RoundingMode::RoundHalfDown, 9),
        (15, 4, RoundingMode::RoundHalfDown, 4),
        (-19, 2, RoundingMode::RoundHalfDown, -9),
        (-15, 4, RoundingMode::RoundHalfDown, -4),
        (19, 2, RoundingMode::RoundHalfEven, 10),
        (15, 4, RoundingMode::RoundHalfEven, 4),
        (-225, 50, RoundingMode::RoundHalfEven, -4),
        (-15, 4, RoundingMode::RoundHalfEven, -4),
        (19, 2, RoundingMode::RoundHalfUp, 10),
        (10802, 4321, RoundingMode::RoundHalfUp, 2),
        (-19, 2, RoundingMode::RoundHalfUp, -10),
        (-10802, 4321, RoundingMode::RoundHalfUp, -2),
        (19, 2, RoundingMode::RoundUp, 10),
        (10802, 4321, RoundingMode::RoundUp, 3),
        (-19, 2, RoundingMode::RoundUp, -10),
        (-10802, 4321, RoundingMode::RoundUp, -3),
        (i32::MAX, 1, RoundingMode::RoundUp, i32::MAX),
    ];

    macro_rules! test_div_rounded_uint {
        ($(($func:ident, $t:ty)),*) => {
            $(
            #[test]
            fn $func() {
                for (divident, divisor, rnd_mode, result) in TESTDATA {
                    if divident > 0
                            && !TryInto::<$t>::try_into(divident).is_err() {
                        let quot = div_rounded(TryInto::<$t>::try_into(divident).unwrap(),
                                               TryInto::<$t>::try_into(divisor).unwrap(),
                                               Some(rnd_mode));
                        // println!("{} {} {:?}", divident, divisor, rnd_mode);
                        assert_eq!(quot, TryInto::<$t>::try_into(result).unwrap());
                    }
                }
            }
            )*
        }
    }

    test_div_rounded_uint!(
        (test_div_rounded_u8, u8),
        (test_div_rounded_u16, u16),
        (test_div_rounded_u32, u32),
        (test_div_rounded_u64, u64),
        (test_div_rounded_u128, u128)
    );

    macro_rules! test_div_rounded_int {
        ($(($func:ident, $t:ty)),*) => {
            $(
            #[test]
            fn $func() {
                for (divident, divisor, rnd_mode, result) in TESTDATA {
                    if !TryInto::<$t>::try_into(divident).is_err() {
                        let quot = div_rounded(TryInto::<$t>::try_into(divident).unwrap(),
                                               TryInto::<$t>::try_into(divisor).unwrap(),
                                               Some(rnd_mode));
                        // println!("{} {} {:?}", divident, divisor, rnd_mode);
                        assert_eq!(quot, TryInto::<$t>::try_into(result).unwrap());
                    }
                }
            }
            )*
        }
    }

    test_div_rounded_int!(
        (test_div_rounded_i8, i8),
        (test_div_rounded_i16, i16),
        (test_div_rounded_i32, i32),
        (test_div_rounded_i64, i64),
        (test_div_rounded_i128, i128)
    );
}

#[cfg(test)]
mod round_decimal_tests {

    use super::*;

    macro_rules! test_decimal_round_no_op {
         ($(($p:expr, $func:ident)),*) => {
            $(
            #[test]
            fn $func() {
                let x = Decimal::<$p>::MIN;
                let y = x.round($p);
                assert_eq!(x.coeff, y.coeff);
                let y = x.round($p + 2);
                assert_eq!(x.coeff, y.coeff);
                let y = x.checked_round($p).unwrap();
                assert_eq!(x.coeff, y.coeff);
                let y = x.checked_round($p + 2).unwrap();
                assert_eq!(x.coeff, y.coeff);
            }
            )*
        }
    }

    test_decimal_round_no_op!(
        (0, test_decimal0_round_no_op),
        (1, test_decimal1_round_no_op),
        (2, test_decimal2_round_no_op),
        (3, test_decimal3_round_no_op),
        (4, test_decimal4_round_no_op),
        (5, test_decimal5_round_no_op),
        (6, test_decimal6_round_no_op),
        (7, test_decimal7_round_no_op),
        (8, test_decimal8_round_no_op),
        (9, test_decimal9_round_no_op)
    );

    macro_rules! test_decimal_round_result_zero {
         ($(($p:expr, $func:ident)),*) => {
            $(
            #[test]
            fn $func() {
                let x = Decimal::<$p>::MIN;
                let y = x.round($p - 39);
                assert_eq!(y.coeff, 0);
                let y = x.round($p - 42);
                assert_eq!(y.coeff, 0);
                let y = x.checked_round($p - 39).unwrap();
                assert_eq!(y.coeff, 0);
                let y = x.checked_round($p - 42).unwrap();
                assert_eq!(y.coeff, 0);
            }
            )*
        }
    }

    test_decimal_round_result_zero!(
        (0, test_decimal0_round_result_zero),
        (1, test_decimal1_round_result_zero),
        (2, test_decimal2_round_result_zero),
        (3, test_decimal3_round_result_zero),
        (4, test_decimal4_round_result_zero),
        (5, test_decimal5_round_result_zero),
        (6, test_decimal6_round_result_zero),
        (7, test_decimal7_round_result_zero),
        (8, test_decimal8_round_result_zero),
        (9, test_decimal9_round_result_zero)
    );

    #[test]
    fn test_decimal_round() {
        let d = Decimal::<0>::new_raw(12345);
        assert_eq!(d.round(-1).coeff, 12340);
        let d = Decimal::<0>::new_raw(1285);
        assert_eq!(d.round(-2).coeff, 1300);
        let d = Decimal::<1>::new_raw(12345);
        assert_eq!(d.round(0).coeff, 12340);
        let d = Decimal::<2>::new_raw(1285);
        assert_eq!(d.round(0).coeff, 1300);
        let d = Decimal::<7>::new_raw(12345678909876543);
        assert_eq!(d.round(0).coeff, 12345678910000000);
        let d = Decimal::<9>::new_raw(123455);
        assert_eq!(d.round(8).coeff, 123460);
    }

    #[test]
    #[should_panic]
    fn test_decimal_round_overflow() {
        let d = Decimal::<8>::MAX;
        let _ = d.round(0);
    }

    #[test]
    fn test_decimal_checked_round() {
        let d = Decimal::<0>::new_raw(12345);
        assert_eq!(d.checked_round(-1).unwrap().coeff, 12340);
        let d = Decimal::<0>::new_raw(1285);
        assert_eq!(d.checked_round(-2).unwrap().coeff, 1300);
        let d = Decimal::<1>::new_raw(12345);
        assert_eq!(d.checked_round(0).unwrap().coeff, 12340);
        let d = Decimal::<2>::new_raw(1285);
        assert_eq!(d.checked_round(0).unwrap().coeff, 1300);
        let d = Decimal::<7>::new_raw(12345678909876543);
        assert_eq!(d.checked_round(0).unwrap().coeff, 12345678910000000);
        let d = Decimal::<9>::new_raw(123455);
        assert_eq!(d.checked_round(8).unwrap().coeff, 123460);
        let d = Decimal::<0>::MAX;
        let res = d.checked_round(-1);
        assert!(res.is_none());
        let d = Decimal::<7>::MAX;
        let res = d.checked_round(4);
        assert!(res.is_none());
    }

    #[test]
    fn test_round_into_i128() {
        let d = Decimal::<4>::new_raw(12345000);
        let i: i128 = d.round_into();
        assert_eq!(i, 1234);
        let d = Decimal::<4>::new_raw(12345678);
        let i: i128 = d.round_into();
        assert_eq!(i, 1235);
        let d = Decimal::<2>::new_raw(12345678);
        let i: i128 = d.round_into();
        assert_eq!(i, 123457);
    }

    #[test]
    fn test_round_into_decimal() {
        let d = Decimal::<4>::new_raw(12345000);
        let r: Decimal<0> = d.round_into();
        assert_eq!(r.coeff, 1234);
        let d = Decimal::<4>::new_raw(12345678);
        let r: Decimal<0> = d.round_into();
        assert_eq!(r.coeff, 1235);
        let d = Decimal::<4>::new_raw(12345678);
        let r: Decimal<2> = d.round_into();
        assert_eq!(r.coeff, 123457);
        let d = Decimal::<7>::MAX; // 17014118346046923173168730371588.4105727
        let r: Decimal<2> = d.round_into();
        assert_eq!(r.coeff, 1701411834604692317316873037158841_i128);
    }
}
