// ----------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ----------------------------------------------------------------------------
// $Source$
// $Revision$

use std::ops::Shl;

use num::{FromPrimitive, Integer, Num};

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

pub trait Round {
    fn round<T: Num>(
        num: T,
        n_frac_digits: i8,
        mode: Option<RoundingMode>,
    ) -> T;
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
mod tests {
    use std::convert::TryInto;

    use super::*;

    const TESTDATA: [(i32, i32, RoundingMode, i32); 32] = [
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
