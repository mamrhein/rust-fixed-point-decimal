// ----------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ----------------------------------------------------------------------------
// $Source$
// $Revision$

use num::{Integer, Num};

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
        RoundingMode::RoundHalfUp
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
pub(crate) fn div_rounded(
    divident: i128,
    divisor: i128,
    mode: Option<RoundingMode>,
) -> i128 {
    assert!(divisor > 0);
    let (quot, rem) = divident.div_mod_floor(&divisor);
    // div_mod_floor => rem >= 0
    if rem == 0 {
        // no need for rounding
        return quot;
    }
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
            if quot >= 0 && quot % 5 == 0 || quot < 0 && (quot + 1) % 5 != 0 {
                return quot + 1;
            }
        }
        RoundingMode::RoundCeiling => {
            // Round towards Infinity (i. e. not away from 0 if negative):
            // => always add 1
            return quot + 1;
        }
        RoundingMode::RoundDown => {
            // Round towards 0 (aka truncate):
            // quotient negativ => add 1
            if quot < 0 {
                return quot + 1;
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
            let rem_doubled = 2 * rem;
            if rem_doubled > divisor || rem_doubled == divisor && quot < 0 {
                return quot + 1;
            }
        }
        RoundingMode::RoundHalfEven => {
            // Round 5 to nearest even, rest to nearest:
            // remainder > divisor / 2 or
            // remainder = divisor / 2 and quotient not even
            // => add 1
            let rem_doubled = 2 * rem;
            if rem_doubled > divisor || rem_doubled == divisor && quot % 2 != 0
            {
                return quot + 1;
            }
        }
        RoundingMode::RoundHalfUp => {
            // Round 5 up (away from 0), rest to nearest:
            // remainder > divisor / 2 or
            // remainder = divisor / 2 and quotient >= 0
            // => add 1
            let rem_doubled = 2 * rem;
            if rem_doubled > divisor || rem_doubled == divisor && quot >= 0 {
                return quot + 1;
            }
        }
        RoundingMode::RoundUp => {
            // Round away from 0:
            // quotient not negative => add 1
            if quot >= 0 {
                return quot + 1;
            }
        }
    }
    // fall-through: round towards 0
    quot
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_div_rounded() {
        let testdata = [
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
        for (divident, divisor, rnd_mode, result) in testdata {
            let quot = div_rounded(divident, divisor, Some(rnd_mode));
            // println!("{} {} {:?}", divident, divisor, rnd_mode);
            assert_eq!(quot, result);
        }
    }
}
