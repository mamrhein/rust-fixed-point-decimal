// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::{cmp::Ordering, ops::Div};

use num::Zero;
use rust_fixed_point_decimal_core::ten_pow;

use crate::{
    prec_constraints::{PrecLimitCheck, True},
    rounding::div_rounded,
    Decimal, DecimalError, MAX_PREC,
};

pub trait DivRounded<Rhs, Result = Self> {
    /// Returns `self` * `other`, rounded as `Result`.
    fn div_rounded(self, rhs: Rhs) -> Result;
}

impl<const P: u8, const Q: u8, const R: u8> DivRounded<Decimal<Q>, Decimal<R>>
    for Decimal<P>
where
    PrecLimitCheck<{ P <= MAX_PREC }>: True,
    PrecLimitCheck<{ Q <= MAX_PREC }>: True,
    Decimal<P>: Div<Decimal<Q>>,
    PrecLimitCheck<{ R <= MAX_PREC }>: True,
{
    #[inline(always)]
    fn div_rounded(self, other: Decimal<Q>) -> Decimal<R> {
        if other.eq_zero() {
            panic!("{}", DecimalError::DivisionByZero);
        }
        match P.cmp(&(Q + R)) {
            Ordering::Equal => Decimal::<R> {
                coeff: div_rounded(self.coeff, other.coeff, None),
            },
            Ordering::Less => Decimal::<R> {
                coeff: div_rounded(
                    self.coeff * ten_pow(R + Q - P),
                    other.coeff,
                    None,
                ),
            },
            Ordering::Greater => Decimal::<R> {
                coeff: div_rounded(
                    self.coeff,
                    other.coeff * ten_pow(P - Q - R),
                    None,
                ),
            },
        }
    }
}

forward_ref_binop_rounded!(impl DivRounded, div_rounded);

#[cfg(test)]
mod div_rounded_decimal_tests {
    use rust_fixed_point_decimal_core::mul_pow_ten;

    use super::*;

    #[test]
    fn test_div_rounded() {
        let x = Decimal::<0>::new_raw(17);
        let y = Decimal::<2>::new_raw(-201);
        let z: Decimal<2> = x.div_rounded(y);
        assert_eq!(z.coeff, -846);
        let x = Decimal::<8>::new_raw(17);
        let y = Decimal::<3>::new_raw(204);
        let z: Decimal<8> = x.div_rounded(y);
        assert_eq!(z.coeff, 83);
        let x = Decimal::<2>::new_raw(12345678901234567890);
        let y = Decimal::<6>::new_raw(244140625);
        let z = x / y;
        assert_eq!(z.coeff, 505679007794567900774400);
    }

    #[test]
    fn test_div_rounded_by_one() {
        let x = Decimal::<5>::new_raw(17);
        let y = Decimal::<2>::ONE;
        let z: Decimal<4> = x.div_rounded(y);
        assert_eq!(z.coeff, 2);
        let y = Decimal::<9>::ONE;
        let z: Decimal<4> = x.div_rounded(y);
        assert_eq!(z.coeff, 2);
    }

    #[test]
    #[should_panic]
    fn test_div_rounded_by_zero() {
        let x = Decimal::<5>::new_raw(17);
        let y = Decimal::<2>::ZERO;
        let _z: Decimal<5> = x.div_rounded(y);
    }

    #[test]
    #[should_panic]
    fn test_div_rounded_overflow() {
        let x = Decimal::<0>::new_raw(mul_pow_ten(17, 20));
        let y = Decimal::<9>::new_raw(2);
        let _z: Decimal<9> = x.div_rounded(y);
    }

    #[test]
    fn test_div_rounded_ref() {
        let x = Decimal::<3>::new_raw(12345);
        let y = Decimal::<4>::new_raw(12345);
        let z: Decimal<2> = x.div_rounded(y);
        let a: Decimal<2> = DivRounded::div_rounded(&x, y);
        assert_eq!(a.coeff, z.coeff);
        let a: Decimal<2> = DivRounded::div_rounded(x, &y);
        assert_eq!(a.coeff, z.coeff);
        let a: Decimal<2> = DivRounded::div_rounded(&x, &y);
        assert_eq!(a.coeff, z.coeff);
    }
}

macro_rules! impl_div_rounded_decimal_and_int {
    (impl $imp:ident, $method:ident) => {
        impl_div_rounded_decimal_and_int!(
            impl $imp, $method, u8, i8, u16, i16, u32, i32, u64, i64, i128
        );
    };
    (impl $imp:ident, $method:ident, $($t:ty),*) => {
        $(
        impl<const P: u8, const R: u8> $imp<$t, Decimal<R>> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
        {
            fn $method(self, other: $t) -> Decimal<R> {
                if other.is_zero() {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                match P.cmp(&R) {
                    Ordering::Equal => Decimal::<R> {
                        coeff: div_rounded(self.coeff, other as i128, None),
                    },
                    Ordering::Less => Decimal::<R> {
                        coeff: div_rounded(
                            self.coeff * ten_pow(R - P),
                            other as i128,
                            None,
                        ),
                    },
                    Ordering::Greater => Decimal::<R> {
                        coeff: div_rounded(
                            self.coeff,
                            other as i128 * ten_pow(P - R),
                            None,
                        ),
                    },
                }
            }
        }

        impl<'a, const P: u8, const R: u8> $imp<$t, Decimal<R>>
        for &'a Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
            Decimal<P>: $imp<$t, Decimal<R>>,
        {
            #[inline(always)]
            fn $method(self, other: $t) -> Decimal<R> {
                $imp::$method(*self, other)
            }
        }

        impl<const P: u8, const R: u8> $imp<&$t, Decimal<R>> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
            Decimal<P>: $imp<$t, Decimal<R>>,
        {
            #[inline(always)]
            fn $method(self, other: &$t) -> Decimal<R> {
                $imp::$method(self, *other)
            }
        }

        impl<const P: u8, const R: u8> $imp<&$t, Decimal<R>> for &Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
            Decimal<P>: $imp<$t, Decimal<R>>,
        {
            #[inline(always)]
            fn $method(self, other: &$t) -> Decimal<R> {
                $imp::$method(*self, *other)
            }
        }

        impl<const P: u8, const R: u8> $imp<Decimal<P>, Decimal<R>> for $t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
        {
            fn $method(self, other: Decimal<P>) -> Decimal::<R> {
                if other.eq_zero() {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                Decimal::<R> {
                    coeff: div_rounded(
                        self as i128 * ten_pow(P + R),
                        other.coeff,
                        None,
                    ),
                }
            }
        }

        impl<'a, const P: u8, const R: u8> $imp<Decimal<P>, Decimal<R>> for &'a $t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
            $t: $imp<Decimal<P>, Decimal<R>>,
        {
            #[inline(always)]
            fn $method(self, other: Decimal<P>) -> Decimal<R> {
                $imp::$method(*self, other)
            }
        }

        impl<const P: u8, const R: u8> $imp<&Decimal<P>, Decimal<R>> for $t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
            $t: $imp<Decimal<P>, Decimal<R>>,
        {
            #[inline(always)]
            fn $method(self, other: &Decimal<P>) -> Decimal<R> {
                $imp::$method(self, *other)
            }
        }

        impl<const P: u8, const R: u8> $imp<&Decimal<P>, Decimal<R>> for &$t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
            $t: $imp<Decimal<P>, Decimal<R>>,
        {
            #[inline(always)]
            fn $method(self, other: &Decimal<P>) -> Decimal<R> {
                $imp::$method(*self, *other)
            }
        }
        )*
    }
}

impl_div_rounded_decimal_and_int!(impl DivRounded, div_rounded);

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod div_rounded_decimal_by_int_tests {
    use super::*;

    macro_rules! gen_div_rounded_decimal_by_int_tests {
        ($func:ident, $p:expr, $coeff:expr, $i:expr, $r:expr,
         $res_coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::<$p>::new_raw($coeff);
                let i = $i;
                let r: Decimal<$r> = d.div_rounded(i);
                assert_eq!(r.coeff, $res_coeff);
                let r: Decimal<$r> = (&d).div_rounded(i);
                assert_eq!(r.coeff, $res_coeff);
                let r: Decimal<$r> = d.div_rounded(&i);
                assert_eq!(r.coeff, $res_coeff);
                let r: Decimal<$r> = (&d).div_rounded(&i);
                assert_eq!(r.coeff, $res_coeff);
            }
        };
    }

    gen_div_rounded_decimal_by_int_tests!(test_u8, 2, -1, 3_u8, 5, -333);
    gen_div_rounded_decimal_by_int_tests!(test_i8, 0, -12, -3_i8, 5, 400000);
    gen_div_rounded_decimal_by_int_tests!(test_u16, 2, -1, 3_u16, 5, -333);
    gen_div_rounded_decimal_by_int_tests!(test_i16, 3, -12, -3_i16, 5, 400);
    gen_div_rounded_decimal_by_int_tests!(
        test_u32,
        4,
        u32::MAX as i128,
        1_u32,
        5,
        u32::MAX as i128 * 10_i128
    );
    gen_div_rounded_decimal_by_int_tests!(
        test_i32, 3, 12345, -328_i32, 5, -3764
    );
    gen_div_rounded_decimal_by_int_tests!(test_u64, 9, -1, 2_u64, 5, 0);
    gen_div_rounded_decimal_by_int_tests!(
        test_i64,
        3,
        u64::MAX as i128,
        i64::MIN,
        2,
        0
    );
    gen_div_rounded_decimal_by_int_tests!(
        test_i128,
        0,
        12345678901234567890,
        987654321_i128,
        5,
        1249999988734375
    );
}

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod div_rounded_int_by_decimal_tests {
    use super::*;

    macro_rules! gen_div_rounded_int_by_decimal_tests {
        ($func:ident, $p:expr, $coeff:expr, $i:expr, $r:expr,
         $res_coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::<$p>::new_raw($coeff);
                let i = $i;
                let r: Decimal<$r> = i.div_rounded(d);
                assert_eq!(r.coeff, $res_coeff);
                let r: Decimal<$r> = (&i).div_rounded(d);
                assert_eq!(r.coeff, $res_coeff);
                let r: Decimal<$r> = i.div_rounded(&d);
                assert_eq!(r.coeff, $res_coeff);
                let r: Decimal<$r> = (&i).div_rounded(&d);
                assert_eq!(r.coeff, $res_coeff);
            }
        };
    }

    gen_div_rounded_int_by_decimal_tests!(test_u8, 2, -14, 3_u8, 5, -2142857);
    gen_div_rounded_int_by_decimal_tests!(test_i8, 0, -12, -3_i8, 5, 25000);
    gen_div_rounded_int_by_decimal_tests!(test_u16, 2, -17, 3_u16, 5, -1764706);
    gen_div_rounded_int_by_decimal_tests!(test_i16, 3, -12, -3_i16, 2, 25000);
    gen_div_rounded_int_by_decimal_tests!(
        test_u32,
        4,
        u32::MAX as i128,
        1_u32,
        9,
        2328
    );
    gen_div_rounded_int_by_decimal_tests!(
        test_i32, 3, 12345, -328_i32, 5, -2656946
    );
    gen_div_rounded_int_by_decimal_tests!(
        test_u64,
        9,
        -1,
        2_u64,
        5,
        -200000000000000
    );
    gen_div_rounded_int_by_decimal_tests!(
        test_i64,
        3,
        u64::MAX as i128,
        i64::MIN,
        2,
        -50000
    );
    gen_div_rounded_int_by_decimal_tests!(
        test_i128,
        0,
        1234567890,
        987654321987654321_i128,
        1,
        8000000081
    );
}
