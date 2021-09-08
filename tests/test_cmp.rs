// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use rust_fixed_point_decimal::{Dec, Decimal};

    #[test]
    fn test_ordering() {
        let test_data = [
            Decimal::<1>::MIN,
            Dec!(-3481900.3),
            Dec!(-0.4),
            Decimal::<1>::ZERO,
            Dec!(0.2),
            Decimal::<1>::ONE,
            Dec!(17.0),
            Decimal::<1>::MAX,
        ];
        for (i, x) in test_data.iter().enumerate() {
            for (j, y) in test_data.iter().enumerate() {
                assert_eq!(x.cmp(&y), i.cmp(&j));
            }
        }
    }

    macro_rules! gen_test_cmp {
        (
            $e1:expr,
            $e2:expr,
            $e3:expr,
            $e4:expr,
            $e5:expr,
            $e6:expr,
            $e7:expr,
            $e8:expr,
            $e9:expr,
            $e10:expr,
        ) => {
            #[test]
            fn test_cmp_1() {
                assert_eq!($e1.partial_cmp($e1).unwrap(), Ordering::Equal);
                assert_eq!($e1.partial_cmp($e2).unwrap(), Ordering::Less);
                assert_eq!($e1.partial_cmp($e3).unwrap(), Ordering::Less);
                assert_eq!($e1.partial_cmp($e4).unwrap(), Ordering::Less);
                assert_eq!($e1.partial_cmp($e5).unwrap(), Ordering::Less);
                assert_eq!($e1.partial_cmp($e6).unwrap(), Ordering::Less);
                assert_eq!($e1.partial_cmp($e7).unwrap(), Ordering::Less);
                assert_eq!($e1.partial_cmp($e8).unwrap(), Ordering::Less);
                assert_eq!($e1.partial_cmp($e9).unwrap(), Ordering::Less);
                assert_eq!($e1.partial_cmp($e10).unwrap(), Ordering::Less);
            }

            #[test]
            fn test_cmp_2() {
                assert_eq!($e2.partial_cmp($e1).unwrap(), Ordering::Greater);
                assert_eq!($e2.partial_cmp($e2).unwrap(), Ordering::Equal);
                assert_eq!($e2.partial_cmp($e3).unwrap(), Ordering::Less);
                assert_eq!($e2.partial_cmp($e4).unwrap(), Ordering::Less);
                assert_eq!($e2.partial_cmp($e5).unwrap(), Ordering::Less);
                assert_eq!($e2.partial_cmp($e6).unwrap(), Ordering::Less);
                assert_eq!($e2.partial_cmp($e7).unwrap(), Ordering::Less);
                assert_eq!($e2.partial_cmp($e8).unwrap(), Ordering::Less);
                assert_eq!($e2.partial_cmp($e9).unwrap(), Ordering::Less);
                assert_eq!($e2.partial_cmp($e10).unwrap(), Ordering::Less);
            }

            #[test]
            fn test_cmp_3() {
                assert_eq!($e3.partial_cmp($e1).unwrap(), Ordering::Greater);
                assert_eq!($e3.partial_cmp($e2).unwrap(), Ordering::Greater);
                assert_eq!($e3.partial_cmp($e3).unwrap(), Ordering::Equal);
                assert_eq!($e3.partial_cmp($e4).unwrap(), Ordering::Less);
                assert_eq!($e3.partial_cmp($e5).unwrap(), Ordering::Less);
                assert_eq!($e3.partial_cmp($e6).unwrap(), Ordering::Less);
                assert_eq!($e3.partial_cmp($e7).unwrap(), Ordering::Less);
                assert_eq!($e3.partial_cmp($e8).unwrap(), Ordering::Less);
                assert_eq!($e3.partial_cmp($e9).unwrap(), Ordering::Less);
                assert_eq!($e3.partial_cmp($e10).unwrap(), Ordering::Less);
            }

            #[test]
            fn test_cmp_4() {
                assert_eq!($e4.partial_cmp($e1).unwrap(), Ordering::Greater);
                assert_eq!($e4.partial_cmp($e2).unwrap(), Ordering::Greater);
                assert_eq!($e4.partial_cmp($e3).unwrap(), Ordering::Greater);
                assert_eq!($e4.partial_cmp($e4).unwrap(), Ordering::Equal);
                assert_eq!($e4.partial_cmp($e5).unwrap(), Ordering::Less);
                assert_eq!($e4.partial_cmp($e6).unwrap(), Ordering::Less);
                assert_eq!($e4.partial_cmp($e7).unwrap(), Ordering::Less);
                assert_eq!($e4.partial_cmp($e8).unwrap(), Ordering::Less);
                assert_eq!($e4.partial_cmp($e9).unwrap(), Ordering::Less);
                assert_eq!($e4.partial_cmp($e10).unwrap(), Ordering::Less);
            }

            #[test]
            fn test_cmp_5() {
                assert_eq!($e5.partial_cmp($e1).unwrap(), Ordering::Greater);
                assert_eq!($e5.partial_cmp($e2).unwrap(), Ordering::Greater);
                assert_eq!($e5.partial_cmp($e3).unwrap(), Ordering::Greater);
                assert_eq!($e5.partial_cmp($e4).unwrap(), Ordering::Greater);
                assert_eq!($e5.partial_cmp($e5).unwrap(), Ordering::Equal);
                assert_eq!($e5.partial_cmp($e6).unwrap(), Ordering::Less);
                assert_eq!($e5.partial_cmp($e7).unwrap(), Ordering::Less);
                assert_eq!($e5.partial_cmp($e8).unwrap(), Ordering::Less);
                assert_eq!($e5.partial_cmp($e9).unwrap(), Ordering::Less);
                assert_eq!($e5.partial_cmp($e10).unwrap(), Ordering::Less);
            }

            #[test]
            fn test_cmp_6() {
                assert_eq!($e6.partial_cmp($e1).unwrap(), Ordering::Greater);
                assert_eq!($e6.partial_cmp($e2).unwrap(), Ordering::Greater);
                assert_eq!($e6.partial_cmp($e3).unwrap(), Ordering::Greater);
                assert_eq!($e6.partial_cmp($e4).unwrap(), Ordering::Greater);
                assert_eq!($e6.partial_cmp($e5).unwrap(), Ordering::Greater);
                assert_eq!($e6.partial_cmp($e6).unwrap(), Ordering::Equal);
                assert_eq!($e6.partial_cmp($e7).unwrap(), Ordering::Less);
                assert_eq!($e6.partial_cmp($e8).unwrap(), Ordering::Less);
                assert_eq!($e6.partial_cmp($e9).unwrap(), Ordering::Less);
                assert_eq!($e6.partial_cmp($e10).unwrap(), Ordering::Less);
            }

            #[test]
            fn test_cmp_7() {
                assert_eq!($e7.partial_cmp($e1).unwrap(), Ordering::Greater);
                assert_eq!($e7.partial_cmp($e2).unwrap(), Ordering::Greater);
                assert_eq!($e7.partial_cmp($e3).unwrap(), Ordering::Greater);
                assert_eq!($e7.partial_cmp($e4).unwrap(), Ordering::Greater);
                assert_eq!($e7.partial_cmp($e5).unwrap(), Ordering::Greater);
                assert_eq!($e7.partial_cmp($e6).unwrap(), Ordering::Greater);
                assert_eq!($e7.partial_cmp($e7).unwrap(), Ordering::Equal);
                assert_eq!($e7.partial_cmp($e8).unwrap(), Ordering::Less);
                assert_eq!($e7.partial_cmp($e9).unwrap(), Ordering::Less);
                assert_eq!($e7.partial_cmp($e10).unwrap(), Ordering::Less);
            }

            #[test]
            fn test_cmp_8() {
                assert_eq!($e8.partial_cmp($e1).unwrap(), Ordering::Greater);
                assert_eq!($e8.partial_cmp($e2).unwrap(), Ordering::Greater);
                assert_eq!($e8.partial_cmp($e3).unwrap(), Ordering::Greater);
                assert_eq!($e8.partial_cmp($e4).unwrap(), Ordering::Greater);
                assert_eq!($e8.partial_cmp($e5).unwrap(), Ordering::Greater);
                assert_eq!($e8.partial_cmp($e6).unwrap(), Ordering::Greater);
                assert_eq!($e8.partial_cmp($e7).unwrap(), Ordering::Greater);
                assert_eq!($e8.partial_cmp($e8).unwrap(), Ordering::Equal);
                assert_eq!($e8.partial_cmp($e9).unwrap(), Ordering::Less);
                assert_eq!($e8.partial_cmp($e10).unwrap(), Ordering::Less);
            }

            #[test]
            fn test_cmp_9() {
                assert_eq!($e9.partial_cmp($e1).unwrap(), Ordering::Greater);
                assert_eq!($e9.partial_cmp($e2).unwrap(), Ordering::Greater);
                assert_eq!($e9.partial_cmp($e3).unwrap(), Ordering::Greater);
                assert_eq!($e9.partial_cmp($e4).unwrap(), Ordering::Greater);
                assert_eq!($e9.partial_cmp($e5).unwrap(), Ordering::Greater);
                assert_eq!($e9.partial_cmp($e6).unwrap(), Ordering::Greater);
                assert_eq!($e9.partial_cmp($e7).unwrap(), Ordering::Greater);
                assert_eq!($e9.partial_cmp($e8).unwrap(), Ordering::Greater);
                assert_eq!($e9.partial_cmp($e9).unwrap(), Ordering::Equal);
                assert_eq!($e9.partial_cmp($e10).unwrap(), Ordering::Less);
            }

            #[test]
            fn test_cmp_10() {
                assert_eq!($e10.partial_cmp($e1).unwrap(), Ordering::Greater);
                assert_eq!($e10.partial_cmp($e2).unwrap(), Ordering::Greater);
                assert_eq!($e10.partial_cmp($e3).unwrap(), Ordering::Greater);
                assert_eq!($e10.partial_cmp($e4).unwrap(), Ordering::Greater);
                assert_eq!($e10.partial_cmp($e5).unwrap(), Ordering::Greater);
                assert_eq!($e10.partial_cmp($e6).unwrap(), Ordering::Greater);
                assert_eq!($e10.partial_cmp($e7).unwrap(), Ordering::Greater);
                assert_eq!($e10.partial_cmp($e8).unwrap(), Ordering::Greater);
                assert_eq!($e10.partial_cmp($e9).unwrap(), Ordering::Greater);
                assert_eq!($e10.partial_cmp($e10).unwrap(), Ordering::Equal);
            }
        };
    }

    gen_test_cmp!(
        &Decimal::<1>::MIN,
        &Decimal::<3>::MIN,
        &Dec!(-34819.003),
        &Dec!(-0.0004),
        &Decimal::<1>::ZERO,
        &Dec!(0.02),
        &Decimal::<5>::ONE,
        &Dec!(17.000000007),
        &Decimal::<1>::MAX,
        &Decimal::<0>::MAX,
    );
}
