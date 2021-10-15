// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

// Implements binary operators "&T op U", "T op &U", "&T op &U"
// based on "T op U" where T and U are Decimal<P> and Decimal<Q>
macro_rules! forward_ref_binop {
    (impl $imp:ident, $method:ident) => {
        impl<'a, const P: u8, const Q: u8> $imp<Decimal<Q>> for &'a Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            Decimal<P>: $imp<Decimal<Q>>,
        {
            type Output = <Decimal<P> as $imp<Decimal<Q>>>::Output;

            #[inline]
            fn $method(self, other: Decimal<Q>) -> Self::Output {
                $imp::$method(*self, other)
            }
        }

        impl<const P: u8, const Q: u8> $imp<&Decimal<Q>> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            Decimal<P>: $imp<Decimal<Q>>,
        {
            type Output = <Decimal<P> as $imp<Decimal<Q>>>::Output;

            #[inline]
            fn $method(self, other: &Decimal<Q>) -> Self::Output {
                $imp::$method(self, *other)
            }
        }

        impl<const P: u8, const Q: u8> $imp<&Decimal<Q>> for &Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            Decimal<P>: $imp<Decimal<Q>>,
        {
            type Output = <Decimal<P> as $imp<Decimal<Q>>>::Output;

            #[inline]
            fn $method(self, other: &Decimal<Q>) -> Self::Output {
                $imp::$method(*self, *other)
            }
        }
    };
}

// Same for ops giving rounded result.
macro_rules! forward_ref_binop_rounded {
    (impl $imp:ident, $method:ident) => {
        impl<'a, const P: u8, const Q: u8, const R: u8>
            $imp<Decimal<Q>, Decimal<R>> for &'a Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
            Decimal<P>: $imp<Decimal<Q>, Decimal<R>>,
        {
            #[inline]
            fn $method(self, other: Decimal<Q>) -> Decimal<R> {
                $imp::$method(*self, other)
            }
        }

        impl<const P: u8, const Q: u8, const R: u8>
            $imp<&Decimal<Q>, Decimal<R>> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
            Decimal<P>: $imp<Decimal<Q>, Decimal<R>>,
        {
            #[inline]
            fn $method(self, other: &Decimal<Q>) -> Decimal<R> {
                $imp::$method(self, *other)
            }
        }

        impl<const P: u8, const Q: u8, const R: u8>
            $imp<&Decimal<Q>, Decimal<R>> for &Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            PrecLimitCheck<{ Q <= MAX_PREC }>: True,
            PrecLimitCheck<{ R <= MAX_PREC }>: True,
            Decimal<P>: $imp<Decimal<Q>, Decimal<R>>,
        {
            #[inline]
            fn $method(self, other: &Decimal<Q>) -> Decimal<R> {
                $imp::$method(*self, *other)
            }
        }
    };
}

// Implements binary operators "&T op U", "T op &U", "&T op &U"
// based on "T op U" where T = Decimal<P> and U is a native int
macro_rules! forward_ref_binop_decimal_int {
    (impl $imp:ident, $method:ident) => {
        forward_ref_binop_decimal_int!(
            impl $imp, $method, u8, i8, u16, i16, u32, i32, u64, i64, i128
        );
    };
    (impl $imp:ident, $method:ident, $($t:ty),*) => {
        $(
        impl<'a, const P: u8> $imp<$t> for &'a Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            Decimal<P>: $imp<$t>,
        {
            type Output = <Decimal<P> as $imp<$t>>::Output;

            #[inline(always)]
            fn $method(self, other: $t) -> Self::Output {
                $imp::$method(*self, other)
            }
        }

        impl<const P: u8> $imp<&$t> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            Decimal<P>: $imp<$t>,
        {
            type Output = <Decimal<P> as $imp<$t>>::Output;

            #[inline(always)]
            fn $method(self, other: &$t) -> Self::Output {
                $imp::$method(self, *other)
            }
        }

        impl<const P: u8> $imp<&$t> for &Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            Decimal<P>: $imp<$t>,
        {
            type Output = <Decimal<P> as $imp<$t>>::Output;

            #[inline(always)]
            fn $method(self, other: &$t) -> Self::Output {
                $imp::$method(*self, *other)
            }
        }

        impl<'a, const P: u8> $imp<Decimal<P>> for &'a $t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            $t: $imp<Decimal<P>>,
        {
            type Output = <$t as $imp<Decimal<P>>>::Output;

            #[inline(always)]
            fn $method(self, other: Decimal<P>) -> Self::Output {
                $imp::$method(*self, other)
            }
        }

        impl<const P: u8> $imp<&Decimal<P>> for $t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            $t: $imp<Decimal<P>>,
        {
            type Output = <$t as $imp<Decimal<P>>>::Output;

            #[inline(always)]
            fn $method(self, other: &Decimal<P>) -> Self::Output {
                $imp::$method(self, *other)
            }
        }

        impl<const P: u8> $imp<&Decimal<P>> for &$t
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            $t: $imp<Decimal<P>>,
        {
            type Output = <$t as $imp<Decimal<P>>>::Output;

            #[inline(always)]
            fn $method(self, other: &Decimal<P>) -> Self::Output {
                $imp::$method(*self, *other)
            }
        }
        )*
    }
}

macro_rules! forward_op_assign {
    (impl $imp:ident, $method:ident, $base_imp:ident, $base_method:ident) => {
        impl<const P: u8, T> $imp<T> for Decimal<P>
        where
            PrecLimitCheck<{ P <= MAX_PREC }>: True,
            Decimal<P>: $base_imp<T, Output = Self>,
        {
            #[inline(always)]
            fn $method(&mut self, other: T) {
                *self = $base_imp::$base_method(*self, other);
            }
        }
    };
}

pub const fn const_max_u8(a: u8, b: u8) -> u8 {
    if a > b {
        a
    } else {
        b
    }
}

pub const fn const_sum_u8(a: u8, b: u8) -> u8 {
    a + b
}

mod add_sub;
mod checked_add_sub;
mod checked_div;
mod checked_mul;
mod cmp;
mod div;
pub mod div_rounded;
mod mul;
pub mod mul_rounded;
mod rem;
