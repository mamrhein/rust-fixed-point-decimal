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
#![feature(associated_type_bounds)]

use criterion::{criterion_group, criterion_main, Criterion};
use order::{Order, OrderBuilder, OrderCalculator, ORDER_DETAILS};
use rust_fixed_point_decimal::Decimal;

pub fn criterion_benchmark(c: &mut Criterion) {
    let order = Order::<Decimal<2>>::build_order(&ORDER_DETAILS);
    c.bench_function("fpd_calc_order", |b| b.iter(|| order.calc_order()));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
