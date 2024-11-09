use criterion::{criterion_group, criterion_main, Criterion};
use peek_again::Peekable;
use core::hint::black_box;

#[derive(Copy, Clone, Default, Debug)]
struct AlwaysOne;

impl Iterator for AlwaysOne {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        Some(black_box(1))
    }
}

fn benchmark(c: &mut Criterion) {
    let inner = AlwaysOne::default();
    let mut std   = inner.peekable();
    let mut again = Peekable::new(inner);

    c.bench_function("std-next", |b| {
        b.iter(|| {
            let res = std.next().unwrap();
            assert_eq!(black_box(res), 1);
        })
    });

    c.bench_function("again-next", |b| {
        b.iter(|| {
            let res = again.next().unwrap();
            assert_eq!(black_box(res), 1);
        })
    });

    c.bench_function("std-next-if", |b| {
        b.iter(|| {
            let res = std.next_if(|item| item == &1).unwrap();
            assert_eq!(res, black_box(1));
        })
    });

    c.bench_function("again-next-if", |b| {
        b.iter(|| {
            let res = again.next_if(|item| item == &1).unwrap();
            assert_eq!(res, black_box(1));
        })
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
