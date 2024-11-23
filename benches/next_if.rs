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
    let mut again = Peekable::new(inner);

    c.bench_function("again-next-if", |b| {
        b.iter(|| {
            let res = again.next_if(|item| item == &1);
            assert_eq!(res, black_box(Some(1)));
        })
    });

    c.bench_function("again-next-if-wrong", |b| {
        b.iter(|| {
            let res = again.next_if(|item| item == &2);
            assert!(black_box(res).is_none());
        })
    });

    // with this usage, this will outperform next_if
    c.bench_function("next-if-via-consume", |b| {
        b.iter(|| {
            let peek = again.peek();
            if peek == Some(&1) {
                assert_eq!(peek.consume(), black_box(Some(1)));
            }
        })
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);

