use criterion::{criterion_group, criterion_main, Criterion};
use peek_again::Peekable;
use core::hint::black_box;

// other benchmarks will be too easy for modern CPUs, here
// we will try and coerce pipeline stalls / bubbles.

#[derive(Copy, Clone, Default, Debug)]
#[repr(transparent)]
struct StallMaker {
    state: u32
}

impl Iterator for StallMaker {
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // xorshift 32 should be confusing enough.
        let mut x = self.state;
        x ^= x.wrapping_shl(13);
        x ^= x.wrapping_shr(17);
        x ^= x.wrapping_shl(5);
        self.state = x;
        // we'll just return 0 or 1 to make condition hit 
        // frequently
        Some(black_box(x & 1))
    }
}

fn benchmark(c: &mut Criterion) {
    let inner = StallMaker::default();
    let mut std   = inner.peekable();
    let mut again = Peekable::new(inner);

    c.bench_function("std-next-if-unpredictable", |b| {
        b.iter(|| {
            let res = std.next_if(|item| item == &1);
            black_box(res)
        })
    });

    c.bench_function("again-next-if-unpredictable", |b| {
        b.iter(|| {
            let res = again.next_if(|item| item == &1);
            black_box(res)
        })
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);

