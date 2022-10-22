use criterion::{black_box, criterion_group, criterion_main, Bencher, Criterion, BatchSize};
use heapz::{Heap, RankPairingHeap};

fn is_empty_benchmark(b: &mut Bencher) {}

fn pop_benchmark(b: &mut Bencher) {
    b.iter_batched(
        || {
            let arr = vec![1, 3, 5, -2, 6, -7, 9, 10, 13, 4, 12, 115, 500, 334, 67, 334];
            let mut heap = RankPairingHeap::multi_pass_min2();
            arr.iter()
                .for_each(|num| heap.push(black_box(*num), black_box(*num)));
            (heap, arr.len())
        },
        |(mut heap, len)| {
            for _ in 0..len {
                let _ = heap.pop();
            }
        },
        BatchSize::SmallInput
    );
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("pop", pop_benchmark);
}

criterion_group!(rank_pairing_heap, criterion_benchmark);
criterion_main!(rank_pairing_heap);
