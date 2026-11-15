# Phase 4 and 5 report: hardware kernels, fused copy and dispatch (AArch64 track)

Status: done on AArch64 (Apple M4), as a quick check rather than the benchmarking protocol. Nothing here has run on real x86-64 hardware. The copy is not interleaved with the CRC inside the loop; see "Decisions taken".

## What is proven

No `sorry`, `axiom`, `native_decide` or `bv_decide`. `#print axioms` shows `propext`, `Classical.choice`, `Quot.sound` for all 56 audited theorems. The hardware results rest on the eight trusted bindings in `lean-simd-models/SimdModels/Trusted.lean`, which `#print axioms` cannot show.

| Theorem | Statement |
| --- | --- |
| `rawExtendHw_eq`, `extendHw_eq_spec` | The hardware kernel (CRC32C-instruction streams plus PMULL folding) equals the reference on any in-bounds range: `fast_eq_ref`. |
| `memcpyCrc32cPortable_spec`, `memcpyCrc32cHw_spec` | Theorem 6 for each path. |
| `memcpyCrc32c_spec` | The headline. The dispatched `memcpyCrc32c` returns `(src.copySlice sOff dst dOff n, Spec.extend init (src.extract sOff (sOff + n)))`. |
| `memcpyCrc32cK_spec` | The same for the continuation-passing entry point. |
| `extendCrc32c_eq_spec`, `computeCrc32c_eq_spec` | The dispatched CRC entry points equal the spec. |

Dispatch correctness holds for either answer of the CPU-feature test, because the test is an `opaque` binding and no proof can depend on its value.

## Trusted

Eight bindings, one file:

- Six instruction bindings (CRC32C on 8/16/32/64 bits, carry-less multiply low and high).
- `loadU64LE`, a C unaligned 64-bit load. Its bounds are guaranteed only by erased proofs. It is load-bearing: with the pure-Lean load the hardware kernel runs at 14.5 GB/s at 1 MiB, with it 58.6 GB/s.
- `cpuHasCrcClmul`, the CPU-feature test. A wrong `true` would fault at run time, not give a wrong answer.

The copy itself is Lean core's `ByteArray.copySlice`, so it adds runtime trust but no new code of ours.

## Measured throughput

Apple M4, idle, GB/s, median of 9. Quick checks (`tests/BenchMemcpy.lean`, `tests/BenchPortable.lean`, `bench/absl_quick.cc`): no thread pinning, no cache flushing, aligned buffers only.

CRC only:

| Size | Lean hardware path | `absl::ExtendCrc32c` | Ratio |
| --- | --- | --- | --- |
| 16 B | 8.2 | 8.6 | 0.95 |
| 256 B | 14.7 | 15.1 | 0.98 |
| 4 KiB | 44.2 | 45.8 | 0.97 |
| 1 MiB | 58.6 | 64.5 | 0.91 |
| 64 MiB | 57.0 | 64.3 | 0.89 |

Copy and CRC:

| Size | `memcpyCrc32cK` (dispatched, hardware) | `memcpyCrc32c` (pair-returning) | Dispatched with hardware disabled | `absl::MemcpyCrc32c` |
| --- | --- | --- | --- | --- |
| 16 B | 3.0 | 1.4 | 2.3 | 4.5 |
| 64 B | 9.6 | 5.3 | not measured | 9.3 |
| 256 B | 14.0 | 12.4 | not measured | 13.6 |
| 1 KiB | 23.6 | 20.5 | not measured | 18.8 |
| 4 KiB | 31.9 | 30.2 | 6.6 | 20.4 |
| 1 MiB | 34.0 | 31.8 | 9.6 | 20.7 |
| 64 MiB | 23.4 | 23.5 | not measured | 20.8 |

Against the brief's goals on this machine: the hardware path is at or above `absl::MemcpyCrc32c` from 64 B up and 1.5× behind at 16 B. The portable path is 2.2× behind at 1 MiB, against a goal of 1.5×.

## Tested

- `tests/run_diff.sh`: every path and the dispatched entry points against abseil, including that the copy is exact and leaves the rest of the destination untouched. Passes with the hardware path available and with `SIMDMODELS_DISABLE_HW=1`.

## Decisions taken

- **The copy is not interleaved with the CRC.** `copySlice` copies the range and the proven kernel then checksums the source. This beats abseil's interleaved routine here, needs no trusted store primitive, and makes theorem 6 immediate.
- **Block-level fusion was tried and dropped.** Copying and checksumming in 512 KiB blocks was implemented and proven. In a fair alternating run at 64 MiB it was slightly slower (about 22–23 against 24.5 GB/s) and it cost throughput at small sizes. An earlier quick experiment that suggested a 25% gain was wrong, most likely first-touch page effects.
- **A continuation-passing entry point.** Returning a pair allocates on every call: 16–17 ns per call at 16 B against about 5 ns without it. `memcpyCrc32cK` avoids it and has its own theorem.
- **Feature detection is `opaque`.** A binding with a Lean body would let proofs learn a value the CPU may contradict.

## Not done

- x86-64: no kernel has run on real hardware, and the bindings will not inline on x86-64 until the kernel modules are built with the instruction-set flags.
- Checking the generated assembly of the fused path instruction by instruction (done for the kernels, not for `memcpyCrc32c`).
- The portable path's gap to abseil.
- Dispatch on a CPU that really lacks the features; only the environment override was used.
