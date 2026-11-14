# Phase 2 report: portable path

Status: exit criteria met on AArch64 (Apple M4). x86-64 numbers wait for real hardware.

## What is proven

`MemcpyCrc32c/Portable.lean`, no `sorry`, `admit`, `axiom` or `native_decide`.

| Theorem | Statement |
| --- | --- |
| `rawExtendPortable_eq` | For any in-bounds `off`, `len`: the portable kernel on `a[off, off+len)` equals the bitwise reference on those bytes. This is `fast_eq_ref`. |
| `extendPortable_eq_extend` | `extendPortable c a = extend c a` for every `c` and `a`. |
| `extendPortable_eq_spec` | `extendPortable c a = Spec.extend c a` (the polynomial spec). |
| `zero6_209`, `zero4_5275` | The zero polynomials are multiples of `G`, by kernel evaluation. |
| `modByMonic_add_zeroPoly_mul` | The core lemma: adding a multiple of a zero polynomial leaves the remainder unchanged. |

Out-of-bounds behaviour: `rawExtendPortable` takes a proof of `off + len ≤ a.size`. No panics, no truncation; the emitted loop has no bounds checks.

`#print axioms rawExtendPortable_eq`: `propext`, `Classical.choice`, `Quot.sound`, plus two quarantined `bv_decide` axioms, `BvDecide.word64_bytes._native.bv_decide.ax_1_5` and `BvDecide.word64_eq_xor._native.bv_decide.ax_1_5`. On Lean 4.35 `bv_decide` records one named axiom per lemma, not `Lean.ofReduceBool`. A third quarantined lemma, `shl24_eq_lowByte`, was closed by `bv_decide`'s rewriting alone and adds no axiom. All three are in `MemcpyCrc32c/BvDecide/Word64.lean`. Phase 1 theorems are unchanged and still depend on the three standard axioms only.

## The kernel

Reduction by `Z = X^209 + X^144 + X^54 + X^39 + X^14 + 1`. Each 64-bit message word is cancelled and re-injected 65, 155, 170, 195 and 209 bits later, which lands in the next four words. Those four pending words are the entire state, so the loop only reads memory. The last four words and up to seven tail bytes are finished by slicing-by-8 tables; inputs under 40 bytes use slicing-by-8 throughout. The tables are defined from the bitwise reference and built at start-up, so their correctness is by definition.

The 64-bit load is assembled from eight byte reads; clang merges them into one load. No trusted C primitive was added.

## Measured throughput

Apple M4, one run, CRC only, GB/s, median of 9. This is a quick check (`tests/BenchPortable.lean`, `bench/proto.c`), not the benchmarking protocol: no thread pinning, no cache flushing, aligned buffers only.

| Size | Lean portable (verified) | C slicing-by-8 | Ratio |
| --- | --- | --- | --- |
| 16 B | 1.76 | 2.03 | 0.87× |
| 64 B | 3.02 | 2.26 | 1.3× |
| 256 B | 5.69 | 2.30 | 2.5× |
| 1 KiB | 6.99 | 2.35 | 3.0× |
| 4 KiB | 7.47 | 2.34 | 3.2× |
| 64 KiB | 7.54 | 2.37 | 3.2× |
| 1 MiB | 7.45 | 2.31 | 3.2× |
| 64 MiB | 7.47 | 2.33 | 3.2× |

The Lean build is within 5% of the same kernel hand-written in C (7.8 GB/s at 1 MiB). At 16 bytes it is 13% slower than C slicing-by-8; the cost is call overhead, not the algorithm.

## Tested

`tests/run_diff.sh` now also checks `extendPortable` against abseil's `ExtendCrc32c`: 360,000 cases over three seeds, no mismatch.

## Trusted

As Phase 1, plus: the Lean compiler for the `bv_decide` certificate check (two lemmas), and for the benchmark and differential binaries the Lean compiler, runtime and clang. No trusted C.

## Decisions taken

- **Zero polynomial.** The lowest-degree 6-term multiple. Its smallest move is 65 bits, just over one word, so a word never feeds back into itself.
- **Register kernel first.** It needs no scratch memory, which suits Lean's code generation, and it was proven before any tuning.
- **Tables for the finisher** were added as a separate commit after the bit-at-a-time finisher was proven; `rawExtendPortable_eq` did not change.
- **`a.size < USize.size` is checked once at run time.** Lean core has no theorem that byte arrays fit the address space. The other branch falls back to the reference and is unreachable in practice.

## Not done

- **Word-aligned kernel.** `Z^64` moves whole words with no shifts: 15.0 GB/s in the C prototype at 1 MiB, twice the register kernel. It needs a 209-word history buffer, so it depends on how well Lean can write to scratch memory. Not ported or proven yet.
- **Hand unrolling.** Not tried; the register kernel is limited by its operation count, not by a dependency chain.
- **Fused copy** (theorem 6) is Phase 5.
- **x86-64 and WebAssembly** measurements.

## Open questions from the brief

- **Does Chorba's gain hold for CRC32C?** Yes on this machine, despite needing six terms where CRC32 needs five: 3.2× over slicing-by-8 from 4 KiB up, against the paper's roughly 2× for CRC32.
- **Crossover.** Between 16 and 64 bytes against slicing-by-8.
