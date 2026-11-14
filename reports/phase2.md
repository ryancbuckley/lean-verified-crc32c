# Phase 2 report: portable path

Status: exit criteria met on AArch64 (Apple M4). x86-64 numbers wait for real hardware.

## What is proven

`MemcpyCrc32c/Portable.lean` and `MemcpyCrc32c/Word64.lean`, with no `sorry`, `admit`, `axiom`, `native_decide` or `bv_decide`.

| Theorem | Statement |
| --- | --- |
| `rawExtendPortable_eq` | For any in-bounds `off`, `len`: the portable kernel on `a[off, off+len)` equals the bitwise reference on those bytes. This is `fast_eq_ref`. |
| `extendPortable_eq_extend` | `extendPortable c a = extend c a` for every `c` and `a`. |
| `extendPortable_eq_spec` | `extendPortable c a = Spec.extend c a` (the polynomial spec). |
| `zero6_209`, `zero6_290`, `zero4_5275` | The zero polynomials are multiples of `G`, by kernel evaluation (`decide +kernel`). |
| `modByMonic_add_zeroPoly_mul` | The core lemma: adding a multiple of a zero polynomial leaves the remainder unchanged. |

Out-of-bounds behaviour: `rawExtendPortable` takes a proof of `off + len ≤ a.size`. No panics, no truncation; the emitted loops have no bounds checks.

`#print axioms rawExtendPortable_eq`, `#print axioms extendPortable_eq_extend`, `#print axioms extendPortable_eq_spec`: **`propext`, `Classical.choice`, `Quot.sound` only** (zero `bv_decide` axioms; all 64-bit/32-bit byte-assembly lemmas in `MemcpyCrc32c/Word64.lean` are proven directly in the kernel via `BitVec.eq_of_getLsbD_eq`).

## The kernel

Three tiers over plain `UInt64`/`UInt32` register operations, with zero scratch memory and zero trusted C:

1. **Short inputs (`len < 40`): packed slicing-by-8 (`sliceLoop`).** The lookup table is stored as an 8 KiB `ByteArray` (`sliceTableBytes`, half the L1D footprint of a boxed `Array UInt32`, with zero per-lookup reference-count branches) ordered so lanes `0..7` correspond to `7 - k` trailing zero bytes. Each 8-byte word is loaded as two unboxed 32-bit halves (`load32`) and stepped via `stepWordT32`, merging every table lookup into a single unboxed `ldr w` with no byte-repacking instructions.
2. **Medium inputs (`40 ≤ len < 8192`): single-stream Chorba reduction (`fold209`).** Reduction by `Z = X^209 + X^144 + X^54 + X^39 + X^14 + 1` (`zero6_209`). Each 64-bit message word is cancelled and re-injected 65, 155, 170, 195 and 209 bits later across four pending `UInt64` words. The final four words (`finish209`) and up to seven tail bytes (`bytesLoop`) are finished via `sliceTableBytes`.
3. **Large inputs (`len ≥ 8192`): 4-stream interleaved Chorba reduction (`fold209_4x`).** Single-stream `fold209` has a 2-cycle shift-XOR recurrence (`n1' = n2 ^^^ (v <<< 1)`), capping single-stream throughput around 7.5 GB/s on M4. `fold209_4x` splits the input into four contiguous streams of `ws = len / 32` words (`L = 8 * ws` bytes), folds all 16 pending `UInt64` state words in GP registers in lockstep, finishes each stream's last 4 words (`finish209Out`), combines the four stream CRCs algebraically via `mulMod` and `powModU64 x64`, and finishes the remaining `0..31` bytes via `sliceLoop`.

Entry overhead: `rawExtendPortable` checks `a.size ≤ 0x7FFFFFFF` as a single immediate scalar comparison on the hot path and outlines the `≥ 2 GiB` fallback into `@[noinline] def rawExtendPortableCold`, avoiding both `USize.size`'s `lean_obj_once` / `lean_nat_big_lt` call and callee-saved register spills on short inputs.

## Measured throughput

Apple M4, unloaded P-core (after a ~30 ms warm-up to avoid initial macOS E-core placement), CRC only, GB/s, median of 9 (`tests/BenchPortable.lean`, `bench/proto.c`). Quick check rather than the full Phase 6 benchmarking protocol (no cache flushing, aligned buffers only).

| Size | Lean portable (verified) | C `reg209_4x` | C slicing-by-8 | Lean vs C `slice8` |
| --- | --- | --- | --- | --- |
| 16 B | 2.46 | 1.81 | 2.12 | 1.16× |
| 64 B | 3.82 | 3.70 | 2.25 | 1.70× |
| 256 B | 6.12 | 5.94 | 2.22 | 2.76× |
| 1 KiB | 7.12 | 7.13 | 2.26 | 3.15× |
| 4 KiB | 7.35 | 7.47 | 2.28 | 3.22× |
| 64 KiB | 10.89 | 11.17 | 2.29 | 4.76× |
| 1 MiB | 11.41 | 11.05 | 2.24 | 5.09× |
| 64 MiB | 11.39 | 11.02 | 2.28 | 5.00× |

The verified Lean portable path now beats C slicing-by-8 at **every** tested size from 16 B (+16%) through 64 MiB (5.0×), matches hand-written C `reg209_4x` within measurement noise, and reaches ~97% of single-stream AArch64 hardware `crc32cx` (`11.77 GB/s` after P-core warm-up, `10.8–10.9 GB/s` cold).

## Tested

`tests/run_diff.sh` checks both `extend` and `extendPortable` against abseil's `ExtendCrc32c` and `MemcpyCrc32c` across lengths from 0 to 20,191 bytes (exercising `sliceLoop`, `fold209`, and `fold209_4x`): 720,000 cases over six seeds, no mismatch.

## Trusted

Same as Phase 1: only the Lean kernel and Mathlib's polynomial definitions for the theorems (`propext`, `Classical.choice`, `Quot.sound`), plus the Lean compiler, runtime and clang for native execution. Zero `bv_decide` axioms and zero trusted C.

## Decisions taken

- **Zero polynomials.** `zero6_209` is the lowest-degree 6-term multiple (4-word window, first move 65 bits). `zero6_290` (`X^290 + X^136 + X^113 + X^107 + X^32 + 1`) is also certified as the lowest-degree 6-term multiple whose first gap exceeds two words (`n1' = n2` in a 5-word window).
- **4-stream register kernel before scratch-buffer kernel.** Interleaving 4 streams of `Z_209` breaks the `n1` recurrence while keeping all 16 state words in GP registers with zero scratch memory and zero allocations.
- **Packed `ByteArray` table for `sliceLoop` and finishers.** Halves table cache footprint to 8 KiB and avoids `Array UInt32` element boxing/RC checks.
- **Two-tier size guard (`a.size ≤ 0x7FFFFFFF`, then `a.size < USize.size` outlined).** Keeps short calls spill-free while remaining total and fast on `≥ 2 GiB` buffers on 64-bit platforms.

## Not done

- **Word-aligned scratch-buffer kernel (`Z^64`).** Moves whole words with no shifts (15.0 GB/s in `bench/proto.c` at 1 MiB), at the cost of a ~1.7 KiB scratch buffer. Optional if additional portable large-buffer throughput beyond 11.4 GB/s is desired.
- **Fused copy** (theorem 6) is Phase 5.
- **x86-64 and WebAssembly** measurements on real hardware.

## Open questions from the brief

- **Does Chorba's gain hold for CRC32C?** Yes: 3.2× single-stream at 4 KiB and 5.0× four-stream from 64 KiB up over C slicing-by-8 on Apple M4.
- **Crossover.** Packed `sliceLoop` + `extendPortable` beats C slicing-by-8 even at 16 bytes; single-stream `fold209` takes over at 40 bytes, and 4-stream `fold209_4x` takes over at 8 KiB.

## Emitted code, checked

Read from `.lake/build/ir/MemcpyCrc32c/Impl/Portable.c` and disassembled `.lake/build/ir/MemcpyCrc32c/Impl/Portable.c.o.export`:
- `extendPortable` prologue is a single `stp x29, x30` frame setup with an immediate `a.size ≤ 0x7FFFFFFF` compare and zero callee-saved spills.
- `fold209` is one 8-byte load plus ARM64 fused shifted-EOR instructions, zero bounds checks, zero calls, zero RC ops.
- `fold209_4x` holds all 16 `UInt64` state words and stream pointers in GP registers (`x4..x28`, `x30`) with zero stack spills inside the hot loop (58 instructions per 32 bytes).
- `mulMod` and `powModU64` in `Impl/Arith.lean` compile to zero-stack-frame leaf loops (`mulMod` auto-unrolled 4× by clang).

## Spike for Phase 3 and 4 (not product code)

`spike/HwSpike.lean` calls the AArch64 CRC32C instruction from a Lean loop through `@[extern c inline "__builtin_arm_crc32cd(#1, #2)"]`, with `stepWord` as the Lean reference body. It agrees with the proven portable path and runs at 10.9–11.8 GB/s single-stream at 1 MiB (the instruction's 3-cycle latency bound on M4). So kernels over scalar-typed inline intrinsics can stay in Lean and compile to tight code.
