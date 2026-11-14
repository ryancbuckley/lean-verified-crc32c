# Phase 3 report: SIMD model library (and Phase 4 AArch64 CRC kernel)

Status: AArch64 exit criteria met; Intel SDM authoritative cross-check met via universal kernel proofs (`SimdModels/IntelSdm.lean`); x86-64 functional lowering verified under Rosetta 2, awaiting real x86-64 hardware. On the Phase 4 AArch64 track, `extendHw` is upgraded to a verified 3-regime hybrid `CRC32CX + PMULL` 64-byte dot-product kernel reaching 82%–104% of `absl::ExtendCrc32c` across 16 B–64 MiB on Apple M4.

## What exists

`lean-simd-models/` is a separate Lake package that the CRC package depends on.

| Part | File | Contents |
| --- | --- | --- |
| Views | `SimdModels/Poly.lean`, `PolyShift.lean` | `ofBits`, `polyR` (reflected), `polyN` (natural), shift lemmas. Moved unchanged from the CRC package, which re-exports them; `Spec.lean` is byte-for-byte identical to Phase 1. |
| Models | `SimdModels/Models.lean` | `V128` (`BitVec 128`) views (`ofHalves`, `lo64`, `hi64`, `lane8/16/32/64`, `veorq`, `vextq`, `vmull_p64`, `vmull_high_p64`, `clmulepi64`, `vld1q`), scalar CRC32C on 8/16/32/64-bit operands, 64×64 carry-less multiply (`clmulLo`, `clmulHi`), and bounds-checked unaligned 64-bit little-endian load (`loadU64LE`). Imports only Lean core (`Init`). |
| Trusted bindings | `SimdModels/Trusted.lean`, `c/simd_shim.h` | Seven scalar-typed `@[extern]` bindings backed by `<stdint.h>`-typed, C++-safe `static inline` shims with per-function `__attribute__((__target__(...)))` guards (`crc,aes` on AArch64; `sse4.2,pclmul` on x86-64). |
| Vector & algebraic semantics | `SimdModels/V128.lean`, `SimdModels/Semantics.lean` | `V128` lane/shuffle/load lemmas and `GF(2)[X]` specs for CRC32C and carry-less multiplication (both natural and bit-reflected). |
| Intel SDM cross-check | `SimdModels/IntelSdm.lean` | Direct transcription of Intel SDM Vol. 2A/2B `CRC32` and `PCLMULQDQ` Operation pseudocode, with universal kernel proofs of equality to `SimdModels.Model`. |

## What is proven

No `sorry`, `axiom`, `native_decide`, or `bv_decide` in any Phase 3 or Phase 4 module. `#print axioms` (`MemcpyCrc32c/Axioms.lean`) shows only `propext`, `Classical.choice`, `Quot.sound` (or subset) for every theorem listed.

| Theorem | Statement |
| --- | --- |
| `crc32c_spec` | The CRC32C instruction model on a `size`-bit operand computes `(acc·X^size + val·X^32) mod castagnoli` in the reflected view. |
| `clmul_spec`, `clmulepi64_spec` | Natural-view carry-less product specs for `clmulLo`/`clmulHi` and 128-bit `clmulepi64`. |
| `clmul_spec_reflected`, `clmulepi64_spec_reflected` | Bit-reflected carry-less product specs: `lo·X^64 + hi = X·a·b`. |
| `V128.ofHalves_lo_hi`, `V128.lane8_vextq`, `V128.lane8_vld1q` | 128-bit half round-trip, byte-extract (`EXT`/`PALIGNR`), and unaligned 128-bit load byte-lane specs. |
| `IntelSdm.crc32_u8/16/32/64_eq`, `crc32_r64_eq`, `clmulepi64_eq` | Universal equality between Intel SDM Vol. 2A/2B Operation pseudocode and `SimdModels.Model` across all operands and `imm8` selectors. |
| `G_eq_castagnoli` | The manuals' constant `0x1EDC6F41` and the frozen spec's term-by-term `G` are the same polynomial. |
| `crc32c_u64_eq`, `crc32c_u32_eq`, `crc32c_u16_eq`, `crc32c_u8_eq` | All four CRC32C instruction bindings equal the reference's `stepWord`, `stepU32`, `stepU16`, and `stepByte`. |
| `loadU64LE_eq_load64`, `R128_clmul` | Unaligned 64-bit load equals byte-assembled `load64`; reflected 128-bit carry-less multiply computes `R a · (X · R b)` in `AdjoinRoot G`. |
| `rawExtendHw_eq`, `extendHw_eq_extend`, `extendHw_eq_spec` | The 3-regime hybrid hardware CRC32C kernel equals the bitwise reference and frozen polynomial spec on every input. |

## Validation

Details and raw output are in `lean-simd-models/validation/`.

| Check | AArch64 | x86-64 |
| --- | --- | --- |
| Hardware differential test | Pass: 2,080,000 pairs per binding across all 7 bindings on an Apple M4, no mismatch | Not run on real hardware. Byte-identical to AArch64 across 232,960,000 output bytes (all 7 bindings + 7 `PCLMULQDQ` `imm8` selectors) under Rosetta 2 |
| Authoritative cross-check | Pass: 100,720 vectors from Arm's machine-readable ASL, executed by ASLp on the real opcodes | Pass: universal Lean kernel proof against Intel SDM Vol. 2A/2B Operation pseudocode (`SimdModels/IntelSdm.lean`) |

## Trusted

- Each of the seven bindings in `SimdModels/Trusted.lean`: that the compiler lowers the C shim in `c/simd_shim.h` to the intended unaligned load or instruction, that `lean_sarray_cptr(a) + off` points to `off..off+8` within a `ByteArray` when `off.toNat + 8 ≤ a.size` and `a.size < USize.size`, and that the hardware executes the instruction as modeled.
- `scripts/check_trusted.sh` strips Lean line/nested comments, strings, and char literals before scanning every `.lean` file in the repository, failing on any `extern` outside `SimdModels/Trusted.lean` or any `implemented_by`, `csimp`, `axiom`, `sorry`, `admit`, `native_decide`, `bv_decide` (outside `BvDecide/`), `unsafe`, or `skipKernelTC`.
- For the Arm cross-check: ASLp's interpreter and its bundled copy of Arm's specification.

## Decisions taken

- **Scalar-typed bindings + proof-only `V128` views.** Lean has no unboxed 128-bit value, so executable bindings take and return `UInt32`/`UInt64`/`USize`, while `V128` (`BitVec 128`) views and lemmas in `SimdModels/Models.lean` and `SimdModels/V128.lean` provide lane/vector reasoning without heap boxing.
- **Bounds-checked `loadU64LE` binding.** Lean's `lean_sarray_object` declares `uint8_t m_data[0]`, preventing Clang from merging 8 separate `ByteArray.uget` calls across `[0 x i8]` bounds; `loadU64LE` takes proof witnesses `a.size < USize.size` and `off.toNat + 8 ≤ a.size` and lowers to a single unaligned 64-bit `ldr`/`movq` (or paired `ldp` / 128-bit `ldur q`).
- **Typed, target-guarded C shims.** `c/simd_shim.h` uses `static inline` functions with explicit `__attribute__((__target__(...)))` attributes so callers compile cleanly under both C11 and C++17 even without global `-msse4.2 -mpclmul` or `-march=armv8-a+crc+crypto` flags.

## Not done

- x86-64 execution and benchmarking on real Intel/AMD hardware.
- `V256` and `VPCLMULQDQ` / AVX-512 models (recorded follow-up in the brief).
- Fused `MemcpyCrc32c` copy-and-CRC kernel, runtime CPU feature dispatch, and C ABI wrapper (Phases 5–6).

## Phase 4, AArch64 track (`extendHw`)

`MemcpyCrc32c/Impl/HwCombine.lean` and `MemcpyCrc32c/Impl/Hw.lean` implement a verified 3-regime hardware CRC32C kernel, proven equal to the frozen spec in `MemcpyCrc32c/HwKernel.lean`:

1. **`< 96 B` (`hwLoop`)**: single-stream `CRC32CX` (`16 B/iter`) with loop-free `8/4/2/1` tail (`CRC32CX`/`CRC32CW`/`CRC32CH`/`CRC32CB`).
2. **`96 .. 767 B` (`rawExtendHw3`)**: 3-way `CRC32CX` (`48 B/iter`) combined in 2 hardware `PMULL + CRC32CX` steps (`combine3`) via a packed 2 KiB shift table (`hwShiftSmallBytes`).
3. **`≥ 768 B` (`hwFold6`)**: 6-way hybrid `3 × CRC32CX + 3 × PMULL` **64-byte dot-product** folding (`384 B/iter`), updating each `PMULL` stream accumulator once per 64 bytes (`a · X^512 + w0..w1 · X^384 + w2..w3 · X^256 + w4..w5 · X^128 + w6..w7`) so memory words feed `pmull.1q` + `eor3.16b` directly from SIMD loads while hiding Clang 23's scalar `uint64_t` loop-PHI latency behind 24 `CRC32CX` instructions, with `< 384 B` remainders ≥ 96 B routed through `rawExtendHw3` and stream lengths ≥ 4 KiB (`ws ≥ 512`) combined via hardware `PMULL + CRC32CX` square-and-multiply (`hwPowGo`).

Quick throughput check on an idle Apple M4, GB/s, median of 9 (unboxed Lean calls vs `absl` built `-O2 -DNDEBUG` on the same machine):

| Size | Lean `extendHw` (verified) | Lean `extendPortable` (verified) | `absl::ExtendCrc32c` | `absl::MemcpyCrc32c` | `memcpy` |
| --- | --- | --- | --- | --- | --- |
| 16 B | 7.87 | 2.43 | 8.83 | 4.70 | 8.83 |
| 64 B | 10.03 | 3.59 | 9.68 | 9.97 | 43.45 |
| 256 B | 14.60 | 6.25 | 14.98 | 14.57 | 94.37 |
| 1 KiB | 24.55 | 6.92 | 24.03 | 19.98 | 110.10 |
| 4 KiB | 44.59 | 7.40 | 46.85 | 22.17 | 114.03 |
| 64 KiB | 55.27 | 11.11 | 67.11 | 22.77 | 82.27 |
| 1 MiB | 57.07 | 11.46 | 66.80 | 22.92 | 74.93 |
| 64 MiB | 56.68 | 10.98 | 65.25 | 23.11 | 46.32 |
