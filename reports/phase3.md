# Phase 3 report: SIMD model library

Status: AArch64 exit criteria met. x86-64 is not: it has no real-hardware run and no authoritative cross-check yet. Work on the AArch64 track of Phase 4 has started ahead of the x86-64 half, because x86-64 hardware is not available.

## What exists

`lean-simd-models/` is a separate Lake package that the CRC package depends on.

| Part | File | Contents |
| --- | --- | --- |
| Views | `SimdModels/Poly.lean`, `PolyShift.lean` | `ofBits`, `polyR` (reflected), `polyN` (natural), shift lemmas. Moved unchanged from the CRC package, which re-exports them; `Spec.lean` is byte-for-byte identical. |
| Models | `SimdModels/Models.lean` | CRC32C on 8/16/32/64-bit operands and 64×64 carry-less multiply, written in the shape of Arm's pseudocode. Imports only Lean core. |
| Trusted bindings | `SimdModels/Trusted.lean`, `c/simd_shim.h` | Six scalar-typed bindings, each one macro that calls one instruction. The only `@[extern]` declarations in the project. |
| Semantics | `SimdModels/Semantics.lean` | The lemmas below. |

## What is proven

No `sorry`, `axiom`, `native_decide` or `bv_decide`. `#print axioms` shows `propext`, `Classical.choice`, `Quot.sound` for every theorem listed.

| Theorem | Statement |
| --- | --- |
| `crc32c_spec` | The CRC32C instruction model on a `size`-bit operand computes `(acc·X^size + val·X^32) mod castagnoli`, in the reflected view. |
| `clmul_spec` | The two halves of the carry-less product multiply the natural views: `lo + hi·X^64 = a·b`. |
| `clmul_spec_reflected` | On bit-reflected operands: `lo·X^64 + hi = X·a·b`. |
| `G_eq_castagnoli` | The manuals' constant `0x1EDC6F41` and the spec's term-by-term `G` are the same polynomial. |
| `crc32c_u64_eq`, `crc32c_u8_eq` | The 64-bit and 8-bit instruction bindings equal the reference's `stepWord` and `stepByte`. |

## Validation

Details and raw output are in `lean-simd-models/validation/`.

| Check | AArch64 | x86-64 |
| --- | --- | --- |
| Hardware differential test | Pass: 2,080,000 pairs per binding on an Apple M4, no mismatch | Not run on real hardware. Byte-identical to the AArch64 results on 1,040,000 pairs under Rosetta 2 |
| Authoritative cross-check | Pass: 100,720 vectors from Arm's machine-readable ASL, executed by ASLp on the real opcodes | Outstanding (Intel Intrinsics Guide pseudocode) |

## Trusted

- Each of the six bindings: that the compiler lowers the builtin to the named instruction, and that the instruction behaves as its model says. This trust is invisible to `#print axioms`. `Trusted.lean` is its record, and `scripts/check_trusted.sh` fails if `extern`, `implemented_by`, `axiom`, `sorry` or `native_decide` appears in any other file.
- For the Arm cross-check: ASLp's interpreter and its bundled copy of Arm's specification.

## Decisions taken

- **Scalar-typed bindings.** Lean has no unboxed 128-bit value, so the bindings take and return `UInt32`/`UInt64`. Carry-less multiply is two bindings, low and high half; clang merges them into one `PMULL`. The 128-bit views are used in proofs only.
- **One model per instruction semantics, bound on both architectures.** Arm's `CRC32C*` and x86's `CRC32` share a model, as do `PMULL` and `PCLMULQDQ`. XOR, loads and stores need no binding: they are plain Lean on 64-bit halves.
- **Compiler builtins, not intrinsic headers.** Lean's bundled clang ships no `arm_neon.h`. The shim uses `__builtin_arm_crc32c*`, `__builtin_neon_vmull_p64` and the `__builtin_ia32_*` equivalents, and is force-included when compiling generated C.
- **No `SimdBackend` typeclass yet.** With one shared model per instruction there is a single instance, so the kernel is written directly against the bindings. A class is only needed if the portable path is to share the folding kernel's proof.

## Not done

- x86-64 on real hardware, and the Intel authoritative cross-check.
- `V256` and AVX models (a recorded follow-up in the brief).
- Reference-linking lemmas for the 16-bit and 32-bit CRC bindings (`crc32c_spec` covers them at the polynomial level; no kernel uses them yet).

## Phase 4, AArch64 track, so far

`MemcpyCrc32c/Impl/Hw.lean` runs the CRC32C instruction over three interleaved streams and combines them with the Phase 1 arithmetic. `rawExtendHw_eq` (`MemcpyCrc32c/HwKernel.lean`) proves it equal to the bitwise reference on any in-bounds range. It agrees with abseil on 360,000 differential cases.

Quick throughput check on the Apple M4, GB/s, median of 9, idle machine. Not the benchmarking protocol.

| Size | Lean hardware-CRC (verified) | Lean portable (verified) | `absl::ExtendCrc32c` | `absl::MemcpyCrc32c` |
| --- | --- | --- | --- | --- |
| 16 B | 3.2 | 1.8 | 7.8 | 4.2 |
| 256 B | 9.7 | 5.6 | 13.7 | 13.8 |
| 4 KiB | 10.2 | 7.0 | 43.1 | 20.0 |
| 64 KiB | 26.9 | 10.6 | 60.9 | 20.9 |
| 1 MiB | 31.7 | 11.1 | 62.5 | 20.8 |
| 64 MiB | 31.5 | 11.1 | 60.4 | 20.1 |

The Lean columns are CRC only; the fused copy is Phase 5. Against abseil's CRC-only routine the hardware kernel is at about half speed from 64 KiB up and a quarter at 4 KiB. The gaps are known: abseil adds `PMULL` folding streams, and combines streams with carry-less multiplies by precomputed constants where this kernel uses software multiplication and only splits from 4 KiB. The portable column is lower at 16 B than in the Phase 2 report because this harness calls through a closure.
