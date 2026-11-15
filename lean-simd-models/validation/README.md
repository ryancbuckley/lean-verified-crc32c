# Validation record for the instruction models

Every model in `SimdModels/Models.lean` that is bound to an instruction or
unaligned load in `SimdModels/Trusted.lean` has two independent checks: a
cross-check against the vendor's authoritative semantics, and differential
testing on hardware.

| Binding | AArch64 hardware | x86-64 | Authoritative cross-check |
| --- | --- | --- | --- |
| `crc32c_u8` | pass | pass under Rosetta only | Arm: pass (ASLp). Intel: partial (proven equal to a hand transcription of the SDM) |
| `crc32c_u16` | pass | pass under Rosetta only | Arm: pass (ASLp). Intel: partial (proven equal to a hand transcription of the SDM) |
| `crc32c_u32` | pass | pass under Rosetta only | Arm: pass (ASLp). Intel: partial (proven equal to a hand transcription of the SDM) |
| `crc32c_u64` | pass | pass under Rosetta only | Arm: pass (ASLp). Intel: partial (proven equal to a hand transcription of the SDM) |
| `clmulLo` | pass | pass under Rosetta only | Arm: pass (ASLp). Intel: partial (proven equal to a hand transcription of the SDM) |
| `clmulHi` | pass | pass under Rosetta only | Arm: pass (ASLp). Intel: partial (proven equal to a hand transcription of the SDM) |
| `loadU8` | pass | pass under Rosetta only | Raw byte load (`SIMDMODELS_SARRAY_BYTES`) + `loadU8_eq_uget` kernel proof |
| `loadU64LE` | pass | pass under Rosetta only | Little-endian `memcpy` + `V128.lane8_vld1q` kernel proof |

## AArch64 hardware differential test

`tests/HwDiff.lean`, built as `hw_diff`. Compares the compiled Lean model with
the hardware binding, for all eight data bindings, on 40,000 edge pairs (all-zero,
all-one, single bits, complements, low runs, alternating patterns, and unaligned
offsets `0..16`) and 10^6 random pairs per seed.

- Machine: Apple M4 (AArch64, `+crc`, `+aes`), macOS 26, Lean 4.35.0 bundled clang 23.1.0.
- Result: seeds 1 and 2, 2,080,000 pairs per binding (16,640,000 binding evaluations), no mismatch.
  Raw output: `hw_diff_aarch64_apple_m4.txt`.
- The disassembled test binary contains `crc32cb/ch/cw/cx`, `pmull`, single-instruction `ldrb`, and single-instruction unaligned `ldr`.

## x86-64

No real x86-64 hardware has been used yet. `validation/cross_arch.c` evaluates
all eight data shim functions (plus all `PCLMULQDQ` immediate selector variants
`0x00`, `0x01`, `0x10`, `0x11`, `0xFE`, `0xEF`, `0xFF`) on the edge pairs and
10^6 random pairs, built once for `arm64` and once for baseline `x86_64`
(without global `-msse4.2 -mpclmul`, exercising the per-function
`__attribute__((__target__("sse4.2,pclmul")))` guards in `c/simd_shim.h`), and
compares the outputs byte for byte.

- Result: identical (299,520,000 bytes, SHA-256 `f5948131…1e6d3997`), with the
  x86-64 build run under Rosetta 2. The x86-64 binary contains `crc32` and
  `pclmulqdq` instructions; compiling `Hw.c` (`-msse4.2 -mpclmul`) and
  `HwCombine.c` (`-msse4.2 -mpclmul -fno-vectorize -fno-slp-vectorize`) for
  `x86_64` inlines all 246 `crc32*` and 140 `pclmulqdq` instructions with zero
  out-of-line shim calls and zero post-SSE2 instructions in module initializers.
- Rosetta is an emulator: this checks the shim, `__target__` attributes, and
  compiler lowering, not Intel or AMD silicon. A run on real hardware is still
  required.

## Authoritative cross-check

### Arm: done (ASLp)

The real A64 opcodes are executed in ASLp (UQ-PAC/aslp, commit `92e4fd94`),
which interprets Arm's machine-readable ASL specification, and the results
are compared with the Lean models.

- `validation/aslp_vectors.py` drives ASLp: it sets the source registers,
  executes `crc32cb/ch/cw/cx w0, w1, w2` and `pmull v0.1q, v1.1d, v2.1d`
  (opcodes `1ac25020`, `1ac25420`, `1ac25820`, `9ac25c20`, `0ee2e020`), and
  reads the destination register. The unused upper register bits are filled
  with random data, so the check also covers "the instruction ignores them".
- `tests/AslCheck.lean` (`asl_check`) compares each vector with the model.
- Result: 100,720 vectors (144 edge pairs and 20,000 random pairs per opcode),
  no mismatch. A 2,220-vector subset is kept in `asl_vectors_arm.txt` as a
  regression input that needs no OCaml toolchain.
- ASLp's symbolic expansion of the CRC opcodes (`:sem`) also has the same
  structure as the model: the constant `0x1EDC6F41`, the bit-test-and-XOR loop
  from the top bit down to bit 32, and the final bit reversal.
- `PMULL` on 64-bit lanes is an optional feature in the specification
  ("Has 128-bit form of PMULL instructions"); the check enables it.

Trusted here: ASLp's interpreter, and that its bundled specification is
Arm's.

### Intel: partial (proven equal to a hand transcription of the SDM pseudocode)

`SimdModels/IntelSdm.lean` transcribes the imperative `Operation` pseudocode
from Intel 64 and IA-32 Architectures Software Developer's Manual:

- Vol. 2A `CRC32 — Accumulate CRC32 Value` (8/16/32/64-bit forms, bit-reversed
  views, `TEMP1[size+31:0] ← TEMP2 ≪ 32 ⊕ TEMP3`, `for i ← 0 to size-1` shift/XOR
  by `0x11EDC6F41`, and 64-bit `REX.W` upper-32-bit zero-extension).
- Vol. 2B `PCLMULQDQ — Carry-Less Multiplication Quadword` (`imm8[0]` and
  `imm8[4]` quadword selectors and the nested `i = 0..63` / `i = 64..126` XOR-AND
  product loops).

Lean's kernel proves universal equivalence (`crc32_u8_eq`, `crc32_u16_eq`,
`crc32_u32_eq`, `crc32_u64_eq`, `crc32_r64_eq`, `clmulepi64_eq`) between the
Intel SDM transcriptions and `SimdModels.Model` across **all** possible operand
values and `imm8` bytes, using only `[propext, Classical.choice, Quot.sound]`.

Limit of this check: the transcription in `IntelSdm.lean` was written by hand
and has not been compared mechanically with Intel's text or with the
machine-readable Intrinsics Guide data. The proof shows the two Lean
definitions agree; it cannot show the transcription is faithful. Unlike the
Arm check, nothing from the vendor was executed. Still to do: derive or check
the transcription from Intel's published pseudocode, and run on real hardware.
