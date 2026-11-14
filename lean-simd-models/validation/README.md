# Validation record for the instruction models

Every model in `SimdModels/Models.lean` that is bound to an instruction in
`SimdModels/Trusted.lean` needs two independent checks: a cross-check against
the vendor's authoritative semantics, and differential testing on hardware.

| Binding | AArch64 hardware | x86-64 | Authoritative cross-check |
| --- | --- | --- | --- |
| `crc32c_u8` | pass | pass under Rosetta only | outstanding |
| `crc32c_u16` | pass | pass under Rosetta only | outstanding |
| `crc32c_u32` | pass | pass under Rosetta only | outstanding |
| `crc32c_u64` | pass | pass under Rosetta only | outstanding |
| `clmulLo` | pass | pass under Rosetta only | outstanding |
| `clmulHi` | pass | pass under Rosetta only | outstanding |

## AArch64 hardware differential test

`tests/HwDiff.lean`, built as `hw_diff`. Compares the compiled Lean model with
the instruction, for each binding, on 40,000 edge pairs (all-zero, all-one,
single bits, complements, low runs, alternating patterns) and 10^6 random
pairs per seed.

- Machine: Apple M4 (AArch64, `+crc`, `+aes`), macOS 26, Lean 4.35.0 bundled clang 23.1.0.
- Result: seeds 1 and 2, 2,080,000 pairs per binding, no mismatch.
  Raw output: `hw_diff_aarch64_apple_m4.txt`.
- The disassembled test binary contains `crc32cb/ch/cw/cx` and `pmull`.

## x86-64

No real x86-64 hardware has been used yet. `validation/cross_arch.c` evaluates
the six shim macros on the same edge pairs and 10^6 random pairs, built once
for arm64 and once for x86_64 (`-msse4.2 -mpclmul`, Apple clang 17), and the
outputs are compared byte for byte.

- Result: identical (49,920,000 bytes, SHA-256 `9a16f20a…0cd015`), with the
  x86-64 build run under Rosetta 2. The x86-64 binary contains `crc32` and
  `pclmulqdq` instructions.
- Rosetta is an emulator: this checks the shim and the compiler lowering, not
  Intel or AMD silicon. A run on real hardware is still required.

## Authoritative cross-check

Outstanding for both vendors.

- Arm: the models are transcribed in the shape of the ASL pseudocode
  (`CRC32C*`, `Poly32Mod2`, `PolynomialMult`), quoted in `Models.lean`. A
  mechanical check against Arm's machine-readable ASL through ASLp is in
  progress.
- Intel: to be checked against the Intrinsics Guide pseudocode.
