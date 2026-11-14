# Validation record for the instruction models

Every model in `SimdModels/Models.lean` that is bound to an instruction in
`SimdModels/Trusted.lean` needs two independent checks: a cross-check against
the vendor's authoritative semantics, and differential testing on hardware.

| Binding | AArch64 hardware | x86-64 | Authoritative cross-check |
| --- | --- | --- | --- |
| `crc32c_u8` | pass | pass under Rosetta only | Arm: pass (ASLp). Intel: outstanding |
| `crc32c_u16` | pass | pass under Rosetta only | Arm: pass (ASLp). Intel: outstanding |
| `crc32c_u32` | pass | pass under Rosetta only | Arm: pass (ASLp). Intel: outstanding |
| `crc32c_u64` | pass | pass under Rosetta only | Arm: pass (ASLp). Intel: outstanding |
| `clmulLo` | pass | pass under Rosetta only | Arm: pass (ASLp). Intel: outstanding |
| `clmulHi` | pass | pass under Rosetta only | Arm: pass (ASLp). Intel: outstanding |

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

### Arm: done

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

### Intel: outstanding

To be checked against the Intrinsics Guide pseudocode. Until then the x86-64
bindings rest on the Rosetta cross-check above and on sharing a model with
the Arm instructions.
