# Phase 1 report: reference spec and CRC arithmetic

Status: exit criteria met, awaiting acceptance. The spec is frozen once this is accepted.

Toolchain: Lean 4.35.0, Mathlib v4.35.0. Abseil at `be93ce23` (13 Nov 2026), built with Apple clang 17 on an Apple M4.

## What is proven

All statements are in `MemcpyCrc32c/`, with no `sorry`, `admit`, `axiom`, `native_decide` or `bv_decide`.

| Brief item | Lean theorem | File |
| --- | --- | --- |
| Bitwise reference equals the polynomial spec | `extend_eq_spec`, `crc32c_eq_spec`, `spec_crc32c_eq_crcList` | `Bitwise.lean`, `Vectors.lean` |
| 1. `extend_append` | `extend_append`, `Spec.extend_append` | `Arith.lean` |
| 2. `concat_spec` | `concat_spec`, `Spec.concat_spec` | `Arith.lean` |
| 3. `removePrefix_spec` | `removePrefix_spec`, `Spec.removePrefix_spec` | `Arith.lean` |
| 4. `removeSuffix_spec` | `removeSuffix_spec`, `Spec.removeSuffix_spec` | `Arith.lean` |
| 5. `extendZeroes_spec` | `extendZeroes_spec`, `Spec.extendZeroes_spec` | `Arith.lean` |
| Test vectors | `check_123456789` (0xE3069283), RFC 3720 B.4 (all five of five, including `rfc3720_iscsi_read`), abseil's "hello world" and `ExtendByZeroesAllLengthBits` values | `Vectors.lean` |

The spec (`Spec.lean`) defines the unconditioned update as `(s·X^(8n) + M·X^32) mod G` in Mathlib's `(ZMod 2)[X]`, with `G` written out term by term, and `extend c bs` as that update with `0xFFFFFFFF` XORed in and out. Theorems 1 to 5 are proven both for the executable functions (`Impl/Arith.lean`) and directly for the polynomial `Spec.*` functions (`Arith.lean`), over `ByteArray`, with `crc = extend 0`.

`#print axioms` (from building `Axioms.lean`): every theorem above depends on `propext`, `Classical.choice`, `Quot.sound` only. `extend_append` and the test vectors do not need `Classical.choice`.

## What is tested

`tests/run_diff.sh` compares the Lean functions with abseil on random inputs: `ExtendCrc32c` and `MemcpyCrc32c` (0 to 20,191 bytes, random initial CRC), and `ExtendCrc32cByZeroes`, `ConcatCrc32c`, `RemoveCrc32cPrefix`, `RemoveCrc32cSuffix` on arbitrary 32-bit words with lengths up to 2^64. 720,000 cases over six seeds, no mismatch.

## Trusted

The Lean kernel and Mathlib's definitions of polynomials and `%ₘ`. For the differential test only: the Lean compiler, clang, and the test harness. Nothing in Phase 1 is trusted C.

## Decisions taken

- **abseil's convention, confirmed from `crc32c.cc` and its tests.** A `crc32c_t` is the fully conditioned standard CRC32C. `ExtendCrc32c` XORs with `0xFFFFFFFF` on entry and exit. `ExtendCrc32cByZeroes` conditions the same way; `ConcatCrc32c` and `RemoveCrc32cSuffix` work on the conditioned values directly. This answers the brief's first open question.
- **Mathlib polynomials for the spec**, not a hand-rolled type. Congruence reasoning is done in the quotient ring `GF(2)[X]/(G)`, so each theorem is a few lines of ring arithmetic.
- **Arithmetic functions use unboxed square-and-multiply**, not abseil's tables of `X^(2^k)`. `mulModU32` and `powModU64` run entirely in unboxed `UInt32`/`UInt64` registers (zero stack frame, leaf codegen) for lengths `< 2^64`, falling back to tail-recursive `powMod.go` for larger `Nat` lengths. Table-driven versions for fixed stream lengths belong to Phase 4 and will be proven equal to these.
- **Executable code is split from proofs.** `MemcpyCrc32c/Impl/` imports only Lean core, so native binaries do not link Mathlib.
- **`decide +kernel` for computations.** It evaluates in the kernel and adds no axioms.

## Not done

- abseil was built by compiling its sources directly with `-O2 -DNDEBUG`, not with its own build system. Benchmarks will use a cmake release build.

## Problems found in the brief

1. **`bv_decide` is not axiom-free.** On Lean 4.35 it records named `_native.bv_decide` certificate axioms backed by the compiler. Both Phase 1 and Phase 2 avoid `bv_decide` entirely, proving all bitvector/word identities in the kernel via `BitVec.eq_of_getLsbD_eq`.
2. **Instruction models will not show up in `#print axioms`.** Success criterion 5 expects "named instruction-model assumptions" there, but the brief also bans new axioms and makes each model a definition with an `@[extern]` implementation. That trust is invisible to `#print axioms`. The single trusted-models file the brief asks for has to be the record instead.
3. **No x86-64 hardware here.** This machine is an Apple M4. Phase 3's hardware differential tests and the benchmarks need a real x86-64 machine; Rosetta is an emulator and does not count.
4. **Chorba's polynomial families do not exist for CRC32C.** See below.

## Early result for the Phase 2 gate

`G` has 18 terms, so `X + 1` divides it and every multiple of `G` has an even number of terms (`eval_one_G`). Chorba's 3-term and 5-term zero polynomials rely on the gzip generator being primitive and have no CRC32C counterpart.

The search (`scripts/zero_poly_search.c`, `scripts/zero_poly_w6.c`) found, and `ZeroPoly.lean` certifies by kernel evaluation:

| Terms | Degree | Polynomial | Notes / CRC32 equivalent in Chorba |
| --- | --- | --- | --- |
| 4 | 5275 | `X^5275 + X^4508 + X^2751 + 1` | Lowest-degree 4-term (`zero4_5275`); Chorba CRC32: 3 terms deg 91639, 4 terms deg 3006 |
| 6 | 209 | `X^209 + X^144 + X^54 + X^39 + X^14 + 1` | Lowest-degree 6-term (`zero6_209`, 4-word window); Chorba CRC32: 5 terms deg 300 |
| 6 | 290 | `X^290 + X^136 + X^113 + X^107 + X^32 + 1` | Lowest-degree 6-term with first gap ≥ 128 bits (`zero6_290`, 5-word window with `n1' = n2`) |

No 3-term multiple exists at any degree. The small kernel therefore costs five shifted XORs per word where Chorba's costs four, so the 2× gain reported for CRC32 is not assured. Whether it beats slicing-by-8 is the Phase 2 measurement. The core lemma `(M + Z·X^k·c) mod G = M mod G` is proven (`modByMonic_add_zeroPoly_mul`).
