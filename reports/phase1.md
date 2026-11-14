# Phase 1 report: reference spec and CRC arithmetic

Status: exit criteria met, awaiting acceptance. The spec is frozen once this is accepted.

Toolchain: Lean 4.35.0, Mathlib v4.35.0. Abseil at `be93ce23` (13 Nov 2026), built with Apple clang 17 on an Apple M4.

## What is proven

All statements are in `MemcpyCrc32c/`, with no `sorry`, `admit`, `axiom`, `native_decide` or `bv_decide`.

| Brief item | Lean theorem | File |
| --- | --- | --- |
| Bitwise reference equals the polynomial spec | `extend_eq_spec`, `crc32c_eq_spec` | `Bitwise.lean` |
| 1. `extend_append` | `extend_append` | `Arith.lean` |
| 2. `concat_spec` | `concat_spec` | `Arith.lean` |
| 3. `removePrefix_spec` | `removePrefix_spec` | `Arith.lean` |
| 4. `removeSuffix_spec` | `removeSuffix_spec` | `Arith.lean` |
| 5. `extendZeroes_spec` | `extendZeroes_spec` | `Arith.lean` |
| Test vectors | `check_123456789` (0xE3069283), RFC 3720 B.4 (four of five), abseil's "hello world" and `ExtendByZeroesAllLengthBits` values | `Vectors.lean` |

The spec (`Spec.lean`) defines the unconditioned update as `(s·X^(8n) + M·X^32) mod G` in Mathlib's `(ZMod 2)[X]`, with `G` written out term by term, and `extend c bs` as that update with `0xFFFFFFFF` XORed in and out. Theorems 2 to 5 are stated exactly as in the brief, over `ByteArray`, with `crc = extend 0`.

`#print axioms` (from building `Axioms.lean`): every theorem above depends on `propext`, `Classical.choice`, `Quot.sound` only. `extend_append` and the test vectors do not need `Classical.choice`.

## What is tested

`tests/run_diff.sh` compares the Lean functions with abseil on random inputs: `ExtendCrc32c` and `MemcpyCrc32c` (0 to 2000 bytes, random initial CRC), and `ExtendCrc32cByZeroes`, `ConcatCrc32c`, `RemoveCrc32cPrefix`, `RemoveCrc32cSuffix` on arbitrary 32-bit words with lengths up to 2^64. 603,000 cases over six seeds, no mismatch.

## Trusted

The Lean kernel and Mathlib's definitions of polynomials and `%ₘ`. For the differential test only: the Lean compiler, clang, and the test harness. Nothing in Phase 1 is trusted C.

## Decisions taken

- **abseil's convention, confirmed from `crc32c.cc` and its tests.** A `crc32c_t` is the fully conditioned standard CRC32C. `ExtendCrc32c` XORs with `0xFFFFFFFF` on entry and exit. `ExtendCrc32cByZeroes` conditions the same way; `ConcatCrc32c` and `RemoveCrc32cSuffix` work on the conditioned values directly. This answers the brief's first open question.
- **Mathlib polynomials for the spec**, not a hand-rolled type. Congruence reasoning is done in the quotient ring `GF(2)[X]/(G)`, so each theorem is a few lines of ring arithmetic.
- **Arithmetic functions use square-and-multiply**, not abseil's tables of `X^(2^k)`. They compute the same products modulo `G` in O(log n) word operations and take a `Nat` length. Table-driven versions for fixed stream lengths belong to Phase 4 and will be proven equal to these.
- **Executable code is split from proofs.** `MemcpyCrc32c/Impl/` imports only Lean core, so native binaries do not link Mathlib.
- **`decide +kernel` for computations.** It evaluates in the kernel and adds no axioms.

## Not done

- The fifth RFC 3720 vector (the 48-byte iSCSI PDU) is not transcribed; the other four are.
- abseil was built by compiling its sources directly with `-O2 -DNDEBUG`, not with its own build system. Benchmarks will use a cmake release build.

## Problems found in the brief

1. **`bv_decide` is not axiom-free.** It proves goals through `Lean.ofReduceBool`, the same compiler-trusting axiom as `native_decide`. The brief recommends `bv_decide` and also requires that only Lean's standard axioms appear. Phase 1 avoids both. Later phases need a ruling: allow `ofReduceBool` from `bv_decide`, or keep proving word identities by hand.
2. **Instruction models will not show up in `#print axioms`.** Success criterion 5 expects "named instruction-model assumptions" there, but the brief also bans new axioms and makes each model a definition with an `@[extern]` implementation. That trust is invisible to `#print axioms`. The single trusted-models file the brief asks for has to be the record instead.
3. **No x86-64 hardware here.** This machine is an Apple M4. Phase 3's hardware differential tests and the benchmarks need a real x86-64 machine; Rosetta is an emulator and does not count.
4. **Chorba's polynomial families do not exist for CRC32C.** See below.

## Early result for the Phase 2 gate

`G` has 18 terms, so `X + 1` divides it and every multiple of `G` has an even number of terms (`eval_one_G`). Chorba's 3-term and 5-term zero polynomials rely on the gzip generator being primitive and have no CRC32C counterpart.

The search (`scripts/zero_poly_search.c`, `scripts/zero_poly_w6.c`) found, and `ZeroPoly.lean` certifies by kernel evaluation:

| Terms | Lowest degree | Polynomial | CRC32 equivalent in Chorba |
| --- | --- | --- | --- |
| 4 | 5275 | `X^5275 + X^4508 + X^2751 + 1` | 3 terms, degree 91639; 4 terms, degree 3006 |
| 6 | 209 | `X^209 + X^144 + X^54 + X^39 + X^14 + 1` | 5 terms, degree 300 |

No 3-term multiple exists at any degree. The small kernel therefore costs five shifted XORs per word where Chorba's costs four, so the 2× gain reported for CRC32 is not assured. Whether it beats slicing-by-8 is the Phase 2 measurement. The core lemma `(M + Z·X^k·c) mod G = M mod G` is proven (`modByMonic_add_zeroPoly_mul`).
